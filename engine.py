# Rory Linerud
# rlinerud@u.rochester.edu
#
# engine.py

import io
import re
import z3
from contextlib import redirect_stdout
from synth.component import Component
from synth.program import Program
from synth.types import (
    Examples, Input, Instantiator, Library,
    LineMapping, Oracle, Value, Variable
)
from synth.vars import VariableGenerator
from typing import Optional


class SynthesisError(Exception):
    """
    Signifies that the supplied component library is insufficient to
    synthesize the specified oracle program.
    """
    pass


class SynthesisEngine:

    """

    """

    def __init__(self, input_types: tuple[Instantiator],
                 output_type: Instantiator, library: Library) -> None:
        """
        Create a new synthesis engine that can generate programs of
        domain `input_types` and range `output_type` using components
        from the given `library`.

        Parameters:

        - `input_types`: a tuple of Z3 variable instantiators
          representing the types of the synthesized program's inputs.
        - `output_type`: a Z3 variable instantiator representing the
          synthesized program's output type.
        - 'library': a dictionary indicating how many of each base
          component should be used during synthesis.
        """
        self._vars = VariableGenerator()
        self.inputs = tuple(self._vars.next_var(t) for t in input_types)
        self.library = library
        self.components = self._build_components()
        self.component_inputs = self._component_inputs()
        self.component_outputs = self._component_outputs()
        self.component_vars = self.component_inputs | self.component_outputs
        self.output = self._vars.next_var(output_type)
        self._alt_output = self._vars.next_var(output_type)
        self.num_lines = len(input_types) + len(self.components)
        self.examples = {}

    def _build_components(self) -> list[Component]:
        """
        Return a list of `Component` objects that is consistent with
        the engine's `library`.
        """
        components = []
        for op, count in self.library.items():
            for _ in range(count):
                components.append(Component(op, self._vars))

        return components

    def _component_inputs(self) -> set[Variable]:
        """
        Return the set of Z3 variables that serve as inputs to
        components of the engine's `library`.
        """
        inputs = set()
        for c in self.components:
            for c_input in c.inputs:
                inputs.add(c_input)

        return inputs

    def _component_outputs(self) -> set[Variable]:
        """
        Return the set of Z3 variables that serve as outputs to
        components of the engine's `library`.
        """
        outputs = set()
        for c in self.components:
            outputs.add(c.output)

        return outputs

    def _locations(self, prefix: str, output_var: Variable) -> LineMapping:
        """
        Return a dictionary that maps each Z3 variable to either its
        corresponding integer-valued location variable or its
        predetermined integer value.

        Map component inputs and outputs to integer-valued location
        variables; map program inputs and outputs to integer values.
        The location of each program input variable should equal its
        index in the program's `inputs` tuple. The location of the
        program's output variable should be the line number of the
        final line of the program.

        Parameters:

        - `prefix`: the string that all returned location variables
          should begin with.
        - `output_var`: the output variable to include in the resulting
          dictionary.
        """
        locations = {}
        for var in self.component_vars:
            locations[var] = z3.Int(f'{prefix}_loc_{var}')

        for i, program_input in enumerate(self.inputs):
            locations[program_input] = i

        locations[output_var] = self.num_lines - 1
        return locations

    def _var_strs(self, locations: LineMapping) -> dict[str, Variable]:
        """
        Return a dictionary that maps the string representation of each
        Z3 variable to the actual variable itself.

        Parameters:

        - `locations`: a dictionary mapping individual input and output
          variables to their (possibly predetermined) location
          variables.
        """
        return {str(var): var for var in locations}

    def _in_cache(self, cache: set[tuple[Variable, Variable]],
                  var1: Variable, var2: Variable) -> bool:
        """
        Check to see whether or not `var1` and `var2` are present
        together in the given `cache` set. If so, return `True`;
        otherwise return `False`.

        Parameters:

        - `cache`: the set of Z3 variable pairs to check `var1` and
          `var2` against.
        - `var1`: the first Z3 variable of the pair.
        - `var2`: the second Z3 variable of the pair.
        """
        return (var1, var2) in cache or (var2, var1) in cache

    def _acyclic(self, locations: LineMapping) -> z3.BoolRef:
        """
        Return a simplified `z3.BoolRef` predicate logic expression
        that represents the acyclicity constraint of synthesized
        programs.

        Iteratively call the `z3.And` function to build up a large
        conjunction of individual propositions. Use the provided
        `locations` dictionary to access the location variables of the
        component input and output variables. Append a final dummy
        constant of `True` to the expression (before simplification) to
        allow for empty component libraries to satisfy the acyclicity
        constraint as well.

        This function should produce the same constraint as the
        acyclicity constraint in Jha et al. (2010).

        Parameters:

        - `locations`: a dictionary mapping individual input and output
          variables to their (possibly predetermined) location
          variables.
        """
        predicate = True
        for c in self.components:
            output_loc = locations[c.output]
            for c_input in c.inputs:
                input_loc = locations[c_input]
                predicate = z3.And(predicate, input_loc < output_loc)

        # Add a dummy `True` predicate just in case the base component
        # library is empty
        predicate = z3.And(predicate, True)
        return z3.simplify(predicate)

    def _consistent(self, locations: LineMapping) -> z3.BoolRef:
        """
        Return a simplified `z3.BoolRef` predicate logic expression
        that represents the consistency constraint of synthesized
        programs.

        Iteratively call the `z3.And` function to build up a large
        conjunction of individual propositions. Use the provided
        `locations` dictionary to access the location variables of the
        component output variables. Append a final dummy constant of
        `True` to the expression (before simplification) to allow for
        singleton component libraries to satisfy the consistency
        constraint as well. As the predicate logic expression is built,
        use a cache to keep track of which propositions have already
        been considered and no longer need to be added to the overall
        conjunction.

        This function should produce the same constraint as the
        consistency constraint in Jha et al. (2010).

        Parameters:

        - `locations`: a dictionary mapping individual input and output
          variables to their (possibly predetermined) location
          variables.
        """
        predicate = True
        cache = set()
        for output1 in self.component_outputs:
            for output2 in self.component_outputs:
                if output1 is not output2:
                    # Use a cache to make sure we are not adding any
                    # constraints that we have already accounted for
                    if not self._in_cache(cache, output1, output2):
                        output1_loc = locations[output1]
                        output2_loc = locations[output2]
                        inequality = output1_loc != output2_loc
                        predicate = z3.And(predicate, inequality)
                        cache.add((output1, output2))

        # Add a dummy `True` predicate for the case where there is just
        # a single component output
        predicate = z3.And(predicate, True)
        return z3.simplify(predicate)

    def _well_formed(self, locations: LineMapping) -> z3.BoolRef:
        """
        Return a simplified `z3.BoolRef` predicate logic expression
        that represents the well-formedness constraint of synthesized
        programs.

        Iteratively call the `z3.And` function to build up a large
        conjunction of individual propositions. Use the provided
        `locations` dictionary to access the location variables of the
        component input and output variables. The line number of each
        component input should be greater than or equal to 0 and less
        than M, where M is the number of lines in the program; the line
        number of each component output should be greater than or equal
        to I and less than M, where I is the number of program inputs.

        This function should produce the same constraint as the
        well-formedness constraint in Jha et al. (2010).

        Parameters:

        - `locations`: a dictionary mapping individual input and output
          variables to their (possibly predetermined) location
          variables.
        """
        predicate = True
        # Add the constraints for the component inputs
        for c_input in self.component_inputs:
            input_loc = locations[c_input]
            predicate = z3.And(predicate, input_loc >= 0)
            predicate = z3.And(predicate, input_loc < self.num_lines)

        # Add the constraints for the component outputs
        for c_output in self.component_outputs:
            output_loc = locations[c_output]
            predicate = z3.And(predicate, output_loc >= len(self.inputs))
            predicate = z3.And(predicate, output_loc < self.num_lines)

        # Add the acyclicity and consistency constraints
        predicate = z3.And(predicate, self._acyclic(locations))
        predicate = z3.And(predicate, self._consistent(locations))
        return z3.simplify(predicate)

    def _components(self) -> z3.BoolRef:
        """
        Return a simplified `z3.BoolRef` predicate logic expression
        that represents the base component semantics of synthesized
        programs.

        Iteratively call the `z3.And` function to build up a large
        conjunction of individual propositions. Use the precalculated
        relation between each component's inputs and output to build up
        the complete constraint. Append a final dummy constant of
        `True` to the expression (before simplification) to allow for
        empty component libraries to satisfy the consistency constraint
        as well.

        This function should produce the same constraint as the
        component semantics constraint in Jha et al. (2010).
        """
        predicate = True
        for c in self.components:
            predicate = z3.And(predicate, c.relation)

        # Add a dummy `True` predicate just in case the base component
        # library is empty
        predicate = z3.And(predicate, True)
        return z3.simplify(predicate)

    def _dataflow(self, locations: LineMapping,
                  inputs: tuple[Input, ...],
                  output_var: Variable,
                  output_val: Optional[Value] = None) -> z3.BoolRef:
        """
        Return a simplified `z3.BoolRef` predicate logic expression
        that represents the dataflow semantics of synthesized programs.

        Iteratively call the `z3.And` function to build up a large
        conjunction of individual propositions. Use the provided
        `locations` dictionary to access the location variables of the
        component input and output variables. Allow the fixing of the
        program inputs and output variables to specific values via the
        given `inputs` and `output_val` parameters. As the predicate
        logic expression is built, use a cache to keep track of which
        propositions have already been considered and no longer need to
        be added to the overall conjunction.

        This function should produce the same constraint as the
        dataflow semantics constraint in Jha et al. (2010).

        Parameters:

        - `locations`: a dictionary mapping individual input and output
          variables to their (possibly predetermined) location
          variables.
        - `inputs`: a tuple of (possibly predetermined) program input
          variables.
        - `output_var`: the output variable used by the program.
        - `output_val`: the value of `output_var`, if it exists.
        """
        predicate = True
        var_set = self.component_vars | set(self.inputs) | {output_var}
        cache = set()
        for var1 in var_set:
            for var2 in var_set:
                # Use a cache to make sure we are not adding any
                # constraints that we have already accounted for
                if not self._in_cache(cache, var1, var2):
                    var1_loc = locations[var1]
                    var2_loc = locations[var2]
                    try:
                        implies = z3.Implies(var1_loc == var2_loc, var1 == var2)
                        predicate = z3.And(predicate, implies)

                    except AttributeError:
                        predicate = z3.And(predicate, var1_loc != var2_loc)

                    cache.add((var1, var2))

        # For each primitive provided in `inputs`, fix the
        # corresponding input variable
        for i, arg in enumerate(inputs):
            if type(arg) in [bool, int, float]:
                predicate = z3.And(predicate, self.inputs[i] == arg)
                predicate = z3.Exists(self.inputs[i], predicate)

        # If `output_val` is provided, fix `output_var`
        if output_val is not None:
            predicate = z3.And(predicate, output_var == output_val)
            predicate = z3.Exists(output_var, predicate)

        return z3.simplify(predicate)

    def _functional(self, locations: LineMapping,
                    inputs: tuple[Input, ...],
                    output_var: Variable,
                    output_val: Optional[Value] = None) -> z3.BoolRef:
        """
        Return a simplified `z3.BoolRef` predicate logic expression
        that represents the functional constraint of synthesized
        programs.

        Build an existential predicate expression using calls to the
        `_dataflow`, `_components`, and `_well_formed` functions. Allow
        the fixing of the program inputs and output to specific values
        via the given `inputs` and `output_val` parameters.

        This function should produce the same constraint as the
        functional constraint in Jha et al. (2010).

        Parameters:

        - `locations`: a dictionary mapping individual input and output
          variables to their (possibly predetermined) location
          variables.
        - `inputs`: a tuple of (possibly predetermined) program input
          variables.
        - `output_var`: the output variable used by the program.
        - `output_val`: the value of `output_var`, if it exists.
        """
        predicate = self._dataflow(locations, inputs, output_var, output_val)
        predicate = z3.And(predicate, self._components())
        predicate = z3.And(predicate, self._well_formed(locations))
        for var in self.component_vars:
            predicate = z3.Exists(var, predicate)

        return z3.simplify(predicate)

    def _behaves(self, locations: LineMapping,
                 output_var: Variable) -> z3.BoolRef:
        """
        Return a simplified `z3.BoolRef` predicate logic expression
        that represents the behavioral constraint of synthesized
        programs.

        Iteratively call the `z3.And` function to build up a large
        conjunction of individual propositions. Each conjunct should
        be a `_functional` constraint satisfying a different input-
        output example. Append a final dummy constant of `True` to the
        expression (before simplification) to allow for empty example
        sets to satisfy the behavioral constraint as well.

        This function should produce the same constraint as the
        behavioral constraint in Jha et al. (2010).

        Parameters:

        - `locations`: a dictionary mapping individual input and output
          variables to their (possibly predetermined) location
          variables.
        - `output_var`: the output variable used by the program.
        """
        predicate = True
        for inputs, output in self.examples.items():
            func = self._functional(locations, inputs, output_var, output)
            predicate = z3.And(predicate, func)

        # Add a dummy `True` predicate in case the example set is empty
        predicate = z3.And(predicate, True)
        return z3.simplify(predicate)

    def _distinct(self) -> z3.BoolRef:
        """
        Return a simplified `z3.BoolRef` predicate logic expression
        that represents the distinguishing constraint of synthesized
        programs.

        Build an existential predicate expression using calls to the
        `_behaves` and `_functional` functions. Use two different sets
        of location variables to represent two distinct programs that
        can be synthesized relative to some set of input-output
        examples.

        This function should produce the same constraint as the
        distinguishing constraint in Jha et al. (2010).
        """
        # Initial location dictionary with O' as the program output
        locations1 = self._locations('alt', self._alt_output)

        # Initial and final location dictionaries with O as the program
        # output
        locations2 = self._locations('orig', self.output)
        candidates = self._candidates(locations2, self.output)

        # Behavioral constraint for L' using O'
        predicate = self._behaves(locations1, self._alt_output)

        # Functional constraint for L' using O'
        func = self._functional(locations1, self.inputs, self._alt_output)
        predicate = z3.And(predicate, func)

        # Existential quantifiers over L'
        for loc_var in locations1.values():
            if type(loc_var) is z3.ArithRef:
                predicate = z3.Exists(loc_var, predicate)

        # Inequality constraint for O and O'
        predicate = z3.And(predicate, self.output != self._alt_output)
        predicate = z3.Exists(self._alt_output, predicate)

        # Functional constraint for L using O
        func = self._functional(candidates, self.inputs, self.output)
        predicate = z3.And(predicate, func)
        predicate = z3.Exists(self.output, predicate)

        # Existential quantifiers over L
        for loc_var in locations2.values():
            if type(loc_var) is z3.ArithRef:
                predicate = z3.Exists(loc_var, predicate)

        return z3.simplify(predicate)

    def _candidates(self, locations: LineMapping, output_var: Variable,
                    verbose: bool = False) -> dict[Variable, int]:
        """
        Return a dictionary that maps each input and output variable to
        a feasible line location.

        Call the `_behaves` function to retrieve a set of location
        assignments that satisfy the constraints imposed by all of the
        input-output pairs in the engine's `examples` dictionary. Save
        Z3's output into a buffer and parse the results using a
        regular expression.

        Parameters:

        - `locations`: a dictionary mapping individual input and output
          variables to their (possibly predetermined) location
          variables.
        - `output_var`: the output variable used by the program.
        - `verbose`: a boolean indicating whether or not informative
          print statements should be run during the execution of this
          function.
        """
        if verbose:
            print('  Finding feasible line locations...')

        buffer = io.StringIO()
        with redirect_stdout(buffer):
            z3.solve(self._behaves(locations, output_var))

        # Return an empty dictionary if no viable candidates exist
        for result in ['no solution', 'failed to solve']:
            if result in buffer.getvalue():
                if verbose:
                    print('    No viable candidates found')

                return {}

        pattern = re.compile(r'[a-z]+_loc_([a-z]+\d+) = (\d+)')
        matches = pattern.findall(buffer.getvalue())
        var_strs = self._var_strs(locations)
        candidates = {var_strs[var]: int(loc) for var, loc in matches}
        if verbose:
            print('    Viable candidates found')

        return locations | candidates

    def _new_input(self, verbose: bool = False) -> tuple[Value, ...]:
        """
        Return a new example input that distinguishes the current
        synthesized program from another valid program of a different
        configuration.

        Call the `_distinct` function to retrieve a program input
        sequence that acts as the distinguishing input between the
        presently synthesized program and another, hypothetical
        program. Save Z3's output into a buffer and parse the results
        using a regular expression.

        Parameters:

        - `verbose`: a boolean indicating whether or not informative
          print statements should be run during the execution of this
          function.
        """
        if verbose:
            print('  Finding a new input-output pair...')

        buffer = io.StringIO()
        z3.solve(self._distinct())
        with redirect_stdout(buffer):
            z3.solve(self._distinct())

        # Return an empty tuple if no solution exists
        for result in ['no solution', 'failed to solve']:
            if result in buffer.getvalue():
                if verbose:
                    print('    No new example found')

                return ()

        regex = r'var(\d+) = (True|False|-?\d+\.?\d*|-?\d*\.?\d+)'
        pattern = re.compile(regex)
        matches = pattern.findall(buffer.getvalue())
        for x, y in matches:
            print(x, y)
        values = {int(index): eval(value) for index, value in matches}
        print(values)
        new_input = []
        for i in range(len(self.inputs)):
            new_input.append(values[i])

        print(new_input)
        return tuple(new_input)

    def synthesize(self, oracle: Oracle, examples: Examples,
                   verbose: bool = True) -> Program:
        """
        Synthesize a program that satisfies all of the behavior
        requirements specified by the given `oracle` program as well as
        the provided input-output pairs in `examples`.

        This function should exhibit the same behavior as the iterative
        synthesis algorothm in Jha et al. (2010).

        Parameters:

        - `oracle`: the reference function to be synthesized.
        - `examples`: a dictionary mapping various program inputs to
          their corresponding outputs.
        """
        self.examples = examples
        locations = self._locations('orig', self.output)
        while True:
            if verbose:
                print('Performing a synthesis loop...')

            candidates = self._candidates(locations, self.output, verbose)
            if not candidates:
                raise SynthesisError('Base components insufficient')

            new_input = self._new_input(verbose)
            print(new_input)
            if not new_input:
                code = self._code(candidates)
                if verbose:
                    print('Synthesis complete!')

                return Program(self.inputs, self.output, code)

            if verbose:
                print(f'    Adding example {new_input}')

            self.examples |= {new_input: oracle(*new_input)}

    def _code(self, locations: dict[Variable, int]) -> str:
        """
        Generate the code for the final synthesized program.
        
        
        """
        prologue = self._prologue()
        epilogue = f'    return T{locations[self.output]}'
        lines = ['' for _ in range(self.num_lines)]

        # Print each program input on its own line
        for program_input in self.inputs:
            input_loc = locations[program_input]
            lines[input_loc] += f'    T{input_loc} = {program_input}\n'

        # Print each gate output on its own line
        for c in self.components:
            output_loc = locations[c.output]
            lines[output_loc] += f'    T{output_loc} = {c.operation}('

            # Print the arguments of the gate separated by commas
            for c_input in c.inputs[:-1]:
                input_loc = locations[c_input]
                lines[output_loc] += f'T{input_loc}, '

            # Print the final argument without a trailing comma
            input_loc = locations[c.inputs[-1]]
            lines[output_loc] += f'T{input_loc})\n'

        return prologue + ''.join(lines) + epilogue

    def _prologue(self) -> str:
        """
        Generate the beginning of the code for the synthesized program.
        """
        prologue = 'def program('
        for program_input in self.inputs[:-1]:
            prologue += f'{program_input}, '

        prologue += f'{self.inputs[-1]}):\n'
        return prologue
