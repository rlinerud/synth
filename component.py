# Rory Linerud
# rlinerud@u.rochester.edu
#
# component.py

from synth.matrix import Matrix
from synth.ops import ops
from synth.vars import VariableGenerator

class Component:

    """
    A base component used for synthesis.

    Encodes the relationship that holds between various inputs and
    outputs with respect to some base component function. Takes in a
    `VariableGenerator` upon initialization that is used to instantiate
    new Z3 variables and `Matrix` objects as necessary. Represents each
    input and output as a `Matrix` object to allow for reversible
    program synthesis.

    Instance variables:

    - `operation`: the name of the function performed by the
      `Component`.
    - `_var_gen`: the Z3 variable generator that the `Component` can
      use to instantiate new input and output `Matrix` objects.
    - `inputs`: a tuple of `Matrix` objects that together represent the
      inputs of the `Component`.
    - `output`: the `Matrix` object that represents the output of the
      `Component`.
    - `relation`: the Z3 expression that relates the inputs and output
      of the `Component` together.

    Public methods:

    - `__init__`: build a new base `Component` along with all of its
      inputs and outputs.
    - `__repr__`: return a string that represents the function
      performed by this `Component`.
    """

    def __init__(self, operation: str, var_gen: VariableGenerator) -> None:
        """
        Create a new base `Component` that has the effect of
        `operation` on the appropriate number and type of arguments.

        Use `var_gen` to generate Z3 variables that can be placed into
        `Matrix` objects to collectively represent the inputs and
        output of the desired `Component`. Encode the mathematical
        relationship between all of these variables as another Z3
        expression.

        Parameters:

        - `operation`: the string representation of the gate's
          operator.
        - `var_gen`: the `VariableGenerator` that this `Component`
          should retrieve new Z3 variables from.
        """
        self.operation = operation
        self._var_gen = var_gen
        self.inputs = self._inputs()
        self.output = self._output()
        self.relation = ops[operation]['func'](*self.inputs) == self.output

    def _inputs(self) -> tuple[Matrix, ...]:
        """
        Return a tuple of `Matrix` objects that are full of Z3
        variables, one for each `Component` input.

        Create the tuple by repeatedly calling on the `variables`
        static method of the `Matrix` class. The first parameter of the
        `Component` should be the first element of the tuple, the
        second parameter the second element, and so on.
        """
        inputs = []
        for arg_type, (num_rows, num_cols) in ops[self.operation]['inputs']:
            matrix = Matrix.variables(num_rows, num_cols,
                                      arg_type, self._var_gen)
            inputs.append(matrix)

        return tuple(inputs)

    def _output(self) -> Matrix:
        """
        Return a `Matrix` object that represents the variable output of
        this `Component`.
        """
        arg_type, (num_rows, num_cols) = ops[self.operation]['output']
        return Matrix.variables(num_rows, num_cols, arg_type, self._var_gen)

    def __repr__(self) -> str:
        """
        Return a string that encodes the mathematical relationship that
        holds between the input and output `Matrix` objects of this
        `Component`.
        """
        return str(self.relation)
