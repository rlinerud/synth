# Rory Linerud
# rlinerud@u.rochester.edu
#
# component.py

from synth.ops import ops
from synth.types import Variable
from synth.vars import VariableGenerator


class Component:

    """
    A base component used for synthesis.

    Encodes the relationship that holds between various input and
    output variables with respect to some base component function.
    Takes in a `VariableGenerator` upon initialization that is used to
    instantiate new Z3 variables as necessary.

    Instance variables:

    - `operation`: the name of the function performed by the component.
    - `_var_gen`: the Z3 variable generator that the component can use
      to instantiate new inputs and outputs.
    - `inputs`: a tuple of Z3 variables that together represent the
      component's inputs.
    - `output`: the Z3 variable representing the component's output.
    - `relation`: the Z3 expression that relates the component's inputs
      to its output.

    Public methods:

    - `__init__`: build a new base component along with all of its
      variables.
    - `__repr__`: return a string that represents the function
      performed by this `Component`.
    """

    def __init__(self, operation: str, var_gen: VariableGenerator) -> None:
        """
        Create a new base component that has the effect of `operation`
        on the appropriate number and type of argument variables.

        Use `var_gen` to generate z3 variables representing the
        component's inputs and output. Encode the mathematical
        relationship between these variables as another z3 expression.

        Parameters:

        - `operation`: the string representation of the gate's
          operator.
        - `var_gen`: the `VariableGenerator` that the component should
          retrieve new z3 variables from.
        """
        self.operation = operation
        self._var_gen = var_gen
        self.inputs = self._inputs()
        self.output = var_gen.next_var(ops[operation]['output'])
        self.relation = ops[operation]['func'](*self.inputs) == self.output

    def _inputs(self) -> tuple[Variable, ...]:
        """
        Return a tuple of z3 variables, one for each component input.

        Create the tuple by repeatedly calling on the `next_var`
        function in `self._var_gen`. The first parameter of the
        component should be the first element of the tuple, the second
        parameter the second element, and so on.
        """
        inputs = []
        for arg_type in ops[self.operation]['inputs']:
            inputs.append(self._var_gen.next_var(arg_type))

        return tuple(inputs)

    def __repr__(self) -> str:
        """
        Return a string that encodes the mathematical relationship
        that holds between this component's input and output variables.
        """
        return str(self.relation)
