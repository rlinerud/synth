# Rory Linerud
# rlinerud@u.rochester.edu
#
# program.py

from synth.types import Variable, Value


class Program:

    """
    A Python program written in static assignment form.

    Instance variables:

    - `inputs`: the Z3 variables that represent the program's inputs.
    - `output`: the Z3 variable that represents the program's output.
    - `code`: a string representation of the program's code, written in
      static assignment form.

    Public methods:

    - `__init__`: create a new `Program`.
    - `__repr__`: return the string representation of the code executed
      by this `Program`.
    - `__call__`: run the `Program` on a set of provided input values.
    """

    def __init__(self, inputs: tuple[Variable, ...],
                 output: Variable, code: str) -> None:
        """
        Create a new `Program` that has the same behavior as that in
        the provided `code` string.

        Use the Z3 variables in `inputs` and `output` to represent the
        program's inputs and output, respectively. Use the `code`
        string to determine the syntax and semantics of the resulting
        Python program.

        Parameters:

        - `inputs`: a tuple of Z3 variables that together represent the
          program's inputs.
        - `output`: a Z3 variable that represents the program's output.
        - `code`: a pseudocode representation of the code that this
          `Program` executes.
        """
        self.inputs = inputs
        self.output = output
        self.code = code

    def __repr__(self) -> str:
        """
        Return the string representation of the program's code.
        """
        return self.code

    def __call__(self, inputs: tuple[Value, ...]) -> Value:
        """
        Convert the `Program` into a syntactically correct Python
        function and call it on the given `inputs`.

        Currently not implemented.

        Parameters:

        - `inputs`: the program arguments to be fed into the Python
          program.
        """
        raise NotImplementedError()
