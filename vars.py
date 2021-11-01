# Rory Linerud
# rlinerud@u.rochester.edu
#
# vars.py

from synth.types import Instantiator, Variable
from typing import Generator


class VariableGenerator:

    """
    A generator of Z3 variables.

    Maintains an internal sequence of variable names and incrementally
    returns Z3 variables using names from this list. No two variables
    ever created from a single generator will ever have the same name.

    Instance variables:

    - `_names`: the sequence of names that the `VariableGenerator`
      builds, maintains, and selects names from.

    Public methods:

    - `__init__`: create a new `VariableGenerator`.
    - `next_var`: return the next Z3 variable that is available.
    """

    def __init__(self) -> None:
        self._names = self._var_names()

    @staticmethod
    def _var_names() -> Generator[str, None, None]:
        """
        Return a generator of variable names. The first variable
        generated should have index 0; each successive variable should
        have an index that is 1 larger.
        """
        count = 0
        while True:
            yield f'var{count}'
            count += 1

    def next_var(self, kind: Instantiator) -> Variable:
        """
        Return a new Z3 variable using the specified `Instantiator`.
        The name of the variable will be the next one available to the
        generator.

        Parameters:

        - `kind`: the Z3 variable instantiator to use in the
          construction of the next variable.
        """
        var_name = next(self._names)
        return kind(var_name)
