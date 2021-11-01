# Rory Linerud
# rlinerud@u.rochester.edu
#
# types.py

from typing import Callable, Union
from z3 import ArithRef, BoolRef

# A `Variable` is a supported Z3 expression; a `Value` is a supported
# Python primitive.
Variable = Union[ArithRef, BoolRef]
Value = Union[bool, int, float]

# Sometimes it doesn't matter whether something is a Python primitive
# or a Z3 variable.
Boolean = Union[BoolRef, bool]
Integral = Union[ArithRef, int]
Real = Union[ArithRef, float]
Arithmetic = Union[Integral, Real]
Input = Union[Boolean, Arithmetic]

# A `Library` is a collection of base components.
Library = dict[str, int]

# A `LineMapping` is a mapping from Z3 variables to their locations (or
# line numbers) in a synthesized program.
LineMapping = dict[Variable, Integral]

# An `Oracle` is just a function that takes in supported inputs and
# returns a supported output.
Oracle = Callable[[Value, ...], Value]

# An `Instantiator` is a Z3 function that instantiates a new Z3
# variable, taking the new variable's name as input.
Instantiator = Callable[[str], Variable]

# `Examples` is an abbreviation for a set of input-output pairs.
Examples = dict[tuple[Value, ...], Value]
