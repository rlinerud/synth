# Rory Linerud
# rlinerud@u.rochester.edu
#
# types.py

from typing import Callable, Union
from z3 import ArithRef, BoolRef

Variable = Union[BoolRef, ArithRef]
Value = Union[bool, int]
Entry = Union[Variable, Value]

Boolean = Union[BoolRef, bool]
Integral = Union[ArithRef, int]
#Real = Union[ArithRef, float]
#Arithmetic = Union[Integral, Real]
#Input = Union[Boolean, Arithmetic]

from synth.matrix import Matrix

Library = dict[str, int]
LineMapping = dict[Matrix, Integral]
Oracle = Callable[[Matrix, ...], Matrix]
Instantiator = Callable[[str], Variable]
Examples = dict[tuple[Matrix, ...], Matrix]
