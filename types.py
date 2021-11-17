# Rory Linerud
# rlinerud@u.rochester.edu
#
# types.py

from typing import Callable, Union
from z3 import ArithRef, BoolRef

Boolean = Union[BoolRef, bool]
Integral = Union[ArithRef, int]

Variable = Union[BoolRef, ArithRef]
Value = Union[bool, int]
Entry = Union[Variable, Value]

Library = dict[str, int]
Instantiator = Callable[[str], Variable]

from synth.matrix import Matrix

LineMapping = dict[Matrix, Integral]
Oracle = Callable[[Matrix, ...], Matrix]
Examples = dict[tuple[Matrix, ...], Matrix]
