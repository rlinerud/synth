# Rory Linerud
# rlinerud@u.rochester.edu
#
# vector.py

from __future__ import annotations


import z3
from synth.types import Integral
from typing import Union


class Vector:

    """
    A finite sequence of integral values or variables.

    Instance variables:

    - `_elements`: the entries of the `Vector` as a tuple.

    Public methods:

    - `__init__`: build a new `Vector` object.
    - `__len__`: return the length of the `Vector`.
    - `__getitem__`: return the entry that is present in the `Vector`
      at the specified index.
    - `__add__`: add this `Vector` to another one.
    - `__eq__`: check if two `Vector` objects are equal.
    - `__neq__`: check if two `Vector` objects are unequal.
    - `__repr__`: return the string representation of the `Vector`.
    - `dot`: take the dot product of this `Vector` and another.
    - `times`: take the scalar product of this `Vector` and an integral
      value or variable.
    - `basis`: return the basis vector of the given dimensionality and
      direction.
    """

    def __init__(self, *elements: Integral) -> None:
        """
        Construct a new `Vector` object.

        Parameters:

        - `elements`: the integral values or variables that are to be
          present in the resulting `Vector`.
        """
        if elements:
            self._elements = elements

        else:
            raise ValueError('Vectors cannot be empty')

    def __len__(self) -> int:
        """
        Return the number of entries that are present in the `Vector`.
        """
        return len(self._elements)

    def __getitem__(self, index: int) -> Integral:
        """
        Return the entry that is present in the `Vector` at the
        specified `index`.

        Parameters:

        - `index`: the location of the entry that should be returned.
        """
        return self._elements[index]

    def __add__(self, other: Vector) -> Vector:
        """
        Return the sum of this `Vector` with another `Vector` of equal
        length.

        Parameters:

        - `other`: the other `Vector` to be added to this one.
        """
        if len(self) == len(other):
            pairs = zip(self._elements, other._elements)
            elements = tuple(x + y for x, y in pairs)
            return Vector(*elements)

        else:
            raise ValueError('Vector operands must have equal length')

    def __eq__(self, other: Vector) -> z3.BoolRef:
        """
        Return the `z3.BoolRef` that represents equality between this
        `Vector` and another.

        Parameters:

        - `other`: the other `Vector` to compare against.
        """
        predicate = True
        if len(self) == len(other):
            for x, y in zip(self._elements, other._elements):
                predicate = z3.And(predicate, x == y)

            return z3.simplify(predicate)

        else:
            predicate = z3.And(predicate, False)
            return z3.simplify(predicate)

    def __neq__(self, other: Vector) -> z3.BoolRef:
        """
        Return the `z3.BoolRef` that represents inequality between this
        `Vector` and another.

        Parameters:

        - `other`: the other `Vector` to compare against.
        """
        return z3.Not(self == other)

    def __repr__(self) -> str:
        """Return the string representation of this `Vector`."""
        return str(self._elements)

    def dot(self, other: Vector) -> Integral:
        """
        Return the dot product of this `Vector` with another `Vector`
        of equal length.

        Parameters:

        - `other`: the other `Vector` to calculate the dot product
          with.
        """
        if len(self) == len(other):
            pairs = zip(self._elements, other._elements)
            return sum([x * y for x, y in pairs])

        else:
            raise ValueError('Vector operands must have equal length')

    def times(self, other: Integral) -> Vector:
        """
        Return the scalar product of this `Vector` with an integer Z3
        variable or primitive `int` value.

        Parameters:

        - `other`: the Z3 variable or `int` value to calculate the
          scalar product with.
        """
        elements = tuple(other * x for x in self._elements)
        return Vector(*elements)

    @staticmethod
    def basis(dim: int, index: int) -> Vector:
        """
        Returns the basis vector of dimensionality `dim` along the
        `index` dimension.

        Parameters:

        - `dim`: the dimensionality of the resulting `Vector`.
        - `index`: the index of the nonzero entry in the resulting
          `Vector`.
        """
        if pos >= dim:
            raise ValueError('Index must be smaller than dimension')

        elements = [0 for _ in range(dim)]
        elements[index] = 1
        return Vector(*tuple(elements))
