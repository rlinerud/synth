# Rory Linerud
# rlinerud@u.rochester.edu
#
# vector.py

from __future__ import annotations

import z3
from synth.types import Entry, Integral

class Vector:

    """
    A finite sequence of boolean or integral values or variables.

    Instance variables:

    - `entries`: the entries of the `Vector` as a tuple.
    - `kind`: the type of the entries of the `Vector`.

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
    - `basis`: return the basis `Vector` of the given dimensionality
      and direction.
    """

    def __init__(self, *entries: Entry) -> None:
        """
        Construct a new `Vector` object.

        Parameters:

        - `entries`: the values or variables that are to be present in
          the resulting `Vector`.
        """
        self._validate(entries)
        self.entries = entries
        self.kind = type(entries[0])

    @staticmethod
    def _validate(entries: tuple[Entry]) -> None:
        if entries:
            kind = type(entries[0])
            for entry in entries:
                if type(entry) is not kind:
                    raise ValueError('All entries must have the same type')

        else:
            raise ValueError('Vectors cannot be empty')

    def __len__(self) -> int:
        """
        Return the number of entries that are present in the `Vector`.
        """
        return len(self.entries)

    def __getitem__(self, index: int) -> Entry:
        """
        Return the entry that is present in the `Vector` at the
        specified `index`.

        Parameters:

        - `index`: the location of the entry that should be returned.
        """
        return self.entries[index]

    def __add__(self, other: Vector) -> Vector:
        """
        Return the sum of this `Vector` with another `Vector` of equal
        length.

        Parameters:

        - `other`: the other `Vector` to be added to this one.
        """
        if self.kind not in [z3.ArithRef, int]:
            raise AttributeError('Vector entries must be integral')

        if other.kind not in [z3.ArithRef, int]:
            raise ValueError('Vector entries must be integral')

        if len(self) == len(other):
            pairs = zip(self.entries, other.entries)
            entries = tuple(x + y for x, y in pairs)
            return Vector(*entries)

        else:
            raise ValueError('Vector length mismatch')

    def __eq__(self, other: Vector) -> z3.BoolRef:
        """
        Return the `z3.BoolRef` that represents equality between this
        `Vector` and another.

        Parameters:

        - `other`: the other `Vector` to compare against.
        """
        predicate = True
        if len(self) == len(other):
            for x, y in zip(self.entries, other.entries):
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
        predicate = z3.Not(self == other)
        return z3.simplify(predicate)

    def __repr__(self) -> str:
        """Return the string representation of this `Vector`."""
        return str(self.entries)

    def dot(self, other: Vector) -> Integral:
        """
        Return the dot product of this `Vector` with another `Vector`
        of equal length.

        Parameters:

        - `other`: the other `Vector` to calculate the dot product
          with.
        """
        if self.kind not in [z3.ArithRef, int]:
            raise AttributeError('Vector entries must be integral')

        if other.kind not in [z3.ArithRef, int]:
            raise ValueError('Vector entries must be integral')

        if len(self) == len(other):
            pairs = zip(self.entries, other.entries)
            return sum([x * y for x, y in pairs])

        else:
            raise ValueError('Vector length mismatch')

    def times(self, other: Integral) -> Vector:
        """
        Return the scalar product of this `Vector` with an integer Z3
        variable or primitive `int` value.

        Parameters:

        - `other`: the Z3 variable or `int` value to calculate the
          scalar product with.
        """
        if self.kind not in [z3.ArithRef, int]:
            raise AttributeError('Vector entries must be integral')

        if type(other) not in [z3.ArithRef, int]:
            raise TypeError('Scalar must be integral')

        entries = tuple(other * x for x in self.entries)
        return Vector(*entries)

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
        if index >= dim:
            raise ValueError('Index must be smaller than dimension')

        entries = [0 for _ in range(dim)]
        entries[index] = 1
        return Vector(*tuple(entries))
