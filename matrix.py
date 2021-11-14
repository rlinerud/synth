# Rory Linerud
# rlinerud@u.rochester.edu
#
# matrix.py

from __future__ import annotations


import z3
from synth.types import Integral
from synth.vector import Vector
from typing import Union


class Matrix:

    """
    A matrix of integral values or variables.

    Instance variables:

    - `dims`: the dimensionality of the `Matrix` as a tuple.
    - `rows`: the rows of the `Matrix` as a tuple of `Vector` objects.
    - `cols`: the columns of the `Matrix` as a tuple of `Vector`
      objects.

    Public methods:

    - `__init__`: build a new `Matrix` object.
    - `__repr__`: return the string representation of the `Matrix`.
    - `__add__`: add this `Matrix` to another one.
    - `__eq__`: check if two `Matrix` objects are equal.
    - `__neq__`: check if two `Matrix` objects are unequal.
    - `mmul`: multiply this `Matrix` with another one.
    - `smul`: multiply this `Matrix` by a given scalar.
    - `transpose`: return the transpose of this `Matrix`.
    - `identity`: build the identity `Matrix` of the specified
      dimensionality.
    - `singleton`: build a `Matrix` containing just a single entry.
    """

    def __init__(self, *rows: Vector) -> None:
        """
        Construct a new `Matrix` object.

        Parameters:

        - `rows`: the `Vector` rows of the `Matrix`.
        """
        self._validate(rows)
        self.dims = len(rows), len(rows[0])
        self.rows = rows
        self.cols = self._cols()

    @staticmethod
    def _validate(rows: tuple[Vector]) -> None:
        """
        Verify that the given `Vector` objects can together comprise a
        `Matrix`.

        Parameters:

        - `rows`: the tuple of row vectors to validate.
        """
        if rows:
            if rows[0]:
                row_len = len(rows[0])
                for row in rows:
                    if len(row) != row_len:
                        message = 'All matrix rows must have equal length'
                        raise ValueError(message)

            else:
                raise ValueError('Matrix rows cannot be empty')

        else:
            raise ValueError('Matrices cannot be empty')

    def _cols(self) -> tuple[Vector]:
        """Return the column vectors of this `Matrix`."""
        num_rows, num_cols = self.dims
        cols = []
        for j in range(num_cols):
            col = []
            for i in range(num_rows):
                entry = self.rows[i][j]
                col.append(entry)

            vector = Vector(*tuple(col))
            cols.append(vector)

        return tuple(cols)

    def __repr__(self) -> str:
        """Return the string representation of this `Matrix`."""
        return str(self.rows)

    def __add__(self, other: Matrix) -> Matrix:
        """
        Return the sum of this `Matrix` with another one of equal
        dimensions.

        Parameters:

        - `other`: the other `Matrix` to be added to this one.
        """
        if self.dims == other.dims:
            rows = tuple(x + y for x, y in zip(self.rows, other.rows))
            return Matrix(*rows)

        else:
            raise ValueError('Matrix dimension mismatch')

    def __eq__(self, other: Matrix) -> z3.BoolRef:
        """
        Return the `z3.BoolRef` that represents equality between this
        `Matrix` and another.

        Parameters:

        - `other`: the other `Matrix` to compare against.
        """
        predicate = True
        if self.dims == other.dims:
            for x, y in zip(self.rows, other.rows):
                predicate = z3.And(predicate, x == y)

            return z3.simplify(predicate)

        else:
            predicate = z3.And(predicate, False)
            return z3.simplify(predicate)

    def __neq__(self, other: Matrix) -> z3.BoolRef:
        """
        Return the `z3.BoolRef` that represents inequality between this
        `Matrix` and another.

        Parameters:

        - `other`: the other `Matrix` to compare against.
        """
        predicate = z3.Not(self == other)
        return z3.simplify(predicate)

    def mmul(self, other: Matrix) -> Matrix:
        """
        Return the product of this `Matrix` with another one of
        compatible dimensions.

        Parameters:

        - `other`: the other `Matrix` to multiply this one with.
        """
        num_rows, num_cols = other.dims[0], self.dims[1]
        if num_rows == num_cols:
            new_rows = []
            for row in self.rows:
                new_row = []
                for col in other.cols:
                    new_row.append(row.dot(col))

                vector = Vector(*tuple(new_row))
                new_rows.append(vector)

            return Matrix(*tuple(new_rows))

        else:
            raise ValueError('Matrix dimension mismatch')

    def smul(self, other: Integral) -> Matrix:
        """
        Return the scalar product of this `Matrix` with an integral
        variable or value.

        Parameters:

        - `other`: the scalar value or variable to multiply this
          `Matrix` with.
        """
        rows = []
        for row in self.rows:
            rows.append(row.times(other))

        return Matrix(*tuple(rows))

    def transpose(self) -> Matrix:
        """Return the transpose of this `Matrix`."""
        return Matrix(*self.cols)

    @staticmethod
    def identity(dim: int) -> Matrix:
        """
        Return the identity `Matrix` of dimensionality `dim`.

        Parameters:

        - `dim`: the number of rows and columns in the resulting
          `Matrix`.
        """
        rows = []
        for i in range(dim):
            vector = Vector.basis(dim, i)
            rows.append(vector)

        return Matrix(*tuple(rows))

    @staticmethod
    def singleton(entry: Integral) -> Matrix:
        """
        Return the singleton `Matrix` that contains just the given
        `entry`.

        Parameters:

        - `entry`: the integral value or variable to include in the
          `Matrix`.
        """
        return Matrix(Vector(entry))
