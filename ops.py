# Rory Linerud
# rlinerud@u.rochester.edu
#
# ops.py

from synth.types import Arithmetic, Boolean, Integral
from z3 import And, Bool, BoolRef, Implies, Int, Not, Real, Or, Xor


def _nand(a: Boolean, b: Boolean) -> BoolRef:
    return Not(And(a, b))


def _nor(a: Boolean, b: Boolean) -> BoolRef:
    return Not(Or(a, b))


def _iff(a: Boolean, b: Boolean) -> BoolRef:
    return And(Implies(a, b), Implies(b, a))


def _add(a: Arithmetic, b: Arithmetic) -> Arithmetic:
    return a + b


def _sub(a: Arithmetic, b: Arithmetic) -> Arithmetic:
    return a - b


def _mul(a: Arithmetic, b: Arithmetic) -> Arithmetic:
    return a * b


def _div(a: Arithmetic, b: Arithmetic) -> Real:
    return a / b


def _mod(a: Integral, b: Integral) -> Integral:
    return a % b


def _pow(a: Arithmetic, b: Arithmetic) -> Arithmetic:
    return a ** b


def _neg(a: Arithmetic) -> Arithmetic:
    return -a


def _leq(a: Arithmetic, b: Arithmetic) -> Boolean:
    return a <= b


def _lt(a: Arithmetic, b: Arithmetic) -> Boolean:
    return a < b


def _gt(a: Arithmetic, b: Arithmetic) -> Boolean:
    return a > b


def _geq(a: Arithmetic, b: Arithmetic) -> Boolean:
    return a >= b


def _eq(a: Arithmetic, b: Arithmetic) -> Boolean:
    return a == b


def _neq(a: Arithmetic, b: Arithmetic) -> Boolean:
    return a != b


ops = {
    'NOT': {
        'func': Not,
        'inputs': (Bool,),
        'output': Bool,
    },

    'AND': {
        'func': And,
        'inputs': (Bool, Bool),
        'output': Bool,
    },

    'OR': {
        'func': Or,
        'inputs': (Bool, Bool),
        'output': Bool,
    },

#    'XOR': {
#        'func': Xor,
#        'inputs': (Bool, Bool),
#        'output': Bool,
#    },

#    'IF': {
#        'func': Implies,
#        'inputs': (Bool, Bool),
#        'output': Bool,
#    },

#    'NAND': {
#        'func': _nand,
#        'inputs': (Bool, Bool),
#        'output': Bool,
#    },

#    'NOR': {
#        'func': _nor,
#        'inputs': (Bool, Bool),
#        'output': Bool,
#    },

#    'IFF': {
#        'func': _iff,
#        'inputs': (Bool, Bool),
#        'output': Bool,
#    },

    'ADD': {
        'func': _add,
        'inputs': (Real, Real),
        'output': Real,
    },

#    'SUB': {
#        'func': _sub,
#        'inputs': (Real, Real),
#        'output': Real,
#    },

    'MUL': {
        'func': _mul,
        'inputs': (Real, Real),
        'output': Real,
    },

    'DIV': {
        'func': _div,
        'inputs': (Real, Real),
        'output': Real,
    },

#    'MOD': {
#        'func': _mod,
#        'inputs': (Int, Int),
#        'output': Int,
#    },

#    'POW': {
#        'func': _pow,
#        'inputs': (Real, Real),
#        'output': Real,
#    },

    'NEG': {
        'func': _neg,
        'inputs': (Real,),
        'output': Real,
    },

#    'LEQ': {
#        'func': _leq,
#        'inputs': (Real, Real),
#        'output': Bool,
#    },

    'LT': {
        'func': _lt,
        'inputs': (Real, Real),
        'output': Bool,
    },

#    'GT': {
#        'func': _gt,
#        'inputs': (Real, Real),
#        'output': Bool,
#    },

#    'GEQ': {
#        'func': _geq,
#        'inputs': (Real, Real),
#        'output': Bool,
#    },

    'EQ': {
        'func': _eq,
        'inputs': (Real, Real),
        'output': Bool,
    },

#    'NEQ': {
#        'func': _neq,
#        'inputs': (Real, Real),
#        'output': Bool,
#    },
}
