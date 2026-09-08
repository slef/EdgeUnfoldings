"""Outward dyadic interval arithmetic, using only integer/rational operations.

All operations round OUT. No binary floating point enters a certificate.
Precision affects success, never validity: an undecided sign stays undecided.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt

BITS = 80
SCALE = 1 << BITS


def floor_grid(x):
    return F((x.numerator * SCALE) // x.denominator, SCALE)


def ceil_grid(x):
    return -floor_grid(-x)


@dataclass(frozen=True)
class I:
    lo: F
    hi: F

    def __init__(self, lo, hi=None):
        if isinstance(lo, float) or isinstance(hi, float):
            raise TypeError('Use integers or rational strings, never floats')
        lo = F(lo)
        hi = lo if hi is None else F(hi)
        if lo > hi:
            raise ValueError('Reversed interval')
        object.__setattr__(self, 'lo', floor_grid(lo))
        object.__setattr__(self, 'hi', ceil_grid(hi))

    @staticmethod
    def of(x):
        return x if isinstance(x, I) else I(x)

    def __add__(self, other):
        b = I.of(other)
        return I(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -I.of(other)

    def __rsub__(self, other):
        return I.of(other) + -self

    def __mul__(self, other):
        b = I.of(other)
        vals = [a * c for a in (self.lo, self.hi) for c in (b.lo, b.hi)]
        return I(min(vals), max(vals))

    __rmul__ = __mul__

    def __truediv__(self, other):
        b = I.of(other)
        if b.lo <= 0 <= b.hi:
            raise ValueError('Division interval includes zero')
        return self * I(1 / b.hi, 1 / b.lo)

    def square(self):
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        return I(low, max(self.lo**2, self.hi**2))

    def sqrt(self):
        if self.lo < 0:
            raise ValueError('Negative square-root interval')
        def lower(x):
            return isqrt((x.numerator * SCALE**2) // x.denominator)
        a, b = lower(self.lo), lower(self.hi)
        if F(b*b, SCALE*SCALE) != self.hi:
            b += 1
        return I(F(a, SCALE), F(b, SCALE))

    def pair(self):
        return [str(self.lo), str(self.hi)]


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), I(0))


def norm2(a):
    return sum((x.square() for x in a), I(0))


def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])


def det(a, b):
    return a[0]*b[1]-a[1]*b[0]
