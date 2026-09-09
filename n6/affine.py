"""Rational affine forms with rigorously bounded nonlinear remainders.

An object encloses c + sum(a_i*epsilon_i) + r, where |epsilon_i|<=1 and
r belongs to an outward rational interval. Shared linear terms cancel exactly.
Products, reciprocals, and square roots bound their nonlinear remainder by
identities; coefficient rounding is added to r, never discarded.
"""
from fractions import Fraction as F
from n6.intervals import I,floor_grid


class A:
    def __init__(self,c=0,coefficients=None,remainder=None):
        if isinstance(c,float):raise TypeError('Rational constants required')
        c=F(c);self.c=floor_grid(c);self.a={};rounding=F(0)
        for i,value in (coefficients or {}).items():
            if isinstance(value,float):raise TypeError('Rational coefficients required')
            value=F(value);rounded=floor_grid(value)
            if rounded:self.a[i]=rounded
            rounding+=abs(value-rounded)
        self.r=(remainder if remainder is not None else I(0))+I(c-self.c)+I(-rounding,rounding)
        self.radius=sum(map(abs,self.a.values()),F(0))
        self.bound=I(self.c)+I(-self.radius,self.radius)+self.r

    @staticmethod
    def of(x):
        if isinstance(x,A):return x
        if isinstance(x,I):
            c=(x.lo+x.hi)/2
            return A(c,remainder=x-I(c))
        return A(x)

    @classmethod
    def variable(cls,lo,hi,index):
        if isinstance(lo,float) or isinstance(hi,float):raise TypeError('Rational interval required')
        lo,hi=F(lo),F(hi)
        if lo>hi:raise ValueError('Reversed interval')
        return cls((lo+hi)/2,{index:(hi-lo)/2}).narrowed(I(lo,hi))

    def narrowed(self,other_bound):
        """Intersect two independently valid enclosures of the actual value."""
        self.bound=I(max(self.lo,other_bound.lo),min(self.hi,other_bound.hi))
        return self

    @property
    def lo(self):return self.bound.lo

    @property
    def hi(self):return self.bound.hi

    def pair(self):return self.bound.pair()

    def deviation(self):return self.bound-self.c

    def __add__(self,other):
        b=A.of(other);coefficients=self.a.copy()
        for i,value in b.a.items():coefficients[i]=coefficients.get(i,F(0))+value
        return A(self.c+b.c,coefficients,self.r+b.r).narrowed(self.bound+b.bound)

    __radd__=__add__

    def __neg__(self):return A(-self.c,{i:-v for i,v in self.a.items()},-self.r).narrowed(-self.bound)

    def __sub__(self,other):return self+-A.of(other)

    def __rsub__(self,other):return A.of(other)+-self

    def __mul__(self,other):
        b=A.of(other);indices=self.a.keys()|b.a.keys()
        coefficients={i:self.c*b.a.get(i,F(0))+b.c*self.a.get(i,F(0)) for i in indices}
        remainder=self.c*b.r+b.c*self.r+self.deviation()*b.deviation()
        return A(self.c*b.c,coefficients,remainder).narrowed(self.bound*b.bound)

    __rmul__=__mul__

    def square(self):
        return A(self.c*self.c,{i:2*self.c*v for i,v in self.a.items()},
                 2*self.c*self.r+self.deviation().square()).narrowed(self.bound.square())

    def recentered(self):
        c=(self.lo+self.hi)/2
        return A(c,self.a,self.r+I(self.c-c)).narrowed(self.bound)

    def reciprocal(self):
        if self.lo<=0<=self.hi:raise ValueError('Division interval includes zero')
        x=self if self.c else self.recentered();c=x.c
        # 1/x = 1/c - (x-c)/c^2 + (x-c)^2/(c^2*x).
        remainder=-x.r/(c*c)+x.deviation().square()/(c*c*x.bound)
        return A(1/c,{i:-v/(c*c) for i,v in x.a.items()},remainder).narrowed(I(1)/x.bound)

    def __truediv__(self,other):return self*A.of(other).reciprocal()

    def __rtruediv__(self,other):return A.of(other)*self.reciprocal()

    def sqrt(self):
        if self.lo<0:raise ValueError('Negative square-root interval')
        if self.hi==0:return A(0)
        x=self if self.c>0 else self.recentered()
        s_interval=I(x.c).sqrt();s=(s_interval.lo+s_interval.hi)/2
        if s<=0:raise ValueError('Square-root linearization is unresolved')
        # sqrt(x) = s + (x-s^2)/(2s) - (sqrt(x)-s)^2/(2s).
        remainder=x.r/(2*s)-(x.bound.sqrt()-s).square()/(2*s)
        return A(s+(x.c-s*s)/(2*s),{i:v/(2*s) for i,v in x.a.items()},remainder).narrowed(x.bound.sqrt())
