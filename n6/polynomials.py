"""Small exact sparse polynomials for coplanarity-preserving certificates.

Coefficients are rational. An identity is checked coefficient by coefficient;
interval evaluation is used only for inequalities over explicit parameter boxes.
"""
from fractions import Fraction
from n6.intervals import I


class Poly:
    def __init__(self,n,terms=()):
        if not isinstance(n,int) or n<0:raise ValueError('Invalid variable count')
        self.n=n;self.terms={}
        for coefficient,exponents in terms:
            if isinstance(coefficient,float):raise TypeError('Rational coefficient required')
            e=tuple(exponents)
            if len(e)!=n or any(not isinstance(k,int) or k<0 for k in e):
                raise ValueError('Invalid monomial')
            self.terms[e]=self.terms.get(e,Fraction(0))+Fraction(coefficient)
        self.terms={e:c for e,c in self.terms.items() if c}

    @classmethod
    def constant(cls,n,value):return cls(n,[(value,[0]*n)])

    @classmethod
    def variable(cls,n,index):
        e=[0]*n;e[index]=1
        return cls(n,[(1,e)])

    def of(self,value):
        if isinstance(value,Poly):
            if value.n!=self.n:raise ValueError('Different variable counts')
            return value
        return Poly.constant(self.n,value)

    def __add__(self,other):
        other=self.of(other)
        return Poly(self.n,[(c,e) for p in (self,other) for e,c in p.terms.items()])

    __radd__=__add__

    def __neg__(self):return Poly(self.n,[(-c,e) for e,c in self.terms.items()])

    def __sub__(self,other):return self+-self.of(other)

    def __rsub__(self,other):return self.of(other)+-self

    def __mul__(self,other):
        other=self.of(other)
        return Poly(self.n,[(c*d,tuple(x+y for x,y in zip(e,f)))
                            for e,c in self.terms.items() for f,d in other.terms.items()])

    __rmul__=__mul__

    def is_zero(self):return not self.terms

    def evaluate(self,box):
        if len(box)!=self.n:raise ValueError('Wrong parameter box dimension')
        total=I(0)
        for e,c in self.terms.items():
            term=I(c)
            for x,k in zip(box,e):
                # Squaring gives tighter bounds for even powers at zero.
                power=I(1);base=x
                while k:
                    if k&1:power=power*base
                    k//=2
                    if k:base=base.square()
                term=term*power
            total=total+term
        return total

    def json(self):return [[str(c),list(e)] for e,c in sorted(self.terms.items())]
