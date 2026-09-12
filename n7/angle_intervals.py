"""Outward rational intervals for ordinary angles, with explicit error bounds.

No floating approximation participates. Atan uses an alternating series
after rational argument reduction; pi uses Machin's identity.
"""
from fractions import Fraction as F
from functools import lru_cache
from n7.a992_exact import I,S,dot,cross,sub

def atan_small(q):
    q=F(q)
    if not 0<=q<=F(1,2):raise ValueError('Small atan argument outside [0,1/2]')
    power=q;total=F(0);sign=1;n=0
    while True:
        total+=sign*power/(2*n+1);power*=q*q;sign=-sign;n+=1
        following=sign*power/(2*n+1)
        if abs(following)<F(1,1<<185):
            return I.bounds(min(total,total+following),max(total,total+following))

@lru_cache(maxsize=1)
def pi():
    return 16*atan_small(F(1,5))-4*atan_small(F(1,239))

def atan_point(q):
    q=F(q)
    if q<0:return -atan_point(-q)
    if q>1:return pi()/2-atan_point(1/q)
    if q>F(1,2):return pi()/4-atan_small((1-q)/(1+q))
    return atan_small(q)

def atan(q):
    q=q if isinstance(q,I) else I.bounds(q)
    a=atan_point(F(q.lo,S));b=atan_point(F(q.hi,S))
    return I(a.lo,b.hi)

def vector_angle(a,b):
    d=dot(a,b)
    if len(a)==3:
        c=cross(a,b);h=dot(c,c).sqrt()
    elif len(a)==2:
        c=a[0]*b[1]-a[1]*b[0]
        h=c if c.lo>0 else -c
    else:raise ValueError('Expected two- or three-dimensional vectors')
    if h.lo<=0:raise ValueError('Strict noncollinearity is needed for this angle check')
    return pi()/2-atan(d/h)

def face_angle(points,face,v):
    a,b=[sub(points[u],points[v]) for u in face if u!=v]
    return vector_angle(a,b)
