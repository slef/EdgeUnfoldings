"""Explicit coordinate charts that retain nonsimplicial facet equations.

These builders propose input for polycert. Their output is checked from scratch;
the checker does not trust claims about a chart's topology or parameter domain.
"""
from n6.polynomials import Poly
from fractions import Fraction as F

PRISM_FACES=((0,2,1),(0,3,5,2),(0,1,3),(1,2,5,4),(1,4,3),(3,4,5))
PRISM_CUTS=((0,2),(1,2),(2,5),(3,5),(4,5))
MINUS_FACES=((0,2,1,3),(0,4,2),(0,5,4),(0,3,5),(1,5,3),(1,4,5),(1,2,4))


def region(box,points,faces,cuts,names):
    return dict(schema='n6-polyhedron-region-v1',parameter_names=list(names),
                parameter_box=[list(q) for q in box],
                coordinate_polynomials=[[p.json() for p in point] for point in points],
                faces=[list(f) for f in faces],cut_edges=[list(e) for e in cuts])


def prism_region(box,cuts=PRISM_CUTS):
    if len(box)!=9:raise ValueError('Expected nine parameters')
    x,y,u,v,w,A,B,C,D=[Poly.variable(9,i) for i in range(9)]
    zero=Poly.constant(9,0);one=Poly.constant(9,1)
    a=(one,zero,zero);b=(x,y,zero);c=(zero,zero,zero);cp=(u,v,w)
    ap=tuple(A*a[i]+B*cp[i] for i in range(3))
    bp=tuple(C*b[i]+D*cp[i] for i in range(3))
    return region(box,[a,b,c,ap,bp,cp],PRISM_FACES,cuts,('x','y','u','v','w','A','B','C','D'))


def minus_region(box,cuts):
    if len(box)!=10:raise ValueError('Expected ten parameters')
    x,y,u,v,r,s,h,t,k,l=[Poly.variable(10,i) for i in range(10)]
    zero=Poly.constant(10,0);one=Poly.constant(10,1)
    points=[(zero,zero,zero),(x,y,zero),(one,zero,zero),(u,v,zero),(r,s,-h),(t,k,-l)]
    return region(box,points,MINUS_FACES,cuts,('x','y','u','v','r','s','h','t','k','l'))


def center_parameters(spec):
    """Exact affine change of parameters, improving interval cancellations.

    Original parameter i equals parameter_origin[i] plus the new parameter i.
    The coordinate polynomials themselves encode the whole change; the checker
    does not trust the descriptive metadata.
    """
    n=len(spec['parameter_box']);centers=[(F(a)+F(b))/2 for a,b in spec['parameter_box']]
    variables=[Poly.variable(n,i)+c for i,c in enumerate(centers)]
    def translated(raw):
        result=Poly.constant(n,0)
        for coefficient,exponents in raw:
            term=Poly.constant(n,coefficient)
            for var,e in zip(variables,exponents):
                for _ in range(e):term=term*var
            result=result+term
        return result.json()
    return {**spec,'parameter_origin':[str(c) for c in centers],
            'parameter_box':[[str(F(a)-c),str(F(b)-c)] for (a,b),c in zip(spec['parameter_box'],centers)],
            'coordinate_polynomials':[[translated(q) for q in p] for p in spec['coordinate_polynomials']]}
