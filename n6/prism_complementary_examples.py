"""Exact examples of the new complementary-route prism family."""
from fractions import Fraction as F
import json
from pathlib import Path
from n6.families import PRISM_FACES,region
from n6.polycert import point_spec,make_certificate,verify as all_pairs
from n6.polynomials import Poly
from n6.intervals import set_precision
from n6.prism_complementary_routes import select

NUMERATORS=[[900,0,1020],[-1200,580,1740],[0,0,0],[-300,-480,2664],[-2580,100,3180],[-1380,-480,1440]]
DENOMINATORS=[10,430,110,310,750,430]


def specification(family=False,reflected=False,points=None):
    p=([[F(x,d) for x in row] for row,d in zip(NUMERATORS,DENOMINATORS)]
       if points is None else [[F(x) for x in row] for row in points])
    if reflected:p=[p[i] for i in [4,3,5,1,0,2]]
    p=[[x-y for x,y in zip(row,p[2])] for row in p]
    scale=max(abs(x) for row in p for x in row);p=[[x/scale for x in row] for row in p]
    cuts=[[0,1],[1,2],[1,3],[1,4],[2,5]]
    if not family:return point_spec([[str(x) for x in row] for row in p],PRISM_FACES,cuts)
    def coefficients(a,b,q):
        for i in range(3):
            for j in range(i+1,3):
                det=a[i]*b[j]-a[j]*b[i]
                if det:
                    x=(q[i]*b[j]-q[j]*b[i])/det;y=(a[i]*q[j]-a[j]*q[i])/det
                    assert all(x*a[k]+y*b[k]==q[k] for k in range(3))
                    return x,y
        raise ValueError('Degenerate basis')
    a,b=coefficients(p[0],p[5],p[3]);c,d=coefficients(p[1],p[5],p[4])
    z0,x1,y1,z1,a3,b3,c4,d4,h=[Poly.variable(9,i) for i in range(9)]
    zero=Poly.constant(9,0)
    p1=[(1+y1)*p[1][i]+x1*p[0][i]+z1*p[5][i] for i in range(3)]
    pts=[[p[0][i]+z0*p[5][i] for i in range(3)],p1,[zero]*3,
         [(a+a3)*p[0][i]+(b+b3)*p[5][i] for i in range(3)],
         [(c+c4)*p1[i]+(d+d4)*p[5][i] for i in range(3)],
         [(1+h)*p[5][i] for i in range(3)]]
    return {**region([['-1/100000000','1/100000000']]*9,pts,PRISM_FACES,cuts,
                     ['z0','x1','y1','z1','a3','b3','c4','d4','h']),
            'arithmetic_mode':'affine','suggested_fractional_bits':240,
            'family_description':'Nine independent shape parameters in the two original quad planes.'}


def main():
    set_precision(240);root=Path(__file__).parent/'results'
    for family,reflected in [(False,False),(True,False),(False,True)]:
        s=specification(family,reflected);r=select(s)
        cert=make_certificate({**s,'cut_edges':r['cut_edges']})
        report=dict(choice=r,independent_all_original_pairs=all_pairs(cert))
        name='prism-complementary'+('-family' if family else '-reflected' if reflected else '-point')
        for suffix,value in [('certificate',cert),('verification',report)]:
            (root/f'{name}.{suffix}.json').write_text(json.dumps(value,indent=2)+'\n')
        print(name,r['branch'],'verified',flush=True)


if __name__=='__main__':main()
