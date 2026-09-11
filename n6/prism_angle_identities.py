"""Exact coefficient audit of the three universal prism angle identities.

Normalize pi to 1 and eliminate one angle per face with its exact face-angle
sum. The remaining 14 angles are independent indeterminates. Vanishing of
every rational coefficient proves each stated identity for all assignments
satisfying those sums; positivity is supplied by the written geometric proof.
"""
from fractions import Fraction as F
from n6.certify import require
from n6.families import PRISM_FACES
from n6.polynomials import Poly


def expressions():
    n=sum(len(f)-1 for f in PRISM_FACES);a={};j=0
    for label,face in zip('ABCDEF',PRISM_FACES):
        for v in face[:-1]:a[label+str(v)]=Poly.variable(n,j);j+=1
        a[label+str(face[-1])]=Poly.constant(n,len(face)-2)-sum(a[label+str(v)] for v in face[:-1])
    k={v:2-sum(a[label+str(v)] for label,face in zip('ABCDEF',PRISM_FACES) if v in face) for v in range(6)}
    slack=lambda name:2-k[int(name[1:])]-2*a[name]
    K=k[3]+k[4]
    fC=2*a['C1']+a['E1']-2-K;fD=2*a['D1']+a['E1']-2-K
    gB=2*a['B5']+a['F5']-2-K;gD=2*a['D5']+a['F5']-2-K
    return [fC+2*a['C0']+slack('B3')+slack('D4')+a['E1']+2*a['F5'],
            fD+gD+2*a['D2']+2*a['E3']+2*a['F3']+2*k[3]+a['E1']+a['F5'],
            fD+gB+slack('A0')+slack('A2')+slack('B5')+2*a['C1']+a['E3']+a['F3']+(1-a['D4'])+k[1]+k[3]+2*(a['E1']-F(1,2))]


def verify():
    polys=expressions();require(all(p.is_zero() for p in polys),'A stated prism angle identity is false')
    return dict(result='verified_exact_prism_angle_identities',identities=3,
                independent_angle_indeterminates=polys[0].n,arithmetic='Exact rational polynomial coefficients',
                geometry_or_positivity_formally_verified=False,proof='PRISM_SHARP_FAN_SWITCH.md')


if __name__=='__main__':
    import json
    print(json.dumps(verify(),indent=2))
