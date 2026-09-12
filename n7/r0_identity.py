"""Check the R0 proof's angle identity with exact integer coefficients.

This validates one displayed algebraic step, not the geometric containment
argument or an entire proof-assistant formalization. No optimizer is used.
"""
from pathlib import Path
import json

FACES=((0,3,6),(0,6,5),(0,5,3),(1,3,6),(1,6,5),(1,5,3))
VARIABLES=[f'f{i}_at_{v}' for i,f in enumerate(FACES) for v in f]+['pi']

def unit(name):return [int(x==name) for x in VARIABLES]
def add(*rows):return [sum(c) for c in zip(*rows)]
def scale(k,row):return [k*x for x in row]
def angle(i,v):return unit(f'f{i}_at_{v}')

def verify():
    pi=unit('pi')
    gamma=add(*(angle(i,6) for i,f in enumerate(FACES) if 6 in f))
    theta=add(angle(1,6),angle(4,6))
    # delta is an independent positive angle, appended as the last coordinate.
    def extend(row):return row+[0]
    delta=[0]*len(VARIABLES)+[1]
    curvature=add(scale(2,pi),scale(-1,gamma))
    lhs=add(extend(add(scale(2,theta),curvature,scale(-1,pi))),scale(2,delta))
    link=add(gamma,scale(-2,angle(3,6)))
    rhs=add(extend(add(link,scale(2,angle(0,0)),scale(-1,pi),scale(2,angle(0,3)))),scale(2,delta))
    triangle=add(*(angle(0,v) for v in FACES[0]),scale(-1,pi))
    residual=add(lhs,scale(-1,rhs),extend(scale(2,triangle)))
    if any(residual):raise AssertionError('Displayed angle identity does not expand')
    return {'scope':'Exact linear-identity check only; geometry is proved in A992_R0.md.',
            'variables':VARIABLES+['delta'],
            'zero_residual':residual,
            'identity':'2 theta + 2 delta + kappa_c - pi = L + (2 nu - pi) + 2 epsilon + 2 delta',
            'assumptions':['nu >= pi/2','L > 0 by the strict spherical-link side inequality',
                           'epsilon > 0','delta > 0'],
            'conclusion':'The right side is strictly positive, contradicting the overlap inequality.'}

if __name__=='__main__':
    report=verify()
    path=Path(__file__).resolve().parent/'results/a992-r0-angle-identity.json'
    path.write_text(json.dumps(report,indent=2)+'\n')
    print('All integer coefficients cancel; the overlap contradiction has four nonnegative terms.')
