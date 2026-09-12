"""Exact integer-coefficient audit of the five-patch wider-angle identity."""
from pathlib import Path
import json
N=21

def add(*xs):return [sum(q) for q in zip(*xs)]
def mul(k,x):return [k*q for q in x]
def unit(i):return [int(i==j) for j in range(N)]

def verify():
 one=unit(20);angles={}
 for s in(5,6):
  for i in range(5):
   j=2*((s-5)*5+i);angles[s,i,s]=unit(j);angles[s,i,i]=unit(j+1)
   angles[s,i,(i+1)%5]=add(one,mul(-1,unit(j)),mul(-1,unit(j+1)))
 k={v:add(mul(2,one),*(mul(-1,a) for (s,i,u),a in angles.items() if u==v)) for v in range(7)}
 checks=[]
 for q,p in((5,6),(6,5)):
  for start in range(5):
   i0,i1,i2,i3,i4=[(start+j)%5 for j in range(5)];a,b=(i1,i2)
   lam,nu,rho=[angles[q,i,q] for i in(i0,i1,i2)];K=add(k[a],k[b])
   A=add(angles[q,i3,i4],angles[q,i4,i4]);B=add(angles[p,i3,i4],angles[p,i4,i4])
   H=add(k[q],mul(-1,k[p]),B,mul(-1,A))
   S=add(mul(4,one),mul(-1,k[i0]),mul(-1,k[i3]),mul(-2,angles[q,i4,i0]),mul(-2,angles[q,i3,i3]))
   for outer,other in((lam,rho),(rho,lam)):
    lhs=add(mul(2,one),K,mul(-2,outer),mul(-1,nu));rhs=add(H,S,nu,mul(2,other));res=add(lhs,mul(-1,rhs))
    if any(res):raise ValueError('Five-patch correction identity has a nonzero coefficient')
    checks.append({'source':q,'fan':p,'first_patch':start,'zero_residual':res})
 return {'scope':'Twenty exact linear identities in twenty independent triangle-angle variables, in units of pi. This checks algebra, not universal geometric separation.',
  'identities':len(checks),'independent_angle_variables':20,'checks':checks,'geometric_proof_formally_verified':False}

if __name__=='__main__':
 r=verify();Path(__file__).resolve().parent.joinpath('results/bipyramid-receiver-identity.json').write_text(json.dumps(r,indent=2)+'\n');print('All 20 five-patch correction identities have zero integer coefficients.')
