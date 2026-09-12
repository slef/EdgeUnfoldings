"""Linear exploration that led to the exact identity; not a proof checker."""
import numpy as np
from scipy.optimize import linprog
faces=((0,3,6),(0,6,5),(0,5,3),(1,3,6),(1,6,5),(1,5,3))
ids={(i,v):3*i+j for i,f in enumerate(faces) for j,v in enumerate(f)}
def term(*pairs):
 v=np.zeros(18)
 for coef,i,p in pairs:v[ids[i,p]]+=coef
 return v
G={v:term(*[(1,i,v) for i,f in enumerate(faces) if v in f]) for v in (0,1,3,5,6)}
A=[];b=[];names=[]
def add(row,B,name):A.append(row);b.append(B);names.append(name)
for v,row in G.items():add(row,2-1e-7,'curvature'+str(v))
for (i,v),j in ids.items():add(2*np.eye(18)[j]-G[v],-1e-7,'link'+str((i,v)))
add(-term((1,0,0)),-.5,'obtuse source0');add(G[1],1-1e-7,'sharp1');add(-term((1,0,6),(1,3,6)),-1-1e-7,'inward6')
eq=[term(*[(1,i,v) for v in f]) for i,f in enumerate(faces)]
expr=2*term((1,4,6),(1,1,6),(1,4,1))-G[6]
r=linprog(expr,A_ub=A,b_ub=b,A_eq=eq,b_eq=np.ones(6),bounds=[(1e-7,None)]*18,method='highs')
print(r.message,'min',r.fun+1 if r.success else None)
if r.success:print({str(faces[i]):dict(zip(faces[i],r.x[3*i:3*i+3])) for i in range(6)})
from fractions import Fraction
print('ineq dual',[(name,str(Fraction(float(z)).limit_denominator(100))) for name,z in zip(names,r.ineqlin.marginals) if abs(z)>1e-7])
print('eq dual',[(i,str(Fraction(float(z)).limit_denominator(100))) for i,z in enumerate(r.eqlin.marginals) if abs(z)>1e-7])
print('bounds',[(next(k for k,v in ids.items() if v==i),str(Fraction(float(z)).limit_denominator(100))) for i,z in enumerate(r.lower.marginals) if abs(z)>1e-7])
