"""Archived floating discovery; not a proof of a point or geometric family."""
import json,math,random
from fractions import Fraction as F
import numpy as np
from n7.a992 import *
R=((0,3),(0,4),(0,6),(1,3),(2,3),(3,5))
def angle(p,a,b,c):
 u=p[a]-p[b];v=p[c]-p[b];return math.atan2(np.linalg.norm(np.cross(u,v)),u@v)
def inspect(q):
 p=points_from_parameters(q)
 if not valid(p):return
 n=unfold(p,R);sc=max(1.,np.ptp(p,axis=0).max())
 E=angle(p,6,0,3);e0=E+angle(p,4,0,6);k4=2*math.pi-angle(p,0,4,2)-angle(p,2,4,6)-angle(p,6,4,0)
 # Auxiliary face 026 attached to diagonal 26, by the six-vertex hull.
 fs=((0,2,3),(0,3,6),(0,2,6),(1,3,5),(1,3,6),(1,5,2,6),(2,3,5))
 a=unfold(p,((0,3),(0,2),(0,6),(1,3),(3,5)),fs,5)
 return {'parameters':q,'r0':e0-(3*math.pi+k4)/2,'E_obtuse':E-math.pi/2,
         'E235':penetration(n[1],n[6])/sc,'E_Q':penetration(n[1],n[0])/sc,
         'E_135':penetration(n[1],n[3])/sc,
         'left':penetration(unfold(p)[1],unfold(p)[0])/sc,
         'M0_vs235':penetration(a[2],a[6])/sc,
         'wide_base_6':angle(p,1,6,2),'angles':[angle(p,3,6,1),angle(p,3,6,0)]}
rng=random.Random(923517);rows=json.load(open('n7/results/a992-survey.json'))['failures'];rows += [{'parameters':[float(F(x)) for x in json.load(open('n7/results/'+nm))['geometry']['parameters']]} for nm in ('a992-exact-counterexample.json','a992-r0-narrow-fan-example.json','a992-length-rule-counterexample.json')]
count=0;best=None;ob=0;bestany=None
for i in range(24000):
 if i%2:
  q=list(rng.choice(rows)['parameters']);c=np.array(q[:2]);normal=np.array([-c[1],c[0]])
  t,u=sorted((rng.uniform(-3,3),rng.uniform(-3,3)),reverse=True)
  q[2:4]=(t*c+10**rng.uniform(-4,2)*normal).tolist();q[4:6]=(u*c+10**rng.uniform(-4,2)*normal).tolist()
 else:q=sample(rng)
 a=inspect(q)
 if a is None:continue
 count+=1
 if a['E_obtuse']>=0:
  ob+=1
  if bestany is None or a['E235']>bestany['E235']:bestany=a
  if a['r0']>0 and(best is None or a['E235']>best['E235']):best=a
  if a['E235']>1e-7:print('FAIL',a,flush=True);break
 if i%1000==1:print(i,count,ob,'best',None if bestany is None else bestany['E235'],flush=True)
result={'scope':'Floating discovery only; no exact or universal conclusion.','seed':923517,'attempted':i+1,'valid':count,'obtuse':ob,'best_R0':best,'best_obtuse':bestany}
open('n7/results/a992-e235-obtuse-search.json','w').write(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
