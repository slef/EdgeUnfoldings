"""Archived test of the hinge-line shortcut; floating discovery only."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
from n7.a992 import *
import numpy as np,random,math,json
from fractions import Fraction
R=((0,3),(0,4),(0,6),(1,3),(2,3),(3,5))
rows=json.load(open('n7/results/a992-survey.json'))['failures']
row=json.load(open('n7/results/a992-exact-counterexample.json'))
rows.append({'parameters':[float(Fraction(x)) for x in row['geometry']['parameters']]})
cross=lambda x,y: x[0]*y[1]-x[1]*y[0]
def ang(p,a,b,c):
 u=p[a]-p[b];v=p[c]-p[b];return math.atan2(np.linalg.norm(np.cross(u,v)),u@v)
def r0(p):
 e0=ang(p,4,0,6)+ang(p,6,0,3);k4=2*math.pi-ang(p,0,4,2)-ang(p,2,4,6)-ang(p,6,4,0)
 return e0-(3*math.pi+k4)/2
rng=random.Random(71388);valids=0;best=None
for source,row in enumerate(rows):
 q0=list(row['parameters']);C=np.array(q0[:2]);N=np.array([-C[1],C[0]])
 for i in range(7000):
  q=q0.copy();t,tt=sorted([rng.uniform(-5,5),rng.uniform(-5,5)],reverse=True)
  h,hh=10**rng.uniform(-3,2),10**rng.uniform(-3,2)
  q[2:4]=(t*C+h*N).tolist();q[4:6]=(tt*C+hh*N).tolist()
  p=points_from_parameters(q)
  if not valid(p):continue
  valids+=1;n=unfold(p,R);a,b=n[1][1],n[1][2];d=b-a;side=np.sign(cross(d,n[1][0]-a));scale=max(1.,np.ptp(p,axis=0).max())
  margins=[max(side*cross(d,x-a) for x in n[j])/scale**2 for j in (0,3,6)]
  scores=[penetration(n[1],n[j])/scale for j in (0,3,6)]
  result={'q':q,'r0_margin':r0(p),'line36_wrong_sides':margins,'right_pairs':scores}
  if best is None or max(margins)>max(best['line36_wrong_sides']):best=result
 print(source,valids,'best',max(best['line36_wrong_sides']) if best else None,flush=True)
print(json.dumps(best,indent=2),flush=True)
best['scope']='Numerical failure of a proposed separator, not of the unfolding rule.'
best['valid_extensions']=valids;best['seed']=71388
(ROOT/'results/a992-r0-line36-search.json').write_text(json.dumps(best,indent=2)+'\n')
