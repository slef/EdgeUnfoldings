"""Archived floating discovery; not a proof of a point or geometric family."""
import json,math,random
from fractions import Fraction as F
import numpy as np
from n7.a992 import *
R=((0,3),(0,4),(0,6),(1,3),(2,3),(3,5));rng=random.Random(912353)
rows=json.load(open('n7/results/a992-survey.json'))['failures']+json.load(open('n7/results/a992-local-corner-search.json'))['failures'];best={};counts=[0,0]
for i in range(65000):
 if i%3:
  q=list(rng.choice(rows)['parameters']);c=np.array(q[:2]);normal=np.array([-c[1],c[0]]);t,u=sorted((rng.uniform(-5,5),rng.uniform(-5,5)),reverse=True)
  q[2:4]=(t*c+10**rng.uniform(-5,2)*normal).tolist();q[4:6]=(u*c+10**rng.uniform(-5,2)*normal).tolist()
 else:q=sample(rng)
 p=points_from_parameters(q)
 if not valid(p):continue
 n=unfold(p,R);P,A,C=n[1];L=(P-A)@(P-A);ob=(p[6]-p[0])@(p[3]-p[0])<0;sc=max(1,np.ptp(p,axis=0).max());counts[int(ob)]+=1
 for j in (3,6):
  A2=n[j][1];score=((P-A2)@(P-A2)-L)/sc**2;key=f'{j}_'+('obtuse' if ob else 'acute')
  if key not in best or score<best[key]['difference']:
   best[key]={'difference':score,'q':q,'penetration':penetration(n[1],n[j])/sc}
 if i%5000==0:print(i,counts,{k:v['difference'] for k,v in best.items()},flush=True)
res={'scope':'Floating discovery only.','seed':912353,'trials':65000,'counts_acute_obtuse':counts,'best':best};open('n7/results/a992-e235-voronoi-search.json','w').write(json.dumps(res,indent=2)+'\n');print(json.dumps(res),flush=True)
