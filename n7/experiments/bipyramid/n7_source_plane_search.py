"""Stress the proposed source supporting-plane rule. Floating only."""
import json,math,random,time,itertools
from pathlib import Path
import numpy as np
from n7_pair_class_search import measurements
from n7_two_gap_wide_search import sample
from n7.a992 import unfold,penetration
from n7.bipyramid_morph import FACES
from n7.checks import canonical_pattern
rng=random.Random(913920);start=time.time();counts={};examples={};bad=[];valid=checked=0
base=np.array([[-1504,-547,0],[100,0,0],[129,153,0],[-69,394,0],[-693,400,0],[0,0,1],[0,0,-1]],float)
for attempt in range(200000):
 if rng.random()<.45:
  p=base.copy();p[:5,2]=[rng.uniform(-.9,.9) for _ in range(5)];p[5,2]*=10**rng.uniform(-.7,1);p[6,2]*=10**rng.uniform(-.7,1)
 else:p=sample(rng)
 m=measurements(p)
 if m is None:continue
 valid+=1
 for q in(5,6):
  f=11-q;axis=p[f]-p[q];g=(p[:5]-p[q])@axis
  if min(g)<1e-9:continue
  checked+=1;k=max(range(5),key=lambda i:np.linalg.norm(p[5]-p[i])+np.linalg.norm(p[6]-p[i]));cut=[(q,i) for i in range(5)]+[(f,k)];n=unfold(p,cut,FACES,0)
  pair=max((penetration(n[i],n[j]),i,j) for i,j in itertools.combinations(range(10),2));key=canonical_pattern(m['pattern']);counts[key]=counts.get(key,0)+1
  row={'points':p.tolist(),'source':q,'slit':k,'pattern':m['pattern'],'source_plane_min':float(min(g)),'curvatures':m['curvatures'],'worst_penetration':pair}
  if key not in examples and max(m['curvatures'][5:])<math.pi:examples[key]=row;print('FIRST',key,checked,flush=True)
  if pair[0]>1e-7:
   bad.append(row);print('SUSPECT',pair,flush=True)
   if len(bad)>5:break
 if len(bad)>5:break
 if time.time()-start>240:break
out={'scope':'Floating stress test only; no universal conclusion follows from the counts. Suspect overlaps require exact checking.','attempts':attempt+1,'valid':valid,'checked_pole_choices':checked,'case_counts':counts,'examples':examples,'suspect_overlaps':bad};Path('/private/tmp/n7_source_plane_search.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',attempt,valid,checked,counts,len(bad),time.time()-start,flush=True)
