"""Discover failures of the ordered-run sufficient rule. Floating only."""
import json,time,random
from pathlib import Path
import numpy as np
from n7_pair_class_search import measurements
from n7_two_gap_wide_search import sample
from n7.checks import canonical_pattern
rng=random.Random(913840);start=time.time();valid=0;counts={};examples={};failures=[]
base=np.array([[-1504,-547,0],[100,0,0],[129,153,0],[-69,394,0],[-693,400,0]],float)/100
for attempt in range(1500000):
 if rng.random()<.6:
  h,H=10**rng.uniform(-3,2),10**rng.uniform(-3,2);p=np.vstack([base,[0,0,h],[0,0,-H]])
  shear=np.array([rng.uniform(-1,1),rng.uniform(-1,1)])*10**rng.uniform(-2,3);p[:,:2]+=p[:,2,None]*shear;p[:,0]*=10**rng.uniform(-1,1)
 else:p=sample(rng)
 m=measurements(p)
 if m is None:continue
 valid+=1;key=canonical_pattern(m['pattern'])
 if key not in('BBBCC','BBBBC'):continue
 k=3 if key=='BBBCC' else 4;target='F'*k+'C'*(5-k);orig=m['pattern']
 for a in range(5):
  for d in(1,-1):
   pp=''.join(orig[(a+i)%5] if d==1 else orig[(a-i-1)%5].translate(str.maketrans('BF','FB')) for i in range(5))
   if pp==target:labels=[(a+d*i)%5 for i in range(5)]+[5,6];break
  else:continue
  break
 p=p[labels];m=measurements(p);g={s:[m['omega'][s][i+1]+m['ell'][s][i+1]-m['ell'][s][i] for i in range(k-1)]+[m['omega'][s][k]-m['ell'][s][k-1]] for s in(5,6)}
 good=[s for s in(5,6) if min(g[s])>1e-8];name=target+(':ordered' if good else ':no-ordered-fan');counts[name]=counts.get(name,0)+1
 row={'points':p.tolist(),'pattern':target,'gates':g,'good_fans':good,'curvatures':m['curvatures']}
 if name not in examples:examples[name]=row;print('FIRST',attempt,name,g,flush=True)
 if not good and max(min(g[s]) for s in(5,6))<-1e-6:
  failures.append(row)
  if len(failures)>=8:break
 if attempt%100000==0:print(attempt,valid,counts,time.time()-start,flush=True)
 if time.time()-start>150:break
out={'scope':'Floating ordered-run rule search. Counts do not prove a universal statement; failures require exact certification.','attempts':attempt+1,'valid':valid,'counts':counts,'examples':examples,'failures':failures};Path('/private/tmp/n7_run_search.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',attempt+1,valid,counts,len(failures),time.time()-start,flush=True)
