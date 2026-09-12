"""Discovery only: can pole choice always satisfy the proved corrected gate?"""
import json,math,random,time
from pathlib import Path
import numpy as np
from n7_pair_class_search import measurements,normalized,pair_class,sample,canonical_pattern
rng=random.Random(913619);base=np.array([[-75,4,0],[-60,-7,0],[12,-10,0],[54,-7,0],[81,0,0],[18,-8,1],[-20,-3,-5]],float)/10
start=time.time();valid=relevant=0;counts={};misses=[];best=None
for attempt in range(250000):
 if rng.random()<.65:
  p=base.copy();p[:5,0]+=np.array([rng.gauss(0,1.2) for _ in range(5)]);p[:5,1]+=np.array([rng.gauss(0,.25) for _ in range(5)]);
  if rng.random()<.6:p[:5,2]+=np.array([rng.gauss(0,.04) for _ in range(5)])
  for s in(5,6):p[s,:2]+=np.array([rng.gauss(0,2),rng.gauss(0,.25)]);p[s,2]*=10**rng.uniform(-1.7,1.2)
  p[:,0]*=10**rng.uniform(-1.7,1.2)
 else:p=sample(rng)
 m=measurements(p)
 if m is None:continue
 valid+=1
 if canonical_pattern(m['pattern'])!='BCFCC' or max(m['curvatures'][5:])>=math.pi or min(m['curvatures'])<1e-7:continue
 p,m=normalized(p,m);relevant+=1;options=[]
 for fan in(5,6):
  e=m['ell'][fan];w=m['omega'][fan]
  if e[0]+e[3]>=w[1]+w[2]-1e-8:continue
  long=0 if e[0]>w[1]+1e-8 else 3 if e[3]>w[2]+1e-8 else None
  if long is None:options.append({'fan':fan,'branch':'both-short','proved':True});continue
  c=pair_class(p,m,fan,long);i=0 if long==0 else 1;out=(i+4)%5;pre=(out-1)%5;a=np.array(m['angles']);q=11-fan;fb=(fan-5)*5;sb=(q-5)*5
  A=a[sb+pre,2]+a[sb+out,1];B=a[fb+pre,2]+a[fb+out,1];H=m['curvatures'][q]-m['curvatures'][fan]+B-A
  passed=c['branch']=='base cones' or H>=1e-8
  options.append({'fan':fan,'long_patch':long,'pair_case':c,'H':H,'proved':bool(passed)})
 if options:
  success=any(row['proved'] for row in options);key='some eligible gate' if success else 'no eligible corrected gate';counts[key]=counts.get(key,0)+1
  if not success:
   row={'points':p.tolist(),**m,'options':options};misses.append(row);print('MISS',attempt,[r['H'] for r in options],flush=True)
   if len(misses)>=5:break
 if attempt%30000==0:print(attempt,valid,relevant,counts,flush=True)
 if time.time()-start>540:break
Path('/private/tmp/n7_chain_gate_cover.json').write_text(json.dumps({'scope':'Floating search only. Gate counts are not proof coverage of all shapes.','seed':913619,'attempts':attempt+1,'valid':valid,'relevant':relevant,'counts':counts,'misses':misses},indent=2)+'\n');print('DONE',attempt+1,valid,relevant,counts,flush=True)
