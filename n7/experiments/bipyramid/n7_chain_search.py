"""Discovery only: stress the two-metric-pair reduction and its auxiliary bridge."""
import json,random,time,math
from pathlib import Path
import numpy as np
from n7_two_gap_wide_search import sample,geometry,measurements,canonical_pattern,angle,cut
from n7.a992 import unfold,penetration
from n7.bipyramid_morph import FACES
rng=random.Random(913617);start=time.time();base=np.array([[-75,4,0],[-60,-7,0],[12,-10,0],[54,-7,0],[81,0,0],[18,-8,1],[-20,-3,-5]],float)/10

def normalize(p,m):
 for d in(1,-1):
  for a in range(5):
   labels=[(a+d*i)%5 for i in range(5)]+[5,6]
   pattern=''.join(m['pattern'][(a+i)%5] if d==1 else m['pattern'][(a-i-1)%5].translate(str.maketrans('BF','FB')) for i in range(5))
   if pattern=='FCCBC':
    pp=p[labels];return pp,measurements(pp)
 raise ValueError('Unrecognized chain')
def aux(p,fan,long):
 removed=4 if long==0 else 0;ends=(3,0) if long==0 else (4,1)
 fs=tuple(f for f in FACES if removed not in f)+tuple((s,*ends) for s in(5,6));active=[i for i in range(7) if i!=removed]
 for f in fs:
  a,b,c=p[list(f)];n=np.cross(b-a,c-a);vv=np.array([(p[v]-a)@n for v in active if v not in f])
  if not(vv.min()>1e-10 or vv.max()<-1e-10):return 'other-reduced-graph'
 k={v:2*math.pi for v in active}
 for f in fs:
  for v in f:k[v]-=angle(*[p[j]-p[v] for j in f if j!=v])
 if k[11-fan]<k[fan]:return 'wrong-auxiliary-pole'
 if max(ends,key=lambda v:k[v])!=max([v for v in active if v<5],key=lambda v:k[v]):return 'interior-auxiliary-maximum'
 return 'bridge'
counts={};examples={};valid=relevant=0;failures=[];both_fail=[];best=None
for attempt in range(200000):
 if rng.random()<.65:
  p=base.copy();p[:5,0]+=np.array([rng.gauss(0,.8) for _ in range(5)]);p[:5,1]+=np.array([rng.gauss(0,.1) for _ in range(5)]);
  if rng.random()<.5:p[:5,2]+=np.array([rng.gauss(0,.008) for _ in range(5)])
  for s in(5,6):p[s,:2]+=np.array([rng.gauss(0,1.2),rng.gauss(0,.12)]);p[s,2]*=10**rng.uniform(-1,1)
  p[:,0]*=10**rng.uniform(-1,1)
 else:p=sample(rng)
 if not geometry(p):continue
 valid+=1;m=measurements(p)
 if canonical_pattern(m['pattern'])!='BCFCC':continue
 p,m=normalize(p,m);relevant+=1;choices=[]
 for fan in(5,6):
  e=m['ell'][fan];a=m['omega'][fan]
  if e[0]+e[3]>=a[1]+a[2]-1e-8:continue
  long=0 if e[0]>a[1]+1e-8 else 3 if e[3]>a[2]+1e-8 else None
  branch='both-short' if long is None else aux(p,fan,long)
  counts[branch]=counts.get(branch,0)+1
  row={'points':p.tolist(),**m,'fan':fan,'long_patch':long,'branch':branch}
  if branch not in examples:examples[branch]=row
  if long is not None:
   net=unfold(p,cut(fan,0),FACES,0);pet=(6-fan)*5+long;rec=2 if long==0 else 1
   score=max(penetration(net[pet],net[b+rec]) for b in(0,5))/np.ptp(p,axis=0).max()
  else:score=-1.
  row['normalized_residual_penetration']=score;choices.append(row)
  if best is None or score>best['normalized_residual_penetration']:best=row
  if score>1e-7:
   failures.append(row);print('candidate failure',attempt,fan,branch,score,flush=True)
 if choices and all(row['normalized_residual_penetration']>1e-7 for row in choices):both_fail.append(choices)
 if len(both_fail)>=3 or len(failures)>=8:break
 if attempt%10000==0:print(attempt,valid,relevant,counts,'failures',len(failures),flush=True)
 if time.time()-start>540:break
out={'scope':'Floating discovery only, not proof. Residual scores are checked only after the written chain selection inequality.','seed':913617,'attempts':attempt+1,'valid':valid,'relevant':relevant,'counts':counts,'examples':examples,'failures':failures,'all_eligible_failed':both_fail,'best':best}
Path('/private/tmp/n7_chain_search.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',attempt+1,valid,relevant,counts,len(failures),len(both_fail),flush=True)
