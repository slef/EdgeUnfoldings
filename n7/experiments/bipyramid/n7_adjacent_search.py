"""Floating discovery of the adjacent-run rule branches; not a proof."""
import json,time,random,math
from pathlib import Path
import numpy as np
from n7_pair_class_search import measurements
from n7_two_gap_wide_search import sample
from n7.checks import canonical_pattern
rng=random.Random(913815);start=time.time();rows={};counts={};valid=0
for attempt in range(400000):
 p=sample(rng);m=measurements(p)
 if m is None:continue
 valid+=1
 if canonical_pattern(m['pattern'])!='BBCCC':continue
 original=m['pattern']
 for a in range(5):
  for d in(1,-1):
   pp=''.join(original[(a+i)%5] if d==1 else original[(a-i-1)%5].translate(str.maketrans('BF','FB')) for i in range(5))
   if pp=='FFCCC':labels=[(a+d*i)%5 for i in range(5)]+[5,6];break
  else:continue
  break
 p=p[labels];m=measurements(p)
 A={s:m['ell'][s][0]-m['omega'][s][1]-m['ell'][s][1] for s in(5,6)}
 B={s:m['ell'][s][1]-m['omega'][s][2] for s in(5,6)}
 q=next(s for s in(5,6) if B[s]<-1e-8) if min(B.values())<-1e-8 else None
 if q is None:continue
 f=q;branch='nested and short'
 if A[q]>1e-8:
  if B[11-q]<-1e-8:f=11-q;branch='switch to nested and short'
  elif B[11-q]>1e-8:branch='outer pocket and radial cover'
  else:continue
 elif A[q]>=-1e-8:continue
 counts[branch]=counts.get(branch,0)+1
 if branch not in rows:
  row={'points':p.tolist(),'pattern':m['pattern'],'fan':f,'A':A,'B':B,'branch':branch};rows[branch]=row;print('FOUND',attempt,branch,A,B,flush=True)
 if len(rows)==3:break
 if attempt%50000==0:print(attempt,valid,counts,time.time()-start,flush=True)
 if time.time()-start>100:break
out={'scope':'Floating search only. Exact coordinates must be separately certified; the universal proof does not use counts.','attempts':attempt+1,'valid':valid,'counts':counts,'examples':rows};Path('/private/tmp/n7_adjacent_search.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',attempt+1,valid,counts,time.time()-start,flush=True)
