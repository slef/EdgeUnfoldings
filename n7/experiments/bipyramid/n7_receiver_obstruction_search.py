"""Floating search for the remaining two-receiver cone obstruction."""
import math,json,random,time
from pathlib import Path
import numpy as np
from n7_two_gap_wide_search import sample,geometry,measurements,canonical_pattern,cut,worst
rng=random.Random(913614);start=time.time();best=None;hits=[];valid=0;relevant=0
for attempt in range(120000):
 p=sample(rng)
 if not geometry(p):continue
 valid+=1;m=measurements(p);pattern=m['pattern'];key=canonical_pattern(pattern)
 if key not in('BCBCC','BCFCC','BFCCC'):continue
 if min(m['curvatures'])<1e-6:continue
 relevant+=1;bad=[i for i,c in enumerate(pattern) if c!='C'];receiver={i:(i+(1 if pattern[i]=='F' else -1))%5 for i in bad};long={s:[i for i in bad if m['ell'][s][i]>m['omega'][s][receiver[i]]] for s in(5,6)}
 if any(len(long[s])!=1 for s in(5,6)) or long[5][0]==long[6][0]:continue
 margins={s:m['ell'][s][long[s][0]]-m['omega'][s][receiver[long[s][0]]]-m['curvatures'][s] for s in(5,6)};score=min(margins.values())
 row={'points':p.tolist(),**m,'long':long,'receivers':receiver,'gap_deficits':margins,'minimum_deficit':score}
 if best is None or score>best['minimum_deficit']:best=row
 if score>1e-6:
  row['net_penetrations']={f'{s}:{k}':worst(p,cut(s,k)) for s in(5,6) for k in range(5)};hits.append(row);print('FOUND',attempt,key,score,flush=True)
  if len(hits)>=3:break
 if attempt%10000==0:print(attempt,valid,relevant, 'best',best['minimum_deficit'] if best else None,flush=True)
 if time.time()-start>600:break
Path('/private/tmp/n7_receiver_obstruction_search.json').write_text(json.dumps({'scope':'Numerical discovery only, not proof of an example or universal implication.','seed':913614,'attempts':attempt+1,'valid':valid,'relevant':relevant,'hits':hits,'best':best},indent=2)+'\n');print('done',attempt+1,valid,relevant,len(hits),best['minimum_deficit'] if best else None,flush=True)
