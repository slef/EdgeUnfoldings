import json,random,time,math,itertools
from pathlib import Path
import numpy as np
from n7_pair_class_search import sample,measurements
from n7_star_patch_search import data
from n7.a992 import unfold,penetration
from n7.bipyramid_morph import FACES,cut_at
rng=random.Random(913621);start=time.time();valid=0;high=0;counts={};fail=[];special=[]
for attempt in range(200000):
 p=sample(rng);m=measurements(p)
 if m is None or min(m['curvatures'])<1e-7:continue
 valid+=1;fans=[f for f in(5,6) if m['curvatures'][f]>math.pi+1e-7]
 if not fans:continue
 high+=1;d=data(p,m);k=d['patch'];bad=5-m['pattern'].count('C');counts[str(bad)]=counts.get(str(bad),0)+1
 for fan in fans:
  h=min(d['halves'][fan],key=lambda h:h['beta']);net=unfold(p,cut_at(11-fan,h['slit']),FACES,0)
  pairs=[(a,b) for a,b in itertools.combinations(range(10),2) if {a,b}&{k,k+5}]
  worst=max((penetration(net[a],net[b]),a,b) for a,b in pairs);score=worst[0]/np.ptp(p,axis=0).max()
  if score>1e-7:fail.append({'points':p.tolist(),**m,'shortest_patch':d,'fan':fan,'choice':h,'score':score,'pair':worst[1:]});break
  if not any(x['radial'] for x in d['halves'][fan]) and len(special)<5:special.append({'points':p.tolist(),**m,'shortest_patch':d,'fan':fan,'choice':h})
 if fail:break
 if high%1000==0:print(attempt,valid,high,counts,'special',len(special),flush=True)
 if time.time()-start>210:break
out={'scope':'Floating stress check of a separately written theorem, not a proof or exact certificate.','seed':913621,'attempts':attempt+1,'valid':valid,'high_pole_shapes':high,'bad_patch_counts':counts,'failures':fail,'acute_ring_corner_examples':special}
Path('/private/tmp/n7_star_high_stress.json').write_text(json.dumps(out,indent=2,default=lambda x:x.item())+'\n');print('DONE',attempt+1,valid,high,counts,'fail',len(fail),'special',len(special),flush=True)
