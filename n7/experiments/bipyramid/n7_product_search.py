"""Discover conflicts in a sufficient local product test; floating only."""
import numpy as np,math,json,random,time
from pathlib import Path
from n7_pair_class_search import measurements
from n7_two_gap_wide_search import sample
from n7.checks import canonical_pattern
rng=random.Random(913948);start=time.time();counts={};examples={};failures={};valid=0
base=np.array([[-1504,-547,0],[100,0,0],[129,153,0],[-69,394,0],[-693,400,0],[0,0,1],[0,0,-1]],float)/100
for attempt in range(2000000):
 if rng.random()<.4:
  p=base.copy();p[5,2]*=10**rng.uniform(-1.3,2);p[6,2]*=10**rng.uniform(-1.3,2);p[:5,2]+=[rng.uniform(-.2,.2)*min(p[5,2],-p[6,2]) for _ in range(5)];shear=np.array([rng.uniform(-1,1),rng.uniform(-1,1)])*10**rng.uniform(-2,4);p[:,:2]+=p[:,2,None]*shear;p[:,0]*=10**rng.uniform(-1,1)
 else:p=sample(rng)
 m=measurements(p)
 if m is None:continue
 valid+=1;pattern=m['pattern'];key=canonical_pattern(pattern);bad=[i for i in range(5) if pattern[i]=='B' or pattern[(i-1)%5]=='F']
 if len(bad)<3:continue
 e=np.roll(p[:5],-1,axis=0)-p[:5];ln=np.linalg.norm(e,axis=1);u=p[5]-p[:5];v=p[6]-p[:5];al=np.sum(u*e,axis=1)/ln;be=np.sum(v*e,axis=1)/ln;hp=np.linalg.norm(np.cross(u,e),axis=1)/ln;hq=np.linalg.norm(np.cross(v,e),axis=1)/ln;D=np.sqrt((al-be)**2+(hp+hq)**2);H=np.sum(u*u-v*v,axis=1);T=D*np.roll(D,1);r=H/T;good=[q for q,rr in ((6,r),(5,-r)) if max(rr[bad])<1-1e-8];name=key+(':pass' if good else ':conflict-or-boundary');counts[name]=counts.get(name,0)+1
 row={'points':p.tolist(),'pattern':pattern,'bad_vertices':bad,'signed_product_ratios':r.tolist(),'good_sources':good,'curvatures':m['curvatures']}
 if good and key not in examples:examples[key]=row
 if min(r[bad])<-1-1e-6 and max(r[bad])>1+1e-6 and key not in failures:
  failures[key]=row;print('CONFLICT',key,r[bad],flush=True)
  Path('/private/tmp/n7_product_search.json').write_text(json.dumps({'scope':'Floating discovery; failed sufficient tests do not imply overlap.','attempts':attempt+1,'valid':valid,'case_counts':counts,'examples':examples,'conflicts':failures},indent=2)+'\n')
 if len(failures)==8 or time.time()-start>300:break
out={'scope':'Floating discovery; failed sufficient tests do not imply overlap.','attempts':attempt+1,'valid':valid,'case_counts':counts,'examples':examples,'conflicts':failures};Path('/private/tmp/n7_product_search.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',attempt,valid,counts,len(failures),time.time()-start,flush=True)
