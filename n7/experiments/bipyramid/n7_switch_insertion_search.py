"""Find a simple tilted-axis insertion with a changing maximal slit. Floating discovery."""
import numpy as np,random,math,json
from pathlib import Path
from n7_pair_class_search import measurements
rng=random.Random(914031)
for attempt in range(100000):
 ang=sorted(rng.uniform(0,2*math.pi) for _ in range(5));ring=np.array([[round(100*math.cos(a)),round(100*math.sin(a)),0] for a in ang],float);ring[:,0]*=rng.choice([1,2,3,5]);q=np.array([rng.randint(-50,50),rng.randint(-50,50),rng.randint(10,200)],float);p=np.array([rng.randint(-120,120),rng.randint(-120,120),-rng.randint(1,120)],float);pts=np.vstack([ring,p,q]);m=measurements(pts)
 if m is None:continue
 if min((ring-q)@(p-q))<0:continue
 c=(q*(-p[2])+p*q[2])/(q[2]-p[2]);d0=np.linalg.norm(ring-q,axis=1)+np.linalg.norm(ring-c,axis=1);d1=np.linalg.norm(ring-q,axis=1)+np.linalg.norm(ring-p,axis=1);i,j=int(np.argmax(d0)),int(np.argmax(d1))
 if i==j or min(np.sort(d0)[-1]-np.sort(d0)[-2],np.sort(d1)[-1]-np.sort(d1)[-2])<.01:continue
 row={'points':pts.astype(int).tolist(),'source':6,'start_slit':i,'end_slit':j,'pattern':m['pattern'],'curvatures':m['curvatures'],'start_point':c.tolist()};Path('/private/tmp/n7_switch_insertion_search.json').write_text(json.dumps(row,indent=2)+'\n');print('FOUND',attempt,row,flush=True);break
