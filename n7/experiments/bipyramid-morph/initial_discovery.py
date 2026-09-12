"""Archived floating discovery; not proof evidence. Run from the worktree root."""
import json,math,random,itertools
import numpy as np
from n7.a992 import unfold,penetration
rng=random.Random(913507)
def faces(m=5):return [(pole,i,(i+1)%m) for pole in (m,m+1) for i in range(m)]
F=faces()
def valid(p,fs=F):
 for f in fs:
  a,b,c=p[list(f)];n=np.cross(b-a,c-a);vals=[float((p[j]-a)@n) for j in range(len(p)) if j not in f]
  if not(min(vals)>1e-9 or max(vals)<-1e-9):return False
 return True
def net(p,pole,k):return unfold(p,[(pole,i) for i in range(5)]+[(11-pole,k)],F,5)
def score(n):
 vals=[(penetration(n[i],n[j]),i,j) for i,j in itertools.combinations(range(10),2)]
 return max(vals)
def kappa(p):
 k=[2*math.pi]*7
 for f in F:
  for v in f:
   a,b=[p[j]-p[v] for j in f if j!=v];k[v]-=math.atan2(np.linalg.norm(np.cross(a,b)),a@b)
 return k
found=None;count=0
for it in range(3500):
 ang=sorted(rng.uniform(0,2*math.pi) for _ in range(5))
 ring=np.array([[math.cos(a),math.sin(a),0] for a in ang])
 if max(ang[i+1]-ang[i] for i in range(4))>=math.pi or ang[0]+2*math.pi-ang[-1]>=math.pi:continue
 weights=np.array([rng.expovariate(1) for _ in range(5)]);v=weights@ring/weights.sum();weights=np.array([rng.expovariate(1) for _ in range(5)]);w=weights@ring/weights.sum();v[2]=10**rng.uniform(-2,1);w[2]=-10**rng.uniform(-2,1)
 p=np.vstack([ring,v,w]);p[:,0]*=10**rng.uniform(-.7,.7)
 if not valid(p):continue
 count+=1
 for pole in (5,6):
  for slit in range(5):
   nn=net(p,pole,slit);s,i,j=score(nn)
   if s<1e-5:continue
   for deleted in range(5):
    if deleted==slit:continue
    p0=p.copy();p0[deleted]=(p[(deleted-1)%5]+p[(deleted+1)%5])/2
    near=p0+1e-4*(p-p0)
    if not valid(near):continue
    n0=net(p0,pole,slit);s0,_,_=score(n0)
    if s0>1e-9:continue
    found={'scope':'Numerical discovery only.','round':it,'points':p.tolist(),'deleted':deleted,'source':pole,'slit':slit,'endpoint_pair':[i,j],'endpoint_penetration':s,'start_max_penetration':s0,'curvatures':kappa(p)};break
   if found:break
  if found:break
 if found:break
 if it%100==0:print(it,count,flush=True)
print(json.dumps(found),flush=True)
if found:open('/private/tmp/n7_morph_search.json','w').write(json.dumps(found,indent=2)+'\n')
