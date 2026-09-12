"""Archived discovery recipe for the obtuse-petal lemma; not a proof."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
from n7.a992 import unfold,penetration
import numpy as np,math,random,json
FACES=((0,3,6),(0,6,5),(0,5,3),(1,3,6),(1,6,5),(1,5,3));CUT=((0,3),(0,5),(0,6),(1,3));rng=random.Random(992319)
best=None
for i in range(52000):
 p=np.zeros((7,3));p[6]=(1,0,0)
 t=rng.uniform(.05,.999);H=math.sqrt(t*(1-t))*rng.uniform(.1,.99999);phi=rng.uniform(.001,math.pi-.001)
 p[0]=(t,H*math.cos(phi),H*math.sin(phi))
 x=1+10**rng.uniform(-2,3);y=(x-1)*H/(1-t)*rng.uniform(.001,.999)
 p[1]=(x,y,0)
 l,m=10**rng.uniform(-5,1),10**rng.uniform(-6,1)
 if l+m<1:beta=rng.uniform(.001,.999999)/(1-l-m)
 else:beta=10**rng.uniform(-3,2)
 p[5]=p[1]+beta*(p[0]-p[1])-beta*l*(p[3]-p[1])-beta*m*(p[6]-p[1])
 n=unfold(p,CUT,FACES,4);scale=max(1,np.ptp(p[[0,1,3,5,6]],axis=0).max());score=penetration(n[0],n[5])/scale
 if best is None or score>best['score']:best={'points':p.tolist(),'score':score,'parameters':[t,H,phi,x,y,l,m,beta],'round':i}
 if score>1e-8:print('FAILED',json.dumps(best),flush=True);break
 if i%10000==0:print(i,best['score'],flush=True)
print('done',json.dumps(best),flush=True);best['scope']='Floating discovery only; no exact signs or universal conclusion.'
best['attempted']=i+1;best['seed']=992319
(ROOT/'results/a992-obtuse-petal-target-search.json').write_text(json.dumps(best,indent=2)+'\n')
