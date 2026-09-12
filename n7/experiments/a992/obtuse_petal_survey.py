"""Archived discovery recipe for the obtuse-petal lemma; not a proof."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
from n7.a992 import unfold,penetration
import numpy as np,math,random,json
FACES=((0,3,6),(0,6,5),(0,5,3),(1,3,6),(1,6,5),(1,5,3))
CUT=((0,3),(0,5),(0,6),(1,3))
rng=random.Random(995713);best=None
for i in range(14000):
 p=np.zeros((7,3));p[6]=(1,0,0);p[5]=(rng.uniform(-3,4),10**rng.uniform(-1,1),0)
 x=rng.uniform(.001,.999);radius=math.sqrt(x-x*x)
 phi=rng.uniform(.001,math.pi-.001);rr=radius*rng.uniform(.01,.999)
 p[0]=(x,rr*math.cos(phi),rr*math.sin(phi))
 a,b,c=[rng.expovariate(1) for _ in range(3)];C=(b*p[6]+c*p[5])/(a+b+c)
 ratio=10**rng.uniform(-3,3);p[1]=C+ratio*(C-p[0])
 n=unfold(p,CUT,FACES,4);scale=max(1,np.ptp(p[[0,1,3,5,6]],axis=0).max());score=penetration(n[0],n[5])/scale
 if best is None or score>best['score']:
  best={'points':p.tolist(),'score':score,'round':i}
 if score>1e-7:print('FAIL',json.dumps(best),flush=True);break
 if i%2000==0:print(i,best['score'],flush=True)
print('done',json.dumps(best),flush=True)
best['scope']='Floating discovery only; no exact signs or universal conclusion.'
best['attempted']=i+1;best['seed']=995713
(ROOT/'results/a992-obtuse-petal-survey.json').write_text(json.dumps(best,indent=2)+'\n')
