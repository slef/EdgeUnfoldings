"""Numerical attempt to refute the single-block conjecture through a six-vertex donor."""
import numpy as np,math,random,json,time
from pathlib import Path
rng=random.Random(914115);PI=math.pi;FF=np.array([(s,i,(i+1)%4) for s in(4,5) for i in range(4)]);mask=np.array([[j not in f for j in range(6)]for f in FF]);start=time.time();valid=relevant=0;conflicts=[]
for attempt in range(2000000):
 angles=sorted(rng.uniform(0,2*PI)for _ in range(4))
 if rng.random()<.5:
  rad=[10**rng.uniform(-2,2)for _ in range(4)];ring=np.array([[r*math.cos(a),r*math.sin(a),rng.uniform(-10,10)]for r,a in zip(rad,angles)]);p=np.vstack([ring,[0,0,0],[0,0,1]])
 else:
  ring=np.array([[math.cos(a),math.sin(a),0]for a in angles]);ring[:,0]*=10**rng.uniform(-2,2);w=np.array([rng.expovariate(1)for _ in range(4)]);c=w@ring/w.sum();h,H=10**rng.uniform(-3,1),10**rng.uniform(-3,1);p=np.vstack([ring,[*c[:2],h],[*c[:2],-H]])
 shear=np.array([rng.uniform(-1,1),rng.uniform(-1,1)])*10**rng.uniform(-2,3);p[:,:2]+=p[:,2,None]*shear;p[:,0]*=10**rng.uniform(-1,1)
 t=p[FF];norm=np.cross(t[:,1]-t[:,0],t[:,2]-t[:,0]);vals=np.sum((p[None,:,:]-t[:,0,None,:])*norm[:,None,:],axis=2);v=np.array([a[b]for a,b in zip(vals,mask)]);tol=1e-10*np.ptp(p,axis=0).max()*np.linalg.norm(norm,axis=1)
 if not np.all((v.min(axis=1)>tol)|(v.max(axis=1)<-tol)):continue
 valid+=1;ed=np.stack([t[:,1]-t[:,0],t[:,2]-t[:,1],t[:,0]-t[:,2]],axis=1);aa=np.arctan2(np.linalg.norm(np.cross(ed,-np.roll(ed,1,axis=1)),axis=2),np.sum(ed*(-np.roll(ed,1,axis=1)),axis=2));cs=aa[:4,1:]+aa[4:,1:];pat=''.join('B'if a>PI else'F'if b>PI else'C'for a,b in cs)
 if pat.count('C')!=1:continue
 relevant+=1;e=np.roll(p[:4],-1,axis=0)-p[:4];ln=np.linalg.norm(e,axis=1);u=p[4]-p[:4];v=p[5]-p[:4];al=np.sum(u*e,axis=1)/ln;be=np.sum(v*e,axis=1)/ln;hp=np.linalg.norm(np.cross(u,e),axis=1)/ln;hq=np.linalg.norm(np.cross(v,e),axis=1)/ln;D=np.sqrt((al-be)**2+(hp+hq)**2);H=np.sum(u*u-v*v,axis=1);r=H/(D*np.roll(D,1));bad=[i for i in range(4)if pat[i]=='B'or pat[(i-1)%4]=='F']
 if min(r[bad])<-1-1e-6 and max(r[bad])>1+1e-6:
  conflicts.append({'points':p.tolist(),'pattern':pat,'ratios':r.tolist()});print('CONFLICT',pat,r,flush=True);break
 if time.time()-start>180:break
Path('/private/tmp/n6_three_product_search.json').write_text(json.dumps({'scope':'Floating discovery only; no conclusion from no conflict.','attempts':attempt+1,'numerically_valid':valid,'three_bad':relevant,'conflicts':conflicts},indent=2)+'\n');print('DONE',attempt,valid,relevant,len(conflicts),time.time()-start,flush=True)
