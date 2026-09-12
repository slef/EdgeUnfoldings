"""Floating search for the nonnested/other-pole-long adjacent branch."""
import numpy as np,math,json,time
from pathlib import Path
from scipy.optimize import differential_evolution,minimize
from n7.bipyramid_morph import FACES
FF=np.array(FACES);PI=math.pi
base=np.array([[-75,4,0],[-60,-7,0],[12,-10,0],[54,-7,0],[81,0,0]],float)/20;base[:,:2]-=base[:,:2].mean(axis=0)
def geometry(x):
 h,H=np.exp(x[:2]);weights=np.exp(np.r_[x[4:],0]);c=weights@base/weights.sum();s=x[2:4]
 return np.vstack([base,[*(c[:2]+h*s),h],[*(c[:2]-H*s),-H]])
def metric(x,details=False):
 p=geometry(x);t=p[FF];ed=np.stack([t[:,1]-t[:,0],t[:,2]-t[:,1],t[:,0]-t[:,2]],axis=1);aa=np.arctan2(np.linalg.norm(np.cross(ed,-np.roll(ed,1,axis=1)),axis=2),np.sum(ed*(-np.roll(ed,1,axis=1)),axis=2));cs=aa[:5,1:]+aa[5:,1:];vals=[];ell={}
 for i in range(5):
  for col in(0,1):vals.append(cs[i,col]-PI if i in(0,1) and col==1 else PI-cs[i,col])
 for fan in(5,6):
  for i in(0,1):
   a=i+1;rho=cs[i,1]-PI;r=np.linalg.norm(p[fan]-p[a]);s=np.linalg.norm(p[11-fan]-p[a]);ell[fan,i]=math.atan2(s*math.sin(rho),r+s*math.cos(rho))
 A={s:ell[s,0]-aa[(s-5)*5+1,0]-ell[s,1] for s in(5,6)};B={s:ell[s,1]-aa[(s-5)*5+2,0] for s in(5,6)}
 vals+=[A[6],B[5]];score=min(vals)
 if details:return {'score':score,'points':p.tolist(),'A':A,'B':B,'parameters':list(map(float,x))}
 return -score
rows=[];start=time.time();rng=np.random.default_rng(913830)
for run in range(30):
 if run:
  angles=np.sort(rng.uniform(0,2*np.pi,5));base=np.c_[np.cos(angles),np.sin(angles),np.zeros(5)];base[:,0]*=10**rng.uniform(0,2);base[:,:2]-=base[:,:2].mean(axis=0)
 opt=differential_evolution(metric,[(-9,3),(-9,3),(-200,200),(-200,200)]+[(-8,8)]*4,popsize=8,maxiter=200,tol=1e-7,seed=913831+run,polish=False)
 local=minimize(metric,opt.x,method='COBYLA',options={'maxiter':1800,'rhobeg':.3,'tol':1e-8});x=local.x if local.fun<opt.fun else opt.x;r=metric(x,True);rows.append(r);print(run,r['score'],r['A'],r['B'],time.time()-start,flush=True)
 Path('/private/tmp/n7_adjacent_pocket_search.json').write_text(json.dumps({'scope':'Floating discovery only; exact certification is required separately.','results':rows},indent=2)+'\n')
 if r['score']>1e-5:break
