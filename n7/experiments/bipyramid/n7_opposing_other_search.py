"""Search for opposing long receivers in other patterns. Floating discovery only."""
import numpy as np,math,json,time
from scipy.optimize import differential_evolution,minimize
from pathlib import Path
from n7.bipyramid_morph import FACES
PI=math.pi;FF=np.array(FACES)
base=np.array([[-75,4,0],[-60,-7,0],[12,-10,0],[54,-7,0],[81,0,0]],float)/20
base[:,:2]-=base[:,:2].mean(axis=0)

def geometry(x):
 h,H=np.exp(x[:2]);weights=np.exp(np.r_[x[4:],0]);c=weights@base/weights.sum();s=x[2:4]
 return np.vstack([base,[*(c[:2]+h*s),h],[*(c[:2]-H*s),-H]])
def metrics(p):
 t=p[FF];ed=np.stack([t[:,1]-t[:,0],t[:,2]-t[:,1],t[:,0]-t[:,2]],axis=1)
 aa=np.arctan2(np.linalg.norm(np.cross(ed,-np.roll(ed,1,axis=1)),axis=2),np.sum(ed*(-np.roll(ed,1,axis=1)),axis=2))
 return aa,aa[:5,1:]+aa[5:,1:]
def evaluate(x,pattern,details=False):
 p=geometry(x);aa,cs=metrics(p);bad=[i for i,c in enumerate(pattern) if c!='C'];vals=[];margins=[]
 for i in range(5):
  for col in(0,1):vals.append((cs[i,col]-PI) if pattern[i]==('B' if col==0 else 'F') else PI-cs[i,col])
 for fan,i in zip((5,6),bad):
  col=0 if pattern[i]=='B' else 1;v=i if col==0 else(i+1)%5;recv=(i+(-1 if col==0 else 1))%5;eta=cs[i,col]-PI
  r=np.linalg.norm(p[fan]-p[v]);s=np.linalg.norm(p[11-fan]-p[v]);ell=math.atan2(s*math.sin(eta),r+s*math.cos(eta));margins.append(ell-aa[(fan-5)*5+recv,0])
 vals+=margins
 score=min(vals)
 if details:return {'pattern':pattern,'score':score,'long_margins':margins,'points':p.tolist(),'triangle_angles':aa.tolist(),'parameters':list(map(float,x))}
 return -score
rows=[];start=time.time()
for pattern in('FCCBC','FCFCC','FCCCB'):
 for seed in range(4):
  opt=differential_evolution(lambda x:evaluate(x,pattern),[(-9,3),(-9,3),(-150,150),(-150,150)]+[(-9,9)]*4,popsize=9,maxiter=250,tol=1e-7,seed=913700+seed,polish=False,workers=1)
  local=minimize(lambda x:evaluate(x,pattern),opt.x,method='COBYLA',options={'maxiter':2500,'rhobeg':.3,'tol':1e-8})
  x=local.x if local.fun<opt.fun else opt.x;r=evaluate(x,pattern,True);rows.append(r);print(pattern,seed,'minimum margin',r['score'],'longs',r['long_margins'],'seconds',time.time()-start,flush=True)
  Path('/private/tmp/n7_opposing_other_search.json').write_text(json.dumps({'scope':'Floating numerical discovery, not a proof of realizability, impossibility, or unfolding.','results':rows},indent=2)+'\n')
  if r['score']>1e-4:break
