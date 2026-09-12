"""Targeted finite searches for a conjecture, not universal evidence."""
import numpy as np,json,time
from pathlib import Path
from scipy.optimize import differential_evolution,minimize
import n7_opposing_other_search as m
rng=np.random.default_rng(913712);results=[];start=time.time()
for run in range(50):
 angles=np.sort(rng.uniform(0,2*np.pi,5));m.base=np.c_[np.cos(angles),np.sin(angles),np.zeros(5)];m.base[:,0]*=10**rng.uniform(0,2);m.base[:,:2]-=m.base[:,:2].mean(axis=0)
 pattern='FCFCC' if run%2==0 else 'FCCCB'
 opt=differential_evolution(lambda x:m.evaluate(x,pattern),[(-9,3),(-9,3),(-250,250),(-250,250)]+[(-8,8)]*4,popsize=7,maxiter=180,tol=1e-7,seed=913720+run,polish=False)
 local=minimize(lambda x:m.evaluate(x,pattern),opt.x,method='COBYLA',options={'maxiter':1400,'rhobeg':.4,'tol':1e-8})
 x=local.x if local.fun<opt.fun else opt.x;r=m.evaluate(x,pattern,True);r['ring']=m.base.tolist();results.append(r)
 print(run,pattern,r['score'],'seconds',time.time()-start,flush=True)
 Path('/private/tmp/n7_opposing_many_rings.json').write_text(json.dumps({'scope':'Finite floating searches only. No impossibility or realization is certified.','results':results},indent=2)+'\n')
 if r['score']>1e-5:break
