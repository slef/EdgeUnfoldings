"""Constrained floating search for failure of the last wider Case A bound."""
import json,math,time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
from n7_pair_class_search import FF,MASK
PI=math.pi
D=json.load(open('/private/tmp/n7_pair_class_search.json'))
E=json.load(open('/private/tmp/n7_chain_search.json'))
seeds=[r for r in E['examples'].values() if r['long_patch'] is not None]+[r for r in D['examples'].values() if r['long_patch'] is not None]

def normalized(row):
 p=np.array(row['points']);fan=row['fan'];source=11-fan
 ring=list(range(5)) if row['long_patch']==0 else list(reversed(range(5)))
 p=p[ring+[fan,source]];p-=p[5];L=np.linalg.norm(p[6]);z=p[6]/L;x=np.cross(z,[1,0,0] if abs(z[0])<.8 else [0,1,0]);x/=np.linalg.norm(x);y=np.cross(z,x);return p@np.array([x,y,z]).T/L

def terms(x):
 p=np.vstack([np.asarray(x).reshape(5,3),[0,0,0],[0,0,1]]);t=p[FF];ed=np.stack([t[:,1]-t[:,0],t[:,2]-t[:,1],t[:,0]-t[:,2]],axis=1);ang=np.arctan2(np.linalg.norm(np.cross(ed,-np.roll(ed,1,axis=1)),axis=2),np.sum(ed*(-np.roll(ed,1,axis=1)),axis=2));k=np.full(7,2*PI)
 for j in range(3):np.add.at(k,FF[:,j],-ang[:,j])
 patch=ang[:5,1:]+ang[5:,1:];ell=[]
 for i,j,v in[(0,1,1),(3,0,3)]:
  rho=patch[i,j]-PI;r=np.linalg.norm(p[5]-p[v]);s=np.linalg.norm(p[6]-p[v]);ell.append(math.atan2(s*math.sin(rho),r+s*math.cos(rho)))
 theta=PI-ang[6,0]+k[1]+k[2];half=(PI+theta)/2;objective=ang[7,0]-half
 n=np.cross(t[:,1]-t[:,0],t[:,2]-t[:,0]);vv=np.sum((p[None,:,:]-t[:,0,None,:])*n[:,None,:],axis=2);vol=np.array([row[mask] for row,mask in zip(vv,MASK)])
 return p,ang,k,patch,ell,theta,objective,vol,n

def run(seed,index):
 p=normalized(seed);x0=p[:5].ravel();v=terms(x0);sgn=np.sign(v[7][:,0]);eps=1e-7
 def cons(x):
  pp,a,k,patch,e,theta,obj,vol,n=terms(x)
  supports=(vol*sgn[:,None]/np.maximum(np.linalg.norm(n,axis=1)[:,None],1e-14)).ravel()
  s=np.ones((5,2));s[0,1]=-1;s[3,0]=-1
  return np.r_[supports-eps,(s*(PI-patch)).ravel()-eps,k-eps,PI-k[5:]-eps,theta-eps,PI-theta-eps,e[0]-a[1,0]-eps,a[1,0]+a[2,0]-sum(e)-eps]
 result=minimize(lambda x:-terms(x)[6],x0,method='COBYLA',bounds=[(-30,30)]*15,constraints=[{'type':'ineq','fun':cons}],options={'maxiter':12000,'rhobeg':0.01,'tol':1e-9,'catol':1e-8})
 vals=terms(result.x);row={'points':vals[0].tolist(),'objective_rho_minus_half':vals[6],'minimum_constraint':float(cons(result.x).min()),'theta':vals[5],'source_angles':vals[1][5:8,0].tolist(),'curvatures':vals[2].tolist(),'optimizer_success':bool(result.success),'optimizer_message':str(result.message),'iterations':int(result.nfev)}
 print(index,row['objective_rho_minus_half'],row['minimum_constraint'],row['optimizer_message'],flush=True);return row
out=[];start=time.time()
for i,seed in enumerate(seeds):
 try:out.append(run(seed,i))
 except Exception as e:print('ERROR',i,str(e),flush=True)
 Path('/private/tmp/n7_chain_cobyla.json').write_text(json.dumps({'scope':'Floating constrained optimization only. Neither objective signs nor feasibility are exact proofs.','results':out},indent=2)+'\n')
 if time.time()-start>540:break
print('DONE',len(out),time.time()-start,flush=True)
