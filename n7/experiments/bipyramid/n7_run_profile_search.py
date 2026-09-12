"""Nonplanar search in a linear convexity domain; all numerical, not a proof."""
import numpy as np,math,json,time
from pathlib import Path
from scipy.optimize import minimize,LinearConstraint,Bounds
from n7.bipyramid_morph import FACES
FF=np.array(FACES);PI=math.pi

def profile(points):
 p=np.array(points,float);axis=p[6]-p[5];D=np.linalg.norm(axis);z=axis/D;u=p[:5]-p[5];rad=u-(u@z)[:,None]*z;x=rad[0]/np.linalg.norm(rad[0]);y=np.cross(z,x)
 if rad[1]@y<0:y=-y
 theta=np.unwrap(np.arctan2(rad@y,rad@x));r=np.linalg.norm(rad,axis=1);return theta,np.r_[(u@z)/r,D/r]
def domain(theta):
 C=[]
 for i in range(5):
  j=(i+1)%5
  for k in range(5):
   if k in(i,j):continue
   row=np.zeros(5);row[i]=np.sin(theta[k]-theta[j]);row[j]=np.sin(theta[i]-theta[k]);row[k]=np.sin(theta[j]-theta[i]);row/=np.linalg.norm(row);C.append(row)
 C=np.array(C);return np.vstack([np.c_[C,np.zeros_like(C),np.zeros(15)],np.c_[-C,C,np.zeros(15)]])
def points(v,theta):
 A=v[:5];r=1/v[5:10];return np.vstack([np.c_[r*np.cos(theta),r*np.sin(theta),r*A],[0,0,0],[0,0,1]])
def gates(v,theta,k):
 p=points(v,theta);t=p[FF];ed=np.stack([t[:,1]-t[:,0],t[:,2]-t[:,1],t[:,0]-t[:,2]],axis=1);aa=np.arctan2(np.linalg.norm(np.cross(ed,-np.roll(ed,1,axis=1)),axis=2),np.sum(ed*(-np.roll(ed,1,axis=1)),axis=2));cs=aa[:5,1:]+aa[5:,1:];m=[];ell={}
 for i in range(5):
  for col in(0,1):m.append(cs[i,col]-PI if i<k and col==1 else PI-cs[i,col])
 for s in(5,6):
  ell[s]=[]
  for i in range(k):
   a=(i+1)%5;rho=cs[i,1]-PI;r=np.linalg.norm(p[s]-p[a]);b=np.linalg.norm(p[11-s]-p[a]);ell[s].append(math.atan2(b*np.sin(rho),r+b*np.cos(rho)))
 g={s:[aa[(s-5)*5+i+1,0]+ell[s][i+1]-ell[s][i] for i in range(k-1)]+[aa[(s-5)*5+k,0]-ell[s][k-1]] for s in(5,6)}
 return np.array(m),g
raw=json.loads(Path('/private/tmp/n7_run_search.json').read_text())['examples'];rng=np.random.default_rng(913866);start=time.time();results=[]
for k in(3,4):
 theta,initial=profile(raw['F'*k+'C'*(5-k)+':ordered']['points']);L=domain(theta)
 for i in range(k):
  for j in range(i+1,k):
   for trial in range(4):
    v=initial.copy();v[:5]+=rng.normal(0,.8)*np.cos(theta)+rng.normal(0,.8)*np.sin(theta)
    if trial%2:v[:5]=v[5:]-v[:5]
    def margins(x):
     pat,g=gates(x,theta,k);return np.r_[pat,-g[5][i],-g[6][j]]
    vv=np.r_[v,min(margins(np.r_[v,0]))-.00001]
    cons=[LinearConstraint(L,1e-10,np.inf),{'type':'ineq','fun':lambda x:margins(x)-x[-1]}]
    opt=minimize(lambda x:-x[-1],vv,jac=lambda x:np.r_[np.zeros(10),-1.],method='SLSQP',constraints=cons,bounds=Bounds([-100]*5+[1e-7]*5+[-4],[100]*10+[1]),options={'maxiter':1500,'ftol':1e-11})
    pat,g=gates(opt.x,theta,k);score=min(margins(opt.x));support=min(L@opt.x);r={'run':k,'opposing_indices':[i,j],'trial':trial,'success':bool(opt.success),'score':float(score),'support_min':float(support),'gates':g,'points':points(opt.x,theta).tolist()};results.append(r);print(k,i,j,trial,score,support,time.time()-start,flush=True)
    Path('/private/tmp/n7_run_profile_search.json').write_text(json.dumps({'scope':'Floating nonplanar profile optimization. Positive candidates require independent exact certification; failure to find one proves nothing.','results':results},indent=2)+'\n')
    if score>1e-5 and support>1e-12:raise SystemExit('Positive candidate found')
    if time.time()-start>240:raise SystemExit('Time bound reached')
