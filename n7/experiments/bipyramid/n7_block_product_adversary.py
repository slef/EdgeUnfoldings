"""Try to break the product criterion on contiguous bad blocks. Numerical only."""
import numpy as np,math,json,time
from pathlib import Path
from scipy.optimize import minimize,Bounds
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

from n7_pair_class_search import measurements
from n7.bipyramid_morph import FACES
FF=np.array(FACES);PI=math.pi;raw=json.loads(Path('/private/tmp/n7_product_search.json').read_text())['examples'];rng=np.random.default_rng(913991);results=[];start=time.time()

def normalize(p,target):
 orig=measurements(p)['pattern']
 for a in range(5):
  for d in(1,-1):
   pat=''.join(orig[(a+i)%5] if d==1 else orig[(a-i-1)%5].translate(str.maketrans('BF','FB')) for i in range(5))
   if pat==target:return p[[(a+d*i)%5 for i in range(5)]+[5,6]]
 raise ValueError('No normalized pattern')
def values(x,target,ia,ib):
 theta=np.r_[0,x[:4]];v=x[4:14];p=points(v,theta);t=p[FF];ed=np.stack([t[:,1]-t[:,0],t[:,2]-t[:,1],t[:,0]-t[:,2]],axis=1);aa=np.arctan2(np.linalg.norm(np.cross(ed,-np.roll(ed,1,axis=1)),axis=2),np.sum(ed*(-np.roll(ed,1,axis=1)),axis=2));cs=aa[:5,1:]+aa[5:,1:];m=[]
 for i,c in enumerate(target):
  for col in(0,1):m.append(cs[i,col]-PI if(c=='B' and col==0)or(c=='F'and col==1)else PI-cs[i,col])
 e=np.roll(p[:5],-1,axis=0)-p[:5];l=np.linalg.norm(e,axis=1);u=p[5]-p[:5];w=p[6]-p[:5];al=np.sum(u*e,axis=1)/l;be=np.sum(w*e,axis=1)/l;hp=np.linalg.norm(np.cross(u,e),axis=1)/l;hq=np.linalg.norm(np.cross(w,e),axis=1)/l;D=np.sqrt((al-be)**2+(hp+hq)**2);H=np.sum(u*u-w*w,axis=1);ratio=H/(D*np.roll(D,1));return np.r_[m,ratio[ia]-1,-ratio[ib]-1],p,ratio
for target,key in [('FFFCC','BBBCC'),('BBFCC','BBFCC'),('FFFFC','BBBBC'),('BBBFC','BBBFC'),('BBFFC','BBFFC')]:
 p=normalize(np.array(raw[key]['points']),target);th,v=profile(p);th-=th[0];bad=[i for i in range(5) if target[i]=='B'or target[(i-1)%5]=='F']
 for ii,ia in enumerate(bad):
  for ib in bad[ii+1:]:
   for trial in range(3):
    vv=v.copy();vv[:5]+=rng.normal(0,.5)*np.cos(th)+rng.normal(0,.5)*np.sin(th)
    if trial%2:vv[:5]=vv[5:]-vv[:5]
    x=np.r_[th[1:],vv,0.];x[-1]=min(values(x,target,ia,ib)[0])-.00001
    def geometry(x):
     theta=np.r_[0,x[:4]];g=np.diff(np.r_[theta,2*PI]);return np.r_[g-1e-5,PI-1e-5-g,domain(theta)@np.r_[x[4:14],0]-1e-9]
    opt=minimize(lambda x:-x[-1],x,jac=lambda x:np.r_[np.zeros(14),-1.],method='SLSQP',bounds=Bounds([1e-5]*4+[-100]*5+[1e-7]*5+[-5],[2*PI-1e-5]*4+[100]*10+[1]),constraints=[{'type':'ineq','fun':geometry},{'type':'ineq','fun':lambda x:values(x,target,ia,ib)[0]-x[-1]}],options={'ftol':1e-10,'maxiter':1000})
    margins,pp,ratio=values(opt.x,target,ia,ib);score=float(min(margins));g=float(min(geometry(opt.x)));row={'pattern':target,'pair':[ia,ib],'trial':trial,'score':score,'geometry_margin':g,'optimizer_success':bool(opt.success),'points':pp.tolist(),'ratios':ratio.tolist()};results.append(row);print(target,ia,ib,trial,score,g,time.time()-start,flush=True)
    Path('/private/tmp/n7_block_product_adversary.json').write_text(json.dumps({'scope':'Floating variable-azimuth constrained search. No proof follows from unsuccessful optimization; positive candidates need exact checking.','results':results},indent=2)+'\n')
    if score>1e-5 and g>-1e-10 and measurements(pp) is not None:raise SystemExit('CANDIDATE')
    if time.time()-start>360:raise SystemExit('Time bound')
