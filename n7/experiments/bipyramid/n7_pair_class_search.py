"""Numerical discovery of branches left by the local three-petal separators."""
import json,math,random,time
from pathlib import Path
import numpy as np
from n7_two_gap_wide_search import sample
from n7.checks import canonical_pattern
PI=math.pi
FF=np.array([(s,i,(i+1)%5) for s in(5,6) for i in range(5)])
MASK=np.array([[j not in f for j in range(7)] for f in FF])
def measurements(p):
 t=p[FF];ed=np.stack([t[:,1]-t[:,0],t[:,2]-t[:,1],t[:,0]-t[:,2]],axis=1)
 cross=np.cross(ed,-np.roll(ed,1,axis=1));angles=np.arctan2(np.linalg.norm(cross,axis=2),np.sum(ed*(-np.roll(ed,1,axis=1)),axis=2))
 normals=np.cross(t[:,1]-t[:,0],t[:,2]-t[:,0]);vv=np.sum((p[None,:,:]-t[:,0,None,:])*normals[:,None,:],axis=2)
 vals=np.array([row[mask] for row,mask in zip(vv,MASK)])
 scale=np.ptp(p,axis=0).max();tol=1e-10*scale*np.linalg.norm(normals,axis=1)
 if not np.all((np.min(vals,axis=1)>tol)|(np.max(vals,axis=1)<-tol)):return None
 k=np.full(7,2*PI)
 for j in range(3):np.add.at(k,FF[:,j],-angles[:,j])
 sums=angles[:5,1:]+angles[5:,1:];pattern=''.join('B' if a>PI else 'F' if b>PI else 'C' for a,b in sums)
 ell={s:np.zeros(5) for s in(5,6)}
 for i,c in enumerate(pattern):
  if c=='C':continue
  col=0 if c=='B' else 1;v=i if c=='B' else(i+1)%5;rho=sums[i,col]-PI
  r=np.linalg.norm(p[5]-p[v]);s=np.linalg.norm(p[6]-p[v]);ell[5][i]=math.atan2(s*math.sin(rho),r+s*math.cos(rho));ell[6][i]=rho-ell[5][i]
 return {'pattern':pattern,'curvatures':k.tolist(),'angles':angles.tolist(),'ell':{s:e.tolist() for s,e in ell.items()},'omega':{s:angles[(s-5)*5:(s-4)*5,0].tolist() for s in(5,6)}}
def normalized(p,m):
 for d in(1,-1):
  for a in range(5):
   pattern=''.join(m['pattern'][(a+i)%5] if d==1 else m['pattern'][(a-i-1)%5].translate(str.maketrans('BF','FB')) for i in range(5))
   if pattern=='FCCBC':
    pp=p[[(a+d*i)%5 for i in range(5)]+[5,6]];return pp,measurements(pp)
 raise ValueError('chain pattern missing')
def pair_class(p,m,fan,long):
 i=0 if long==0 else 1;q=11-fan;aa=np.array(m['angles']);sb=(q-5)*5;fb=(fan-5)*5;mid=i+1;k=m['curvatures'];phi,psi=aa[sb+mid,1:];alpha=phi+k[i+1];beta=psi+k[i+2];theta=alpha+beta;lam,nu,rho=aa[sb+np.array([i,i+1,i+2]),0]
 sigma=aa[fb+i,2]+aa[fb+i+1,1];tau=aa[fb+i+1,2]+aa[fb+i+2,1]
 out={'theta':theta,'sigma_plus_tau':sigma+tau,'source_angles':[lam,nu,rho],'middle_curvature_sum':k[i+1]+k[i+2]}
 if theta<PI-1e-8:
  ll=np.linalg.norm(p[i+1]-p[i+2]);L=ll*math.sin(beta)/math.sin(theta);R=ll*math.sin(alpha)/math.sin(theta);s=np.linalg.norm(p[q]-p[i+1]);sp=np.linalg.norm(p[q]-p[i+2]);half=(PI+theta)/2
  out['cut_length_deficits']=[s-L,sp-R];out['wide_angle_slacks']=[half-lam,half-rho]
  out['branch']='Case A wide' if(s<L-1e-8 and lam<half-1e-8)or(sp<R-1e-8 and rho<half-1e-8) else 'Case A residual'
 elif theta>=PI+1e-8 and sigma+tau>=PI+1e-8:out['branch']='base cones'
 else:out['branch']='small-fan pocket' if sigma+tau<PI-1e-8 else 'near-boundary'
 return out

def main():
 rng=random.Random(913618);base=np.array([[-75,4,0],[-60,-7,0],[12,-10,0],[54,-7,0],[81,0,0],[18,-8,1],[-20,-3,-5]],float)/10
 start=time.time();valid=relevant=0;counts={};examples={};residual=[];all_residual=[]
 for attempt in range(350000):
  if rng.random()<.6:
   p=base.copy();p[:5,0]+=np.array([rng.gauss(0,1.2) for _ in range(5)]);p[:5,1]+=np.array([rng.gauss(0,.25) for _ in range(5)]);
   if rng.random()<.6:p[:5,2]+=np.array([rng.gauss(0,.04) for _ in range(5)])
   for s in(5,6):p[s,:2]+=np.array([rng.gauss(0,2),rng.gauss(0,.25)]);p[s,2]*=10**rng.uniform(-1.7,1.2)
   p[:,0]*=10**rng.uniform(-1.7,1.2)
  else:p=sample(rng)
  m=measurements(p)
  if m is None:continue
  valid+=1
  if canonical_pattern(m['pattern'])!='BCFCC' or max(m['curvatures'][5:])>=PI or min(m['curvatures'])<1e-7:continue
  p,m=normalized(p,m);relevant+=1;options=[]
  for fan in(5,6):
   e=m['ell'][fan];w=m['omega'][fan]
   if e[0]+e[3]>=w[1]+w[2]-1e-8:continue
   long=0 if e[0]>w[1]+1e-8 else 3 if e[3]>w[2]+1e-8 else None
   c={'branch':'both short'} if long is None else pair_class(p,m,fan,long)
   row={'points':p.tolist(),**m,'fan':fan,'long_patch':long,'pair_case':c};name=c['branch'];counts[name]=counts.get(name,0)+1;options.append(row)
   if name not in examples:examples[name]=row
   if name in('Case A residual','small-fan pocket'):residual.append(row)
  if options and all(r['pair_case']['branch'] in('Case A residual','small-fan pocket') for r in options):all_residual.append(options)
  if len(all_residual)>=3:break
  if attempt%20000==0:print(attempt,valid,relevant,counts,len(all_residual),flush=True)
  if time.time()-start>540:break
 out={'scope':'Floating discovery only; local separator branch tests are numerical and are not proof predicates.','seed':913618,'attempts':attempt+1,'valid':valid,'relevant':relevant,'counts':counts,'examples':examples,'residual_examples':residual[:10],'all_eligible_residual':all_residual}
 Path('/private/tmp/n7_pair_class_search.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',attempt+1,valid,relevant,counts,len(all_residual),flush=True)
if __name__=='__main__':main()
