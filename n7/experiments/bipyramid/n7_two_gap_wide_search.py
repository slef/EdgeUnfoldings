import itertools,json,math,random,time
from pathlib import Path
import numpy as np
from n7.a992 import unfold,penetration
from n7.bipyramid_morph import FACES
from n7.checks import canonical_pattern
PI=math.pi

def angle(a,b):return math.atan2(np.linalg.norm(np.cross(a,b)),a@b)
def geometry(p):
 for f in FACES:
  a,b,c=p[list(f)];n=np.cross(b-a,c-a);vals=[(p[v]-a)@n for v in range(7) if v not in f]
  if not(min(vals)>1e-10 or max(vals)<-1e-10):return False
 return True

def measurements(p):
 curv=np.full(7,2*PI);faceangles=[]
 for f in FACES:
  aa={v:angle(*[p[j]-p[v] for j in f if j!=v]) for v in f};faceangles.append(aa)
  for v in f:curv[v]-=aa[v]
 pattern=''.join('B' if faceangles[i][i]+faceangles[5+i][i]>PI else 'F' if faceangles[i][(i+1)%5]+faceangles[5+i][(i+1)%5]>PI else 'C' for i in range(5))
 ws={s:[faceangles[(s-5)*5+i][s] for i in range(5)] for s in (5,6)};ell={}
 for pole in (5,6):
  other=11-pole;out=[]
  for i in range(5):
   # The two-face patch uses its local equator edge as hinge.
   fs=((pole,i,(i+1)%5),(other,i,(i+1)%5))
   nn=unfold(p,[],fs,0);P=nn[1][0];theta=math.atan2(P[1],P[0]);out.append(-theta if pattern[i]=='B' else theta-ws[pole][i] if pattern[i]=='F' else 0.)
  ell[pole]=out
 return {'curvatures':curv.tolist(),'pattern':pattern,'omega':ws,'ell':ell}

def selection(m):
 pattern=m['pattern'];bad=[i for i,c in enumerate(pattern) if c!='C'];pole=max((5,6),key=lambda s:m['curvatures'][s]);gap_pole=pole
 if len(bad)!=2 or m['curvatures'][pole]<PI:return None
 if pattern[bad[0]]==pattern[bad[1]] and ((bad[1]-bad[0])%5 in(1,4)):
  first=next(i for i in bad if(i+1)%5 in bad);k=(first+2)%5 if pattern[first]=='F' else first
  return pole,k,'adjacent-same'
 target={i:(i+(1 if pattern[i]=='F' else -1))%5 for i in bad}
 if any(pattern[j]!='C' for j in target.values()):raise ValueError('Unclassified receiving patch')
 protected={(i+1)%5 if pattern[i]=='F' else i for i in bad}
 if len(set(target.values()))==1:
  j=next(iter(target.values()));pole=next(p for p in(5,6) if sum(m['ell'][p][i] for i in bad)<m['omega'][p][j])
  k=next(k for k in range(5) if k not in protected);return pole,k,'one-receiver'
 long=[i for i in bad if m['ell'][pole][i]>m['omega'][pole][target[i]]]
 if len(long)==2:
  pole=11-pole
  if not all(m['ell'][pole][i]<m['omega'][pole][target[i]] for i in bad):raise ValueError('Dual short identity failed')
  return pole,next(k for k in range(5) if k not in protected),'switch-pole'
 if len(long)==1:
  i=long[0];return pole,(i+2)%5 if pattern[i]=='F' else (i-1)%5,'one-long'
 return pole,next(k for k in range(5) if k not in protected),'both-short'

def cut(pole,k):return [(11-pole,i) for i in range(5)]+[(pole,k)]
def worst(p,c):
 n=unfold(p,c,FACES,0);return max((penetration(n[i],n[j]),i,j) for i,j in itertools.combinations(range(10),2))

def sample(rng):
 if rng.random()<.5:
  angles=sorted(rng.uniform(0,2*PI) for _ in range(5));rr=[10**rng.uniform(-.8,.8) for i in range(5)]
  ring=np.array([[r*math.cos(a),r*math.sin(a),rng.uniform(-1.5,2.5)] for r,a in zip(rr,angles)])
  p=np.vstack([ring,[0,0,0],[0,0,1]])
 else:
  angles=sorted(rng.uniform(0,2*PI) for _ in range(5));ring=np.array([[math.cos(a),math.sin(a),0] for a in angles]);ring[:,0]*=10**rng.uniform(-1.5,1.5)
  weights=np.array([rng.expovariate(1) for _ in range(5)]);o=weights@ring/weights.sum();h,k=10**rng.uniform(-2,2),10**rng.uniform(-2,2)
  if rng.random()<.5:ring[:,2]=np.array([rng.uniform(-.15,.15) for i in range(5)])*min(h,k)
  p=np.vstack([ring,[*o[:2],h],[*o[:2],-k]])
 # Shears and anisotropic stretches preserve the graph but change its angles.
 shear=np.array([rng.uniform(-1,1),rng.uniform(-1,1)])*10**rng.uniform(-1,2)
 p[:,:2]+=p[:,2,None]*shear
 p[:,0]*=10**rng.uniform(-1,1)
 return p

def main():
 rng=random.Random(913612);start=time.time();examples={};bad=None;counts={};valid=0;checked=0;long_fail=None
 for attempt in range(45000):
  p=sample(rng)
  if not geometry(p):continue
  valid+=1;m=measurements(p);s=selection(m)
  if s:
   fan,k,branch=s;key=canonical_pattern(m['pattern'])+':'+branch;counts[key]=counts.get(key,0)+1;checked+=1
   score,i,j=worst(p,cut(fan,k))
   if score>1e-7:bad={'points':p.tolist(),**m,'selection':s,'failure':[score,i,j]};break
   if key not in examples:examples[key]={'points':p.tolist(),**m,'selection':s,'cut':cut(fan,k),'worst_penetration':score}
  if long_fail is None and m['pattern'].count('C')<4:
   source=max((5,6),key=lambda s:m['curvatures'][s]);k=max(range(5),key=lambda i:np.linalg.norm(p[5]-p[i])+np.linalg.norm(p[6]-p[i]));score,i,j=worst(p,cut(11-source,k))
   if score>1e-5:long_fail={'points':p.tolist(),**m,'source':source,'slit':k,'failure':[score,i,j],'cut':cut(11-source,k)}
  if attempt%1000==0:print(attempt,valid,checked,len(examples),'max-distance failure',long_fail is not None,flush=True)
  if time.time()-start>600:break
 result={'scope':'Floating discovery and algorithm stress check only; not proof of any shape or universal rule.','seed':913612,'attempts':attempt+1,'valid':valid,'selected_checked':checked,'case_counts':counts,'examples':examples,'rule_failure':bad,'length_slit_whole_net_failure':long_fail}
 Path('/private/tmp/n7_two_gap_wide_search.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k not in('examples','length_slit_whole_net_failure')},flush=True)
if __name__=='__main__':main()
