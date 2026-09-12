"""Read old n6 examples, without changing them, to test a proposed n7 extension."""
from pathlib import Path
import numpy as np,json,math
from fractions import Fraction
R=Path('/Users/sl/Dropbox/MyStuff/dev/EdgeUnfoldings/n6/results');out=[];checked=0
for fn in R.glob('*.certificate.json'):
 x=json.loads(fn.read_text());ps=x.get('coordinate_polynomials',[])
 if len(ps)!=6 or x.get('parameter_box') or not x.get('faces') or len(x['faces'])!=8:continue
 try:p=np.array([[float(Fraction(c[0][0])) for c in v] for v in ps])
 except Exception:continue
 faces=x['faces'];edges={tuple(sorted((a,b))) for f in faces for a,b in zip(f,f[1:]+f[:1])}
 for source in range(6):
  far=[i for i in range(6) if i!=source and tuple(sorted((source,i))) not in edges]
  if len(far)!=1 or source>far[0]:continue
  other=far[0];ring=[i for i in range(6) if i not in(source,other)];order=[ring[0]]
  while len(order)<4:
   ns=[v for v in ring if v not in order and tuple(sorted((order[-1],v)))in edges]
   if not ns:break
   order.append(ns[0])
  if len(order)!=4:continue
  pp=p[order+[source,other]];FF=np.array([(s,i,(i+1)%4) for s in(4,5) for i in range(4)]);t=pp[FF];ed=np.stack([t[:,1]-t[:,0],t[:,2]-t[:,1],t[:,0]-t[:,2]],axis=1);aa=np.arctan2(np.linalg.norm(np.cross(ed,-np.roll(ed,1,axis=1)),axis=2),np.sum(ed*(-np.roll(ed,1,axis=1)),axis=2));cs=aa[:4,1:]+aa[4:,1:];pat=''.join('B'if a>math.pi else'F'if b>math.pi else'C'for a,b in cs)
  if pat.count('C')!=1:continue
  checked+=1;bad=[i for i in range(4) if pat[i]=='B'or pat[(i-1)%4]=='F'];e=np.roll(pp[:4],-1,axis=0)-pp[:4];l=np.linalg.norm(e,axis=1);u=pp[4]-pp[:4];v=pp[5]-pp[:4];al=np.sum(u*e,axis=1)/l;be=np.sum(v*e,axis=1)/l;hp=np.linalg.norm(np.cross(u,e),axis=1)/l;hq=np.linalg.norm(np.cross(v,e),axis=1)/l;D=np.sqrt((al-be)**2+(hp+hq)**2);H=np.sum(u*u-v*v,axis=1);rat=H/(D*np.roll(D,1))
  if min(rat[bad])<-1-1e-7 and max(rat[bad])>1+1e-7:
   row={'file':fn.name,'points':pp.tolist(),'pattern':pat,'ratios':rat.tolist()};out.append(row);print('FOUND',fn.name,source,other,pat,rat,flush=True)
Path('/private/tmp/n6_product_probe.json').write_text(json.dumps({'scope':'Numerical investigation of old exact examples, not a new certificate.','checked':checked,'conflicts':out},indent=2)+'\n');print('DONE',checked,len(out))
