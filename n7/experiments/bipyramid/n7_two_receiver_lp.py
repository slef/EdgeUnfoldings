"""Necessary-angle relaxation. Feasible angle arrays are not convex realizations."""
import numpy as np,json
from scipy.optimize import linprog
from pathlib import Path
N=33;one=np.zeros(N);one[-1]=1;unit=lambda i:np.eye(N)[i]
ang={(s,i,v):unit((s-5)*15+3*i+j) for s in(5,6) for i in range(5) for j,v in enumerate((s,i,(i+1)%5))}
k={v:2*one-sum(a for (s,i,w),a in ang.items() if w==v) for v in range(7)}
w=lambda s,i:ang[s,i,s];corner=lambda i,v:ang[5,i,v]+ang[6,i,v]
def solve(pattern):
 bad=[i for i,c in enumerate(pattern) if c!='C'];receiver={i:(i+(1 if pattern[i]=='F' else -1))%5 for i in bad};vertex={i:(i+1)%5 if pattern[i]=='F' else i for i in bad}
 rho={i:corner(i,vertex[i])-one for i in bad};ell={(s,i):unit(30+j) if s==5 else rho[i]-unit(30+j) for j,i in enumerate(bad) for s in(5,6)}
 A=[];b=[];names=[];eps=1e-7
 def positive(x,name):A.append(-x[:-1]);b.append(x[-1]-eps);names.append(name)
 for x in ang.values():positive(x,'positive angle')
 for v in range(7):positive(k[v],'curvature')
 for s in(5,6):positive(one-k[s],'low pole')
 for i in range(5):
  for v in(i,(i+1)%5):positive(corner(i,v)-one if i in bad and vertex[i]==v else one-corner(i,v),'pattern')
 for(s,i,v),a in ang.items():positive(2*one-k[v]-2*a,'link side')
 for(s,i),e in ell.items():
  positive(e,'extension');positive(2*one-k[s]-2*(w(s,i)+e),'half fan')
 for s,i in zip((5,6),bad):
  q=11-s;r=receiver[i];a=vertex[i]
  positive(ell[s,i]-w(s,r),'long receiver')
  positive(2*ell[q,i]+k[a]-one,'other extension bound')
  positive(w(q,r)-k[a]-ell[q,i],'receiver diagonal split')
  positive(one-w(q,i)-ell[q,i],'outer triangle source apex')
 Aeq=[];beq=[]
 for s in(5,6):
  for i in range(5):
   a=sum(ang[s,i,v] for v in(s,i,(i+1)%5))-one;Aeq.append(a[:-1]);beq.append(-a[-1])
 r=linprog(np.zeros(N-1),A_ub=A,b_ub=b,A_eq=Aeq,b_eq=beq,bounds=[(None,None)]*(N-1),method='highs')
 out={'pattern':pattern,'message':r.message}
 if r.success:
  x=np.r_[r.x,1];out.update({'curvatures':[float(k[v]@x) for v in range(7)],'angles':{str((s,i)):[float(ang[s,i,v]@x) for v in(s,i,(i+1)%5)] for s in(5,6) for i in range(5)},'ell':{str(key):float(e@x) for key,e in ell.items()}})
 return out
out={'scope':'Linear relaxation only. Feasibility is not geometric realizability.','cases':[solve(p) for p in('FCCBC','FCFCC','FCCCB')]}
Path('/private/tmp/n7_two_receiver_lp.json').write_text(json.dumps(out,indent=2)+'\n')
for r in out['cases']:print(r['pattern'],r['message'])
