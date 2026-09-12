"""Exact examples for the written bipyramid local and two-patch rules.

The geometric proofs are in BIPYRAMID_OVERNIGHT.md. This checker verifies
specified rational inputs and their hypotheses; samples are not proof premises.
"""
from pathlib import Path
from fractions import Fraction as F
import json
from n7.bipyramid_morph import ROOT,FACES,I,exact_points,support,develop,check_net,sub,dot,cross,cross2,separating_axis,cut_at

def angle_factor(p,f,v):
 a,b=[sub(p[j],p[v]) for j in f if j!=v];c=cross(a,b)
 return dot(a,b),dot(c,c).sqrt()

def product(z,w):return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])

def phase(p,v):
 z=(I.bounds(1),I.bounds(0))
 for f in FACES:
  if v in f:z=product(z,angle_factor(p,f,v))
 return z

def strict_sign(x):
 if x.lo>0:return 1
 if x.hi<0:return -1
 raise ValueError('Strict sign not certified')

def patch_pattern(p):
 symbols=[];evidence=[]
 for i in range(5):
  vals=[product(angle_factor(p,FACES[i],v),angle_factor(p,FACES[5+i],v))[1] for v in(i,(i+1)%5)]
  signs=[strict_sign(x) for x in vals]
  if signs==[-1,-1]:raise ValueError('Impossible two-reflex patch')
  symbols.append('B' if signs[0]<0 else 'F' if signs[1]<0 else 'C')
  evidence.append([x.export() for x in vals])
 return ''.join(symbols),evidence

def sharper_pole(p):
 a,b=phase(p,5),phase(p,6);sa,sb=strict_sign(a[1]),strict_sign(b[1])
 if sa!=sb:return (5 if sa>0 else 6),{'phase_halves':[sa,sb]}
 d=cross2(a,b);return (5 if strict_sign(d)>0 else 6),{'phase_halves':[sa,sb],'phase_determinant':d.export()}

def extension_comparison(p,pole,i,symbol):
 """Compare the two angles in (0,pi) by their cosine difference."""
 k=(i+3)%5 if symbol=='F' else (i+2)%5
 n=develop(p,cut_at(11-pole,k));fan_base=(pole-5)*5;petal_base=(6-pole)*5
 fan=n[fan_base+i];O=fan[0];P=sub(n[petal_base+i][0],O)
 ray=sub(fan[2] if symbol=='F' else fan[1],O)
 cos_extension=dot(ray,P)/(dot(ray,ray)*dot(P,P)).sqrt()
 receiver=(i+(1 if symbol=='F' else -1))%5
 a,b=sub(p[receiver],p[pole]),sub(p[(receiver+1)%5],p[pole])
 cos_receiver=dot(a,b)/(dot(a,a)*dot(b,b)).sqrt()
 value=cos_extension-cos_receiver
 return strict_sign(value)>0,value.export()

def receiver_gate(p,pole):
 """Certify 2*kappa_pole + kappa_other > 2*pi; equality is a written boundary case."""
 z=phase(p,pole);other=phase(p,11-pole)
 if z[1].lo>0:return {'kind':'pole above pi','phase_sine':z[1].export()}
 if z[1].hi>=0:raise ValueError('Chosen pole phase is uncertain')
 other_sign=strict_sign(other[1])
 c=z[0]/dot(z,z).sqrt();cc=other[0]/dot(other,other).sqrt()
 half_cos=((1+cc)/2).sqrt()
 value=c+(-half_cos if other_sign>0 else half_cos)
 if value.hi>=0:raise ValueError('Weighted receiver gate not certified')
 return {'kind':'both poles below pi; weighted gate' if other_sign<0 else 'weighted gate with the other pole above pi','negative_cosine_test':(-value).export(),
  'pole_phase_sines':[z[1].export(),other[1].export()]}

def two_gap_choice(p,pattern,pole):
 ph=phase(p,pole);gate=receiver_gate(p,pole)
 bad=[i for i,c in enumerate(pattern) if c!='C']
 if len(bad)!=2:raise ValueError('This example checker expects exactly two inward patches')
 if pattern[bad[0]]==pattern[bad[1]] and (bad[1]-bad[0])%5 in(1,4):
  if ph[1].lo<=0:raise ValueError('Adjacent same-direction patches need the original large-gap gate')
  first=next(i for i in bad if(i+1)%5 in bad)
  k=(first+2)%5 if pattern[first]=='F' else first
  return cut_at(11-pole,k),{'branch':'adjacent-same','curvature_gate':gate}
 receiver={i:(i+(1 if pattern[i]=='F' else -1))%5 for i in bad}
 if any(pattern[j]!='C' for j in receiver.values()) or len(set(receiver.values()))!=2:raise ValueError('This checker expects distinct convex receivers')
 comparisons={i:extension_comparison(p,pole,i,pattern[i]) for i in bad}
 long=[i for i in bad if not comparisons[i][0]]
 protected={(i+1)%5 if pattern[i]=='F' else i for i in bad}
 if len(long)==2:fan=11-pole;k=next(k for k in range(5) if k not in protected);branch='switch-pole'
 elif len(long)==1:fan=pole;i=long[0];k=(i+2)%5 if pattern[i]=='F' else (i-1)%5;branch='one-long'
 else:fan=pole;k=next(k for k in range(5) if k not in protected);branch='both-short'
 return cut_at(11-fan,k),{'branch':branch,'curvature_gate':gate,
  'receivers':receiver,'extension_comparisons':comparisons}

def length_choice(p):
 source,order=sharper_pole(p);dist=[dot(sub(p[5],p[i]),sub(p[5],p[i])).sqrt()+dot(sub(p[6],p[i]),sub(p[6],p[i])).sqrt() for i in range(5)]
 eligible=[k for k in range(5) if all(k==i or (dist[k]-dist[i]).lo>0 for i in range(5))]
 if len(eligible)!=1:raise ValueError('Unique largest distance sum not certified')
 k=eligible[0];cut=cut_at(source,k);net=develop(p,cut);left,right=(k-1)%5,k;sb=(source-5)*5;fb=(6-source)*5
 pairs=[(sb+left,sb+right),(sb+left,fb+right),(sb+right,fb+left)]
 return {'source':source,'slit':k,'pole_order':order,'distance_sum_gaps':{i:(dist[k]-dist[i]).export() for i in range(5) if i!=k},
  'local_separators':[{'faces':list(pair),**separating_axis(net[pair[0]],net[pair[1]])} for pair in pairs]}

def certify(row):
 exact=exact_points(row['points']);supports=support(exact);p=[[I.bounds(x) for x in v] for v in exact]
 pattern,signs=patch_pattern(p);cut,choice=two_gap_choice(p,pattern,row['gate_pole']);good=check_net(p,cut)
 return {'strict_support_minimum':str(min(x for _,vals in supports for x in vals)),
  'pattern':pattern,'patch_sines':signs,'chosen_cut':cut,'choice':choice,
  'fan_pairs':len(good['shared_vertex_pairs']),'strict_separators':good['strict_separators'],
  'length_slit_local_check':length_choice(p)}

def replay_saved():
 rows=json.loads((ROOT/'results/bipyramid-two-gap.json').read_text())['examples']
 for row in rows:
  if json.loads(json.dumps(certify(row)))!=row['certificate']:raise ValueError('Two-gap certificate mismatch')
 return {'exact_examples':len(rows),'local_pairs_checked':3*len(rows),'full_nets_checked':len(rows),'scope':'Specified rational examples of the written theorems, not a universal computational proof.'}

if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
