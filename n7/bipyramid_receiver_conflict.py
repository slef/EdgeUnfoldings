"""Exact counterexample to two sufficient cone-selection shortcuts.

This does not refute edge unfolding: six star-plus-slit nets are certified.
It refutes choosing a pole where both receiver extensions are short and
shows that the two simultaneous receiver-plus-gap failures are realizable.
"""
import json
from n7.bipyramid_morph import ROOT,FACES,I,exact_points,support,develop,cut_at,sub,dot,cross2,check_net
from n7.bipyramid_rule_checks import phase,product,angle_factor,patch_pattern,sharper_pole

def long_beyond_gap(p,pole,i,symbol):
 z=phase(p,pole)
 if z[1].hi>=0:raise ValueError('This checker requires pole curvature in (0,pi)')
 receiver=(i+(1 if symbol=='F' else -1))%5
 rf=angle_factor(p,FACES[(pole-5)*5+receiver],pole)
 bound=product(rf,(z[0],-z[1]))
 if bound[1].lo<=0:raise ValueError('Receiver angle plus gap is not certified below pi')
 n=develop(p,cut_at(11-pole,(i+3)%5 if symbol=='F' else (i+2)%5))
 fan=n[(pole-5)*5+i];O=fan[0];P=sub(n[(6-pole)*5+i][0],O);ray=sub(fan[2] if symbol=='F' else fan[1],O)
 ellcos=dot(ray,P)/(dot(ray,ray)*dot(P,P)).sqrt()
 boundcos=bound[0]/dot(bound,bound).sqrt();margin=boundcos-ellcos
 if margin.lo<=0:raise ValueError('Long extension beyond receiver plus gap not certified')
 return {'pole':pole,'patch':i,'receiver':receiver,'pole_phase_sine':z[1].export(),
  'receiver_plus_gap_sine':bound[1].export(),'positive_cosine_difference':margin.export()}

def angle_less(z,w):
 """Strict comparison with both represented angles known to lie in (0,2*pi)."""
 def sign(x):
  if x.lo>0:return 1
  if x.hi<0:return -1
  raise ValueError('Uncertain phase half')
 a,b=sign(z[1]),sign(w[1])
 if a!=b:
  if a<0:raise ValueError('First angle is larger')
  return {'phase_halves':[a,b]}
 d=cross2(z,w)
 if d.lo<=0:raise ValueError('Angle order not certified')
 return {'phase_halves':[a,b],'positive_phase_determinant':d.export()}

def auxiliary_bridge(ex,p):
 faces=tuple(f for f in FACES if 4 not in f)+((5,3,0),(6,3,0))
 supports=support(ex,faces,[0,1,2,3,5,6]);phases={}
 for v in(0,1,2,3,5,6):
  z=(I.bounds(1),I.bounds(0))
  for f in faces:
   if v in f:z=product(z,angle_factor(p,f,v))
  phases[v]=z
 order=angle_less(phases[6],phases[5])
 maximum={v:angle_less(phases[3],phases[v]) for v in(0,1,2)}
 # Verify the chosen fan also satisfies the chain's sum-of-extensions rule.
 n=develop(p,cut_at(6,0));extensions=[]
 for i,symbol in((0,'F'),(3,'B')):
  O=n[i][0];P=sub(n[5+i][0],O);ray=sub(n[i][2] if symbol=='F' else n[i][1],O)
  cp=cross2(ray,P);positive=cp if cp.lo>0 else -cp
  if positive.lo<=0:raise ValueError('Nonpositive extension angle')
  extensions.append((dot(ray,P),positive))
 ext=product(*extensions);receivers=product(angle_factor(p,FACES[1],5),angle_factor(p,FACES[2],5))
 chain=angle_less(ext,receivers)
 cuts=[(6,i) for i in range(4)]+[(5,3)];net=check_net(p,cuts,faces)
 return {'deleted_vertex':4,'fan_pole':5,'source':6,'auxiliary_slit':3,
  'strict_support_minimum':str(min(x for _,vs in supports for x in vs)),
  'source_order':order,'maximum_equator_curvature':maximum,'chain_extension_order':chain,
  'auxiliary_fan_pairs':len(net['shared_vertex_pairs']),'auxiliary_strict_separators':net['strict_separators']}

def certify(row):
 ex=exact_points(row['points']);vol=support(ex);p=[[I.bounds(x) for x in q] for q in ex];pattern,signs=patch_pattern(p)
 if pattern!='FCCBC':raise ValueError('The specified conflict needs pattern FCCBC')
 source,order=sharper_pole(p)
 failures=[long_beyond_gap(p,5,0,'F'),long_beyond_gap(p,6,3,'B')]
 nets=[]
 for pole in(5,6):
  for slit in(0,2,4):
   cut=cut_at(11-pole,slit);c=check_net(p,cut)
   nets.append({'fan_pole':pole,'slit':slit,'cut':cut,'fan_pairs':len(c['shared_vertex_pairs']),'strict_separators':c['strict_separators']})
 return {'strict_support_minimum':str(min(x for _,vs in vol for x in vs)),
  'pattern':pattern,'patch_sines':signs,'sharper_pole':source,'pole_order':order,
  'two_conflicting_extensions':failures,'certified_safe_nets':nets,'auxiliary_bridge':auxiliary_bridge(ex,p)}

def replay_saved():
 row=json.loads((ROOT/'results/bipyramid-receiver-conflict.json').read_text())
 if json.loads(json.dumps(certify(row)))!=row['certificate']:raise ValueError('Receiver conflict certificate mismatch')
 return {'conflicting_receiver_plus_gap_tests':2,'certified_safe_nets':6,
  'scope':'One exact integer-coordinate bipyramid: sufficient cone shortcuts fail, but six original-edge nets are safe.'}

if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
