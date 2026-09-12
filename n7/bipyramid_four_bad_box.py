"""An exact full-coordinate neighborhood of four-inward low-pole bipyramids.

All 21 coordinates vary independently. Strict outward interval predicates
cover every point of the closed box; no sampled point is used as a proof.
"""
import json
from fractions import Fraction as F
from n7.bipyramid_morph import *
from n7.bipyramid_rule_checks import patch_pattern
from n7.angle_intervals import pi,face_angle
CENTER=[[-1504,-547,0],[100,0,0],[129,153,0],[-69,394,0],[-693,400,0],[0,0,1],[0,0,-1]]
def certify(eps):
 e=exact_points(CENTER);orient=support(e);p=[[I.bounds(x-eps,x+eps) for x in row] for row in e];supports=[]
 for face,(sign,_) in zip(FACES,orient):
  a,b,c=[p[v] for v in face];n=cross(sub(b,a),sub(c,a))
  for v in range(7):
   if v in face:continue
   val=sign*dot(n,sub(p[v],a))
   if val.lo<=0:raise ValueError('Supporting determinant not positive throughout')
   supports.append(val.export())
 pattern,signs=patch_pattern(p)
 if pattern!='CBBBB':raise ValueError('Wrong four-bad class')
 curvatures={v:2*pi()-sum(face_angle(p,f,v) for f in FACES if v in f) for v in (5,6)}
 margins={}
 for v,k in curvatures.items():
  if k.lo<=0 or (pi()/180-k).lo<=0:raise ValueError('Both poles below one degree not certified')
  margins[v]={'positive_curvature':k.export(),'below_one_degree':(pi()/180-k).export()}
 n=check_net(p,cut_at(6,0))
 return {'half_width':str(eps),'center':CENTER,'independent_coordinates':21,'strict_support_intervals':supports,
         'pattern':pattern,'patch_sines':signs,'pole_curvatures':margins,'cut':cut_at(6,0),'whole_box_net_check':n}
def replay_saved():
 d=json.loads((ROOT/'results/bipyramid-four-bad-box.json').read_text())
 if json.loads(json.dumps(certify(F(d['half_width']))))!=d:raise ValueError('Four-inward box certificate mismatch')
 n=d['whole_box_net_check']
 return {'independent_coordinate_intervals':21,'half_width':d['half_width'],'pattern':d['pattern'],
         'shared_vertex_pairs':len(n['shared_vertex_pairs']),'strict_interval_separators':len(n['strict_separators']),
         'scope':'Every coordinate tuple in the specified closed rational box, not the whole CBBBB class.'}
if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
