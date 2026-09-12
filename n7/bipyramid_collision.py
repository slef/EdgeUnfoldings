"""Replay the exact first-collision classification for one insertion path.

The circle-line argument and local separation lemma are written in
BIPYRAMID_COLLISION.md. This is not a universal shape-space certificate.
"""
from fractions import Fraction as F
from itertools import combinations
import json
import networkx as nx
from n7.bipyramid_morph import ROOT,FACES,I,exact_points,morph_geometry,develop,adjacency,sub,cross2,dot,separating_axis,cut_at
from n7.a992_exact import S
from n7.bipyramid_rule_checks import phase,angle_factor,product
LOCAL={(0,1),(0,6),(1,5)}

def problem():
 row=next(r for r in json.loads((ROOT/'results/bipyramid-morph.json').read_text())['examples'] if r['id']=='minimum-fixed-net-failure')
 if row['inserted_vertex']!=2 or row['subdivision_edge']!=[1,3] or {tuple(e) for e in row['initial_cut']}!={tuple(e) for e in cut_at(5,1)}:raise ValueError('The written collision theorem uses the specified insertion and cuts')
 p=exact_points(row['points']);p0,geometry=morph_geometry(p,2,[1,3]);g=adjacency(FACES,row['initial_cut'])
 pairs=[(a,b) for a,b in combinations(range(10),2) if(a,b) not in LOCAL and not set.intersection(*(set(FACES[i]) for i in nx.shortest_path(g,a,b)))]
 if len(pairs)!=15:raise ValueError('Unexpected pair partition')
 return row,p,p0,geometry,pairs

def parameter_box(p,p0,lo,hi):
 q=[[I.bounds(x) for x in v] for v in p];q[2]=[I.bounds(a)+I.bounds(lo,hi)*(b-a) for a,b in zip(p0[2],p[2])];return q

def interval_proof(p,p0,cut,pairs,lo,hi):
 q=parameter_box(p,p0,lo,hi);n=develop(q,cut);v,w=phase(q,5),phase(q,6);d=cross2(v,w)
 if v[1].hi>=0 or w[1].hi>=0 or d.lo<=0:raise ValueError('Pole angles or order not certified')
 seps=[separating_axis(n[a],n[b]) for a,b in pairs]
 other=[cross2(sub(n[0][(i+1)%3],n[0][i]),sub(n[6][1],n[0][i])) for i in(0,1)]
 if any(x.lo<=0 for x in other):raise ValueError('Other root-edge signs not certified')
 return {'nonlocal_gap':min(F(x['gap_lower_bound']) for x in seps),
  'negative_pole_sines':F(min(-v[1].hi,-w[1].hi),S),'pole_order':F(d.lo,S),
  'other_root_edges':min(F(x.lo,S) for x in other)}

def certify(spec):
 row,p,p0,geometry,pairs=problem();cut=row['initial_cut'];next_start=F(0);mins={}
 for a,b in spec['cells']:
  a,b=F(a),F(b)
  if a!=next_start or not a<b<=1:raise ValueError('Incomplete parameter cover')
  values=interval_proof(p,p0,cut,pairs,a,b)
  for k,v in values.items():mins[k]=min(mins.get(k,v),v)
  next_start=b
 if next_start!=1:raise ValueError('Cover does not reach one')
 lo,hi=map(F,spec['critical_bracket'])
 if not 0<lo<hi<1:raise ValueError('Invalid critical bracket')
 sides=[]
 for t in(lo,hi):
  n=develop(parameter_box(p,p0,t,t),cut);sides.append(cross2(sub(n[0][0],n[0][2]),sub(n[6][1],n[0][2])))
 if sides[0].hi>=0 or sides[1].lo<=0:raise ValueError('Opposite crossing signs not certified')
 n=develop(parameter_box(p,p0,lo,hi),cut);a,b=n[0][2],n[0][0];P=n[6][1]
 along=dot(sub(P,a),sub(b,a))/dot(sub(b,a),sub(b,a))
 if along.lo<=0 or along.hi>=S:raise ValueError('Contact not inside the cut edge')
 fixed=parameter_box(p,p0,F(0),F(0));net=develop(fixed,cut);C=net[5][0];A=net[0][2];V=net[0][0]
 radius,direction=sub(A,C),sub(V,A);nd=-dot(radius,direction);nc=-cross2(radius,direction)
 reflex=-product(angle_factor(fixed,FACES[0],1),angle_factor(fixed,FACES[5],1))[1]
 if min(nd.lo,nc.lo,reflex.lo)<=0:raise ValueError('Fixed reflex corner geometry not certified')
 return {'geometry':geometry,'nonlocal_pairs':pairs,'closed_interval_cells':len(spec['cells']),
  'minimum_bounds':{k:str(v) for k,v in mins.items()},
  'critical_bracket':spec['critical_bracket'],'cut_line_sides':[x.export() for x in sides],
  'contact_edge_parameter':along.export(),'negative_radius_cut_dot':nd.export(),
  'negative_radius_cut_cross':nc.export(),'negative_reflex_sine':reflex.export()}

def replay_saved():
 spec=json.loads((ROOT/'results/bipyramid-first-collision.json').read_text())
 if json.loads(json.dumps(certify(spec)))!=spec['certificate']:raise ValueError('First-collision certificate mismatch')
 return {'cells':len(spec['cells']),'nonlocal_pairs':15,'critical_bracket':spec['critical_bracket'],
  'scope':'The specified minimum-vertex insertion and initial cut tree only.'}

if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
