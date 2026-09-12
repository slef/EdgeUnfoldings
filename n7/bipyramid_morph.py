"""Exact checks for specified bipyramid insertion paths, not all bipyramids.

Convexity is proved by affine supporting determinants; pair safety uses
shared-vertex fans or strict rational interval separation. The written
geometric lemmas remain dependencies, not formally verified theorems.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import json
from n7.a992_exact import I,sub,dot,cross,cross2,separating_axis,inside
import networkx as nx
FACES=tuple((p,i,(i+1)%5) for p in (5,6) for i in range(5))
def exact_points(p):return [[F(str(x)) for x in v] for v in p]
def support(p,faces=FACES,active=None):
 active=range(len(p)) if active is None else active
 out=[]
 for fi,f in enumerate(faces):
  a,b,c=[p[v] for v in f];n=cross(sub(b,a),sub(c,a));rest=[v for v in active if v not in f];val=dot(n,sub(p[rest[0]],a));sgn=1 if val>0 else -1
  vs=[sgn*dot(n,sub(p[v],a)) for v in rest]
  if min(vs)<=0:raise ValueError(('Support',fi))
  out.append((sgn,vs))
 return out
def adjacency(faces,cut):
 ef={}
 for i,f in enumerate(faces):
  for a,b in combinations(f,2):ef.setdefault(tuple(sorted((a,b))),[]).append(i)
 cut={tuple(sorted(e)) for e in cut}
 vertices=set().union(*map(set,faces));tree=nx.Graph();tree.add_nodes_from(vertices);tree.add_edges_from(cut)
 if not cut<=set(ef) or not nx.is_tree(tree):raise ValueError('Not an original-edge spanning tree')
 g=nx.Graph();g.add_nodes_from(range(len(faces)))
 for e,ids in ef.items():
  if len(ids)!=2:raise ValueError('Nonclosed triangulation')
  if e not in cut:g.add_edge(*ids,hinge=e)
 if not nx.is_tree(g):raise ValueError('Uncut dual is not a tree')
 return g
def develop(p,cut,faces=FACES):
 p=[[x if isinstance(x,I) else I.bounds(x) for x in v] for v in p];g=adjacency(faces,cut)
 a,b,c=faces[0];L2=dot(sub(p[b],p[a]),sub(p[b],p[a]));L=L2.sqrt();D=dot(sub(p[c],p[a]),sub(p[c],p[a]))-dot(sub(p[c],p[b]),sub(p[c],p[b]))+L2
 x=D/(2*L);y=(dot(sub(p[c],p[a]),sub(p[c],p[a]))-x*x).sqrt()
 placed={0:{a:[I.bounds(0),I.bounds(0)],b:[L,I.bounds(0)],c:[x,y]}};queue=[0]
 for parent in queue:
  for child in g[parent]:
   if child in placed:continue
   a,b=g[parent][child]['hinge'];A,B=placed[parent][a],placed[parent][b];d=sub(B,A);perp=[-d[1],d[0]];o=next(v for v in faces[parent] if v not in (a,b));sign=cross2(d,sub(placed[parent][o],A))
   if sign.lo>0:perp=[-x for x in perp]
   elif sign.hi>=0:raise ValueError('Uncertain parent side')
   L2=dot(sub(p[b],p[a]),sub(p[b],p[a]));v=next(v for v in faces[child] if v not in(a,b));da=dot(sub(p[v],p[a]),sub(p[v],p[a]));db=dot(sub(p[v],p[b]),sub(p[v],p[b]));D=da-db+L2
   along=D/(2*L2);height=(4*L2*da-D*D).sqrt()/(2*L2)
   P=[A[j]+along*d[j]+height*perp[j] for j in range(2)]
   placed[child]={a:A,b:B,v:P};queue.append(child)
 return [[placed[i][v] for v in f] for i,f in enumerate(faces)]
def check_net(p,cut,faces=FACES):
 n=develop(p,cut,faces);g=adjacency(faces,cut);fans=[];seps=[]
 for a,b in combinations(range(len(faces)),2):
  path=nx.shortest_path(g,a,b);common=set.intersection(*(set(faces[i]) for i in path))
  if common:fans.append({'faces':[a,b],'shared_vertex':min(common),'path':path})
  else:seps.append({'faces':[a,b],**separating_axis(n[a],n[b])})
 return {'shared_vertex_pairs':fans,'strict_separators':seps}
def minimum(p,j):
 p=[[I.bounds(x) for x in v] for v in p];z=[]
 for v in range(7):
  r,s=I.bounds(1),I.bounds(0)
  for face in FACES:
   if v not in face:continue
   a,b=[sub(p[u],p[v]) for u in face if u!=v];c=dot(a,b);q=cross(a,b);d=dot(q,q).sqrt();r,s=r*c-s*d,r*d+s*c
  z.append((r,s))
 if z[j][1].hi>=0:raise ValueError('Chosen angle sum not in lower half')
 out=[]
 for k in range(7):
  if k==j:continue
  if z[k][1].lo>0:out.append([k,'upper',z[k][1].export()])
  elif z[k][1].hi<0:
   d=cross2(z[k],z[j]);
   if d.lo<=0:raise ValueError('Minimum-curvature ordering not certified')
   out.append([k,'lower',d.export()])
  else:raise ValueError('Uncertain phase')
 return out


ROOT=Path(__file__).resolve().parent

def cut_at(source,slit):
 return [(source,i) for i in range(5)]+[(11-source,slit)]

def morph_geometry(p,j,edge):
 """Verify exact six-vertex cap and the whole affine insertion geometry."""
 a,b=(j-1)%5,(j+1)%5
 if set(edge)=={a,b}:cap=((5,a,b),(6,a,b));route='equator edge'
 elif set(edge)=={5,6}:cap=((5,6,a),(5,6,b));route='pole edge'
 else:raise ValueError('Unsupported subdivision edge')
 reduced=tuple(f for f in FACES if j not in f)+cap
 reduced_proof=support(p,reduced,[v for v in range(7) if v!=j])
 end=support(p);p0=[v[:] for v in p];p0[j]=[(x+y)/2 for x,y in zip(p[edge[0]],p[edge[1]])]
 start_values=[];areas=[]
 for f,(sgn,_) in zip(FACES,end):
  a,b,c=[p0[v] for v in f];n=cross(sub(b,a),sub(c,a));areas.append(dot(n,n))
  start_values.extend(sgn*dot(n,sub(p0[v],a)) for v in range(7) if v not in f)
 if min(start_values)<0 or min(areas)<=0:raise ValueError('Invalid flat starting subdivision')
 return p0,{'route':route,'start_points':[[str(x) for x in v] for v in p0],
  'reduced_support_minimum':str(min(x for _,vals in reduced_proof for x in vals)),
  'endpoint_support_minimum':str(min(x for _,vals in end for x in vals)),
  'start_support_minimum':str(min(start_values)),
  'start_zero_supports':sum(x==0 for x in start_values),
  'start_area_squared_minimum':str(min(areas))}

def net_summary(p,cut):
 proof=check_net(p,cut)
 return {'fan_pairs':len(proof['shared_vertex_pairs']),
  'separated_pairs':len(proof['strict_separators']),
  'minimum_separator':str(min(F(x['gap_lower_bound']) for x in proof['strict_separators']))}

def certify(row):
 p=exact_points(row['points']);j=row['inserted_vertex']
 p0,geometry=morph_geometry(p,j,row['subdivision_edge'])
 answer={'geometry':geometry,'minimum_curvature':minimum(p,j),
  'initial_net':net_summary(p0,row['initial_cut']),'cover':[]}
 if 'overlap_pair' in row:
  net=develop(p,row['initial_cut'])
  answer['endpoint_overlap']=[inside(net[i],list(map(F,row['overlap_witness']))) for i in row['overlap_pair']]
 next_start=F(0)
 for section in row['cover']:
  cells=[]
  for lo,hi in section['cells']:
   lo,hi=F(lo),F(hi)
   if lo!=next_start or not lo<hi<=1:raise ValueError('Parameter cover has a gap, overlap, or reversed cell')
   q=[v[:] for v in p];q[j]=[I.bounds(x)+I.bounds(lo,hi)*(y-x) for x,y in zip(p0[j],p[j])]
   cells.append(net_summary(q,section['cut']));next_start=hi
  if not cells:raise ValueError('Empty cover section')
  answer['cover'].append({'cell_count':len(cells),'fan_pairs_per_cell':cells[0]['fan_pairs'],
   'separated_pairs_per_cell':cells[0]['separated_pairs'],
   'minimum_separator':str(min(F(c['minimum_separator']) for c in cells))})
 if next_start!=1:raise ValueError('Parameter cover does not reach the endpoint')
 return answer

def replay_saved():
 records=json.loads((ROOT/'results/bipyramid-morph.json').read_text())
 for row in records['examples']:
  fresh=json.loads(json.dumps(certify(row)))
  if fresh!=row['certificate']:raise ValueError('Stored certificate mismatch: '+row['id'])
 return {'examples':len(records['examples']),
  'closed_interval_cells':sum(len(s['cells']) for r in records['examples'] for s in r['cover']),
  'minimum_curvature_comparisons':6*len(records['examples']),
  'scope':'Only the two specified rational insertion paths; no universal existence claim.'}

if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
