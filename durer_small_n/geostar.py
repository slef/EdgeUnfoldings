import numpy as np, collections, sys, itertools
from unfold import Polytope, unfold
from unfold2 import sat_pen
from gen import rand_points
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
def rot(th): c,s=np.cos(th),np.sin(th); return np.array([[c,-s],[s,c]])
def place(p, seq):
    pos={seq[0]:dict(p.L[seq[0]])}
    for f,g in zip(seq,seq[1:]):
        u,x=sorted(set(p.faces[f])&set(p.faces[g])); A,B=pos[f][u],pos[f][x]; a,b=p.L[g][u],p.L[g][x]
        th=np.arctan2(*(B-A)[::-1])-np.arctan2(*(b-a)[::-1]); R=rot(th); pos[g]={y:R@(p.L[g][y]-a)+A for y in p.L[g]}
    return pos
def cross(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
def main():
  stats=collections.Counter(); cnt=0
  while cnt<N:
      P=rand_points(6,rng)
      try: p=Polytope(P)
      except: continue
      if len(p.P)!=6 or len(p.faces)!=8 or tuple(sorted(p.deg.values()))!=(4,)*6: continue
      cnt+=1
      adj=collections.defaultdict(set)
      for a,b in p.edges: adj[a].add(b); adj[b].add(a)
      fidx={frozenset(f):i for i,f in enumerate(p.faces)}
      hinge_index={(a,b):ei for ei,(f,g,a,b) in enumerate(p.E)}
      for v in range(6):
          w=[x for x in range(6) if x!=v and x not in adj[v]][0]
          ring=[next(iter(adj[w]))]
          while len(ring)<4: ring.append([x for x in adj[w] if x not in ring and x in adj[ring[-1]]][0])
          star={tuple(sorted((v,u))) for u in adj[v]}
          conv=[]; diag=[]; goodZ=[]; geo_simple=[]
          for i in range(4):
              u1,u2=ring[i],ring[(i+1)%4]
              fV=fidx[frozenset((v,u1,u2))]; fW=fidx[frozenset((w,u1,u2))]
              pos=place(p,[fW,fV]); W=pos[fW]; V=pos[fV]
              # convex iff segment v w crosses open segment u1 u2
              c=cross(V[v],W[w],W[u1])*cross(V[v],W[w],W[u2])<0 and cross(W[u1],W[u2],V[v])*cross(W[u1],W[u2],W[w])<0
              conv.append(c); diag.append(np.linalg.norm(V[v]-W[w]) if c else np.inf)
              # pendant unfolding Z_i
              cut=star|{tuple(sorted((w,u1)))}; tree=[hinge_index[e] for e in p.edges if e not in cut]
              posZ=unfold(p.faces,p.L,p.E,tree)
              bad=False
              for f,g in itertools.combinations(range(8),2):
                  sh=set(p.faces[f])&set(p.faces[g])
                  if any(np.linalg.norm(posZ[f][x]-posZ[g][x])<p.eps for x in sh): continue
                  if sat_pen(np.array([posZ[f][x] for x in p.faces[f]]),np.array([posZ[g][x] for x in p.faces[g]]))>p.eps: bad=True; break
              goodZ.append(not bad)
              # geodesic star unfolding through edge i (if convex): pieces = Z_i pieces with Q_i split along vw,
              # u1-half rotated about w by -kappa_w to the other side of the gap. Test simplicity.
              if c:
                  # in Z_i frame: fan opened at w u1. Build pieces
                  pieces=[]
                  for f in range(8):
                      if f in (fW,fV): continue
                      pieces.append(np.array([posZ[f][x] for x in p.faces[f]]))
                  Wp={x:posZ[fW][x] for x in p.faces[fW]}; Vp={x:posZ[fV][x] for x in p.faces[fV]}
                  wpt=Wp[w]; 
                  # curvature at w = 2pi - fan angle
                  fan=0
                  for f in range(8):
                      F=p.faces[f]
                      if w in F:
                          i0=F.index(w); a=p.P[F[(i0+1)%3]]-p.P[w]; b=p.P[F[(i0+2)%3]]-p.P[w]
                          fan+=np.arccos(np.clip(np.dot(a,b)/np.linalg.norm(a)/np.linalg.norm(b),-1,1))
                  kw=2*np.pi-fan
                  # which rotation direction: the fan occupies angles from ray w->u1 going CCW (faces CCW). Rotating by -kw moves u1-side across the gap.
                  # determine sign: the other copy u1' is at angle(ray w u1) - kw or + kw; check via posZ of face W41 (contains u1 copy)
                  fW4=[f for f in range(8) if w in p.faces[f] and u1 in p.faces[f] and f!=fW][0]
                  u1p=posZ[fW4][u1]; ang=lambda q: np.arctan2(q[1]-wpt[1],q[0]-wpt[0])
                  d=(ang(u1p)-ang(Wp[u1])+np.pi)%(2*np.pi)-np.pi; R=rot(d)  # rotate u1-side by d so that u1 -> u1'
                  A1=np.array([wpt,Wp[u1],Vp[v]]); A2=np.array([Vp[v],Vp[u1],Wp[u1]])  # w u1 v (triangle) split into W-part and V-part: w u1 v_diag? 
                  # halves: u1-side: triangle w u1 y? no -- split along diagonal v w: u1-side = triangle w u1 v (contains parts of both faces). 
                  # pieces: triangle w u1 v ; triangle w v u2  (each is union of subpieces of W and V, convex)
                  T1=np.array([wpt,Wp[u1],Vp[v]]); T2=np.array([wpt,Vp[v],Wp[u2]])
                  T1r=(T1-wpt)@R.T+wpt
                  allp=pieces+[T2,T1r]
                  simple=True
                  for X,Y in itertools.combinations(allp,2):
                      # skip pairs sharing a point
                      if any(np.linalg.norm(x-y)<p.eps for x in X for y in Y): continue
                      if sat_pen(X,Y)>p.eps: simple=False; break
                  geo_simple.append(simple)
              else: geo_simple.append(None)
          j=int(np.argmin(diag))  # shortest geodesic edge
          stats['cases']+=1; stats['#convex Q = %d'%sum(conv)]+=1
          for i in range(4):
              if conv[i]:
                  stats['geodesic-star through convex edge: simple' if geo_simple[i] else 'geodesic-star through convex edge: OVERLAP']+=1
                  if i!=j: stats['non-shortest geodesic star: simple' if geo_simple[i] else 'non-shortest geodesic star: OVERLAP']+=1
          if not goodZ[j] and not goodZ[(j+1)%4]:
              stats['both shortest-edge pendants fail']+=1
              others=[(k,conv[k],goodZ[k]) for k in range(4) if k not in (j,(j+1)%4)]
              stats['   ...then pattern (edge k: convex?, Z_k good?) '+str(others)]+=1
  return stats
if __name__=='__main__':
    stats=main()
    for k,c in sorted(stats.items()): print(k,c)
