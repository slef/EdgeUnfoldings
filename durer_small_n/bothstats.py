import numpy as np, collections, sys, itertools
from unfold import Polytope, unfold
from unfold2 import sat_pen
from gen import rand_points
from geostar import place, cross
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
def ang(p,F,x):
    i=F.index(x); a=p.P[F[(i+1)%3]]-p.P[x]; b=p.P[F[(i+2)%3]]-p.P[x]
    return np.arccos(np.clip(np.dot(a,b)/np.linalg.norm(a)/np.linalg.norm(b),-1,1))
rows=[]; cnt=0
while cnt<N:
    P=rand_points(6,rng)
    try: p=Polytope(P)
    except: continue
    if len(p.P)!=6 or len(p.faces)!=8 or tuple(sorted(p.deg.values()))!=(4,)*6: continue
    cnt+=1
    adj=collections.defaultdict(set)
    for a,b in p.edges: adj[a].add(b); adj[b].add(a)
    fidx={frozenset(f):i for i,f in enumerate(p.faces)}; hinge_index={(a,b):ei for ei,(f,g,a,b) in enumerate(p.E)}
    def curv(x): return 2*np.pi-sum(ang(p,F,x) for F in p.faces if x in F)
    for v in range(6):
        w=[x for x in range(6) if x!=v and x not in adj[v]][0]
        ring=[next(iter(adj[w]))]
        while len(ring)<4: ring.append([x for x in adj[w] if x not in ring and x in adj[ring[-1]]][0])
        star={tuple(sorted((v,u))) for u in adj[v]}
        e=[];f=[];conv=[];diag=[];good=[];om=[];nu=[]
        for i in range(4):
            u1,u2=ring[i],ring[(i+1)%4]; fV=fidx[frozenset((v,u1,u2))]; fW=fidx[frozenset((w,u1,u2))]
            e.append(ang(p,p.faces[fV],u1)+ang(p,p.faces[fW],u1)); f.append(ang(p,p.faces[fV],u2)+ang(p,p.faces[fW],u2))
            om.append(ang(p,p.faces[fW],w)); nu.append(ang(p,p.faces[fV],v))
            pos=place(p,[fW,fV]); W=pos[fW]; V=pos[fV]
            c=cross(V[v],W[w],W[u1])*cross(V[v],W[w],W[u2])<0 and cross(W[u1],W[u2],V[v])*cross(W[u1],W[u2],W[w])<0
            conv.append(c); diag.append(np.linalg.norm(V[v]-W[w]) if c else np.inf)
            cut=star|{tuple(sorted((w,u1)))}; tree=[hinge_index[q] for q in p.edges if q not in cut]
            posZ=unfold(p.faces,p.L,p.E,tree); worst=0
            for a,b in itertools.combinations(range(8),2):
                sh=set(p.faces[a])&set(p.faces[b])
                if any(np.linalg.norm(posZ[a][x]-posZ[b][x])<p.eps for x in sh): continue
                worst=max(worst,sat_pen(np.array([posZ[a][x] for x in p.faces[a]]),np.array([posZ[b][x] for x in p.faces[b]])))
            good.append(worst<=p.eps)
        j=int(np.argmin(diag))
        if not good[j] and not good[(j+1)%4]:
            k=lambda i: curv(ring[(j+i)%4]); kw=curv(w); kv=curv(v)
            r=lambda i: np.linalg.norm(p.P[w]-p.P[ring[(j+i)%4]]); l=lambda i: np.linalg.norm(p.P[v]-p.P[ring[(j+i)%4]])
            d=diag[j]
            rows.append(dict(kv=kv,kw=kw,k1=k(0),k2=k(1),k3=k(2),k4=k(3),
                e3=e[(j+2)%4],f4=f[(j+2)%4],om1=om[j],om2=om[(j+1)%4],om3=om[(j+2)%4],om4=om[(j+3)%4],
                nu1=nu[j],nu3=nu[(j+2)%4],d=d,path3=l(2)+r(2),path4=l(3)+r(3),r1=r(0),l1=l(0),r2=r(1),l2=l(1)))
print("both-fail cases:",len(rows))
keys=['kv','kw','k1','k2','k3','k4','e3','f4','om1','om2','om3','om4','nu1','nu3']
for kk in keys:
    a=np.array([rw[kk] for rw in rows]); print("%-4s min %.3f  median %.3f  max %.3f"%(kk,a.min(),np.median(a),a.max()))
a=np.array([rw['k1']+rw['kw'] for rw in rows]); print("k1+kw max %.3f"%a.max())
a=np.array([rw['k3']+rw['k4'] for rw in rows]); print("k3+k4 min %.3f"%a.min())
a=np.array([rw['om1']+rw['om3'] for rw in rows]); print("om1+om3 min %.3f max %.3f"%(a.min(),a.max()))
a=np.array([rw['d']/min(rw['path3'],rw['path4']) for rw in rows]); print("d/(min edge path via u3,u4) max %.3f"%a.max())
a=np.array([rw['d']/(rw['r1']+rw['l1']) for rw in rows]); print("d/(r1+l1) min %.3f max %.3f"%(a.min(),a.max()))
