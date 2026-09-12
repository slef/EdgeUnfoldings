"""Exact examples and algebra for the paired-pole theorem.

The universal geometry is written in PAIRED_POLE_RULE.md. The selector
checks uniform curvature orders; each returned net is independently replayed.
"""
from fractions import Fraction as F
from n6.certify import edge, require
from n6.curvature import interval_angle_le
from n6.polycert import Geometry, make_certificate, verify as all_pairs
from n6.polynomials import Poly
from n6.prism_paths import polygon_angle_product
from n6.trees import incidence


def wide_identities():
    faces = [(1,2+i,2+(i+1)%4) for i in range(4)]+[(0,2+(i+1)%4,2+i) for i in range(4)]
    n=16; angles={}; index=0
    for i,face in enumerate(faces):
        for v in face[:-1]:angles[i,v]=Poly.variable(n,index);index+=1
        angles[i,face[-1]]=1-sum(angles[i,v] for v in face[:-1])
    k={v:2-sum(angles[i,v] for i,f in enumerate(faces) if v in f) for v in range(6)}
    residuals=[]
    for v,w,start in ((0,1,4),(1,0,0)):
        for middle in range(4):
            eta=angles[start+(middle+2)%4,v]
            nu=angles[start+middle,v]
            lam=angles[start+(middle-1)%4,v]
            rho=angles[start+(middle+1)%4,v]
            base=[u for u in faces[start+middle] if u!=v]
            outside=[u for u in faces[start+(middle+2)%4] if u!=v]
            K=sum(k[u] for u in base)
            S=sum(2-k[u]-2*angles[start+(middle+2)%4,u] for u in outside)
            residuals += [2+K-2*lam-nu-((k[v]-k[w])+S+nu+2*rho),
                          2+K-2*rho-nu-((k[v]-k[w])+S+nu+2*lam)]
    require(all(q.is_zero() for q in residuals),'A paired-pole wider-cone identity failed')
    return dict(result='verified_exact_paired_pole_wide_identities',identities=len(residuals),
                independent_angle_indeterminates=n,geometric_proof_formally_verified=False)


def signature(g,v):
    if any(q.lo!=q.hi for p in g.p for q in p):return None
    p=[[q.lo for q in row] for row in g.p];result=[]
    for f in g.faces:
        if v not in f:continue
        i=f.index(v);a=[x-y for x,y in zip(p[f[i-1]],p[v])];b=[x-y for x,y in zip(p[f[(i+1)%len(f)]],p[v])]
        d=sum(x*y for x,y in zip(a,b));s=sum(x*x for x in a)*sum(x*x for x in b)
        require(s>0,'Degenerate corner')
        result.append(((d>0)-(d<0),d*d/s))
    return tuple(sorted(result))


def choose(g,pair=None):
    inc=incidence(g.faces);adj={v:{u for u in range(6) if edge(v,u) in inc} for v in range(6)}
    require((len(g.faces)==8 and all(len(f)==3 for f in g.faces)) or
            (len(g.faces)==7 and sorted(map(len,g.faces))==[3]*6+[4]),
            'Expected an octahedron or octahedron minus an edge')
    require(sorted(map(len,adj.values())) == ([4]*6 if len(g.faces)==8 else [3,3,4,4,4,4]),
            'Facet counts alone do not establish the required graph')
    pairs=[(v,w) for v in range(6) for w in range(v+1,6)
           if len(adj[v])==len(adj[w])==4 and w not in adj[v]]
    if pair is not None:
        pair=tuple(sorted(pair));require(pair in pairs,'Expected an opposite pair with all four incident edges original');pairs=[pair]
    require(bool(pairs),'No original degree-four opposite pair')
    totals={v:polygon_angle_product(g,v) for v in range(6)}
    signatures={v:signature(g,v) for v in range(6)}
    def ge(a,b):
        if a==b:return True
        if signatures[a] is not None and signatures[a]==signatures[b]:return True
        return interval_angle_le(totals[a],totals[b]) is True
    for a,b in pairs:
        for v,w in ((a,b),(b,a)):
            if not ge(v,w):continue
            equator=sorted(set(range(6))-{v,w})
            for c in equator:
                if not all(ge(c,u) for u in equator):continue
                cuts=sorted({edge(v,u) for u in adj[v]}|{edge(w,c)})
                return dict(source=v,fan=w,slit=c,equator=equator,cut_edges=[list(e) for e in cuts],
                    source_at_least_fan=True,equator_maximum=True,
                    upper_face_cap_bounds_required=False,curvature_difference_comparison_required=False,
                    curve_order_phases={str(u):[q.pair() for q in totals[u]] for u in range(6)})
    raise ValueError('No uniform paired-pole order certified on this domain')


def select(spec,pair=None):
    decision=choose(Geometry(spec),pair)
    clean={k:v for k,v in spec.items() if k not in ('selection','pair_witnesses','overlap_witness','angular_claims')}
    cert=make_certificate({**clean,'cut_edges':decision['cut_edges']})
    return dict(result='verified_paired_pole_example',selection=decision,certificate=cert,
                independent_whole_net=all_pairs(cert),geometric_proof_formally_verified=False,
                scope='Exact uniform order and whole-net replay on this explicit domain; universal proof is PAIRED_POLE_RULE.md.')
