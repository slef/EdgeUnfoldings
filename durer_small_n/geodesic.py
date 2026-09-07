import numpy as np, itertools
from unfold import unfold

def seg_cross(a,b,c,d,eps=1e-12):
    """does segment ab cross open segment cd (strictly inside cd)?"""
    def cr(p,q,r): return (q[0]-p[0])*(r[1]-p[1])-(q[1]-p[1])*(r[0]-p[0])
    d1,d2=cr(c,d,a),cr(c,d,b); d3,d4=cr(a,b,c),cr(a,b,d)
    return d1*d2<0 and d3*d4<0

def shortest_vw(p, v, w, maxlen=5):
    """Shortest surface path from vertex v to vertex w through a sequence of faces.
    Returns (length, face sequence, crossed edges)."""
    faces=p.faces; adj={}
    for ei,(f,g,u,x) in enumerate(p.E):
        adj.setdefault(f,[]).append((g,u,x,ei)); adj.setdefault(g,[]).append((f,u,x,ei))
    best=(np.inf,None,None)
    if w in {u for f in faces for u in f if v in f and u!=v}:  # adjacent: the edge
        return (np.linalg.norm(p.P[v]-p.P[w]), None, None)
    def rec(seq, crossed, tree_edges):
        nonlocal best
        f=seq[-1]
        if w in faces[f]:
            pos=unfold(faces,p.L,p.E,tree_edges) if tree_edges else None
            # place faces of seq only: build a mini unfold via full unfold of a tree containing seq edges
            return
        if len(seq)>=maxlen: return
        for g,u,x,ei in adj[f]:
            if g in seq: continue
            rec(seq+[g], crossed+[(u,x)], tree_edges+[ei])
    # simpler: enumerate face sequences, and unfold them directly
    def place(seq):
        pos={seq[0]:dict(p.L[seq[0]])}
        for f,g in zip(seq,seq[1:]):
            u,x=sorted(set(faces[f])&set(faces[g]))
            A,B=pos[f][u],pos[f][x]; a,b=p.L[g][u],p.L[g][x]
            th=np.arctan2(*(B-A)[::-1])-np.arctan2(*(b-a)[::-1]); c,s=np.cos(th),np.sin(th)
            R=np.array([[c,-s],[s,c]]); pos[g]={y:R@(p.L[g][y]-a)+A for y in p.L[g]}
        return pos
    def rec2(seq):
        nonlocal best
        f=seq[-1]
        if w in faces[f]:
            pos=place(seq); a=pos[seq[0]][v]; b=pos[f][w]
            ok=True
            for i,(ff,gg) in enumerate(zip(seq,seq[1:])):
                u,x=sorted(set(faces[ff])&set(faces[gg]))
                if not seg_cross(a,b,pos[ff][u],pos[ff][x]): ok=False; break
            if ok:
                L=np.linalg.norm(b-a)
                if L<best[0]: best=(L,list(seq),[tuple(sorted(set(faces[ff])&set(faces[gg]))) for ff,gg in zip(seq,seq[1:])])
            return
        if len(seq)>=maxlen: return
        for g,u,x,ei in adj[f]:
            if g not in seq: rec2(seq+[g])
    for f in range(len(faces)):
        if v in faces[f]: rec2([f])
    return best
