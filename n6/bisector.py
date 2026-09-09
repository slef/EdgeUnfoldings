"""Check a failure of the slit-bisector sufficient condition for Lemma L.

This is a failure of one proposed separating line, not of the unfolding. The
ordinary all-pairs checker can independently verify the same net is simple.
"""
from itertools import combinations
from n6.certify import require,edge,tree_path
from n6.polycert import Geometry
from n6.intervals import sub,norm2
from n6.curvature import verify_order


def selected_flanks(cert,claim):
    """Validate the hull, cut tree, rankings, and slit-based ring once."""
    g=Geometry(cert);v=claim['apex'];u=claim['slit_vertex']
    require(len(g.faces)==8 and all(len(f)==3 for f in g.faces),'Expected triangular octahedron')
    adj={x:set() for x in range(6)}
    for f in g.faces:
        for a,b in combinations(f,2):adj[a].add(b);adj[b].add(a)
    require(all(len(xs)==4 for xs in adj.values()),'Not octahedral adjacency')
    w=next(x for x in range(6) if x!=v and x not in adj[v])
    require(u in adj[w],'Invalid slit vertex')
    require({edge(*e) for e in cert['cut_edges']}=={edge(v,x) for x in adj[v]}|{edge(w,u)},'Wrong cut tree')
    ranking=verify_order(g,[(v,x) for x in range(6) if x!=v]+[(u,x) for x in adj[w] if x!=u])
    nxt={}
    for f in g.faces:
        if w in f:
            i=f.index(w);nxt[f[(i+1)%3]]=f[(i+2)%3]
    ring=[u]
    while len(ring)<4:ring.append(nxt[ring[-1]])
    return g,v,w,u,ring,ranking


def opposite_flank_development(g,v,w,ring,side):
    lookup={frozenset(f):i for i,f in enumerate(g.faces)}
    require(side in ('first','last'),'Unknown flank petal')
    i,j=(0,3) if side=='last' else (3,0)
    root=lookup[frozenset((w,ring[i],ring[(i+1)%4]))]
    target=lookup[frozenset((v,ring[j],ring[(j+1)%4]))]
    path=tree_path(g.adj,root,target)
    A=g.develop(path[:1]);B=g.develop(path)
    return A,B,(ring[i],ring[(i+1)%4])


def verify(cert):
    claim=cert['bisector_failure'];g,v,w,u,ring,ranking=selected_flanks(cert,claim)
    side=claim['petal'];A,B,_=opposite_flank_development(g,v,w,ring,side)
    difference=norm2(sub(B[v],A[u]))-norm2(g.vector(u,v))
    require(difference.hi<0,'Bisector failure not certified')
    return dict(result='verified_failure_of_bisector_separator',petal=side,apex=v,antipode=w,slit_vertex=u,
                other_copy_distance_squared_minus_own_edge_squared=difference.pair(),curvature_order=ranking,
                scope='This particular bisector does not separate the flank petals; this is not a failure of Lemma L.')


def main():
    import argparse,json
    from pathlib import Path
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path);ap.add_argument('--bits',type=int,default=320)
    args=ap.parse_args();set_precision(args.bits)
    print(json.dumps(verify(json.loads(args.input.read_text())),indent=2))


if __name__=='__main__':main()
