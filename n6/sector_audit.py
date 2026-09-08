"""Verify that a particular sharpest-vertex sector strategy fails its radial test."""
from itertools import combinations
from n6.polycert import Geometry
from n6.curvature import verify_order
from n6.certify import require,tree_path
from n6.intervals import sub,det,norm2


def verify(cert):
    g=Geometry(cert);claim=cert['radial_obstruction'];v,w=claim['source'],claim['sector_vertex']
    a,b=claim['crossed_edge'];lookup={frozenset(f):i for i,f in enumerate(g.faces)}
    A=lookup[frozenset((v,a,b))];B=lookup[frozenset((w,a,b))]
    require(all(len(f)==3 for f in g.faces) and len(g.faces)==8,'Expected triangular octahedron')
    adj={t:set() for t in range(6)}
    for f in g.faces:
        for x,y in combinations(f,2):adj[x].add(y);adj[y].add(x)
    require(all(len(ns)==4 for ns in adj.values()) and v not in adj[w],'Wrong antipodal pair')
    ranking=verify_order(g,[(w,t) for t in range(6) if t!=w])
    q=g.develop((A,));r=g.develop((A,B));direction=sub(r[w],q[v])
    da=det(direction,sub(q[a],q[v]));db=det(direction,sub(q[b],q[v]))
    require((da*db).hi<0,'Path not certified to cross the base interior')
    length_squared=norm2(direction);margins={}
    for u in sorted(adj[w]):
        gap=norm2(g.vector(w,u))-length_squared
        require(gap.lo>0,'A neighbour may pass the radial condition')
        margins[str(u)]=gap.pair()
    return dict(result='verified_failure_of_sharpest_sector_radial_test',
                scope='The true shortest path is no longer than this valid two-face path, shorter than every w-neighbour edge. This refutes this sufficient strategy only.',
                source=v,sector_vertex=w,crossed_edge=[a,b],curvature_order=ranking,
                path_length_squared=length_squared.pair(),radial_squared_gaps=margins)


def main():
    import argparse,json
    from pathlib import Path
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    args=ap.parse_args();print(json.dumps(verify(json.loads(args.input.read_text())),indent=2))


if __name__=='__main__':main()
