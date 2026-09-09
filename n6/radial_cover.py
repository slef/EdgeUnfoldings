"""Exact local hypotheses for the mixed radial-cover unfolding theorem.

Each possible shortest-path patch may use a chord bound or a face-angle
bound. The checker invokes the written sector theorem; it does not prove
that every octahedron admits this cover or select a shortest path by sampling.
"""
import json
from pathlib import Path
from n6.polycert import Geometry
from n6.convex_patches import geometry_patches
from n6.curvature import angle_product, face_angle, cmul, conjugate, interval_angle_le
from n6.intervals import I, norm2
from n6.certify import require


def radial_angle_bound(omega, nu):
    """Decide omega+2*nu <= 2*pi for two triangle angles in (0,pi).

    Compare 2*nu with 2*pi-omega, both already in (0,2*pi). Return None
    when outward intervals cannot decide a sign; never accept that case.
    """
    return interval_angle_le(cmul(nu,nu),conjugate(omega))


def verify(spec):
    g=Geometry(spec); claim=spec['radial_cover']
    w,v,ring=claim['sector_vertex'],claim['source'],claim['equator']
    patches=geometry_patches(g,dict(apex=v,antipode=w,equator=ring))
    total=angle_product(g.p,g.faces,g.h,w)
    require(interval_angle_le(total,(I(-1),-I(3).sqrt())) is True,
            'Cannot certify sector-vertex curvature at least 2*pi/3')
    diagonal2=norm2(g.vector(w,v))
    gaps={u:diagonal2-norm2(g.vector(w,u)) for u in ring}
    short={u for u in ring if gaps[u].lo>=0}
    lookup={frozenset(f):i for i,f in enumerate(g.faces)}
    routes=[];choices=set()
    for patch in patches:
        a,b=patch['equator_edge']
        valid=all(r=='<' for r in patch['corner_relations_to_pi'])
        wi,vi=[lookup[frozenset((pole,a,b))] for pole in (w,v)]
        omega=face_angle(g.p,g.faces[wi],g.h[wi],w)
        nu=face_angle(g.p,g.faces[vi],g.h[vi],v)
        angle=radial_angle_bound(omega,nu)
        endpoints=[u for u in (a,b) if u in short]
        methods=[]
        if endpoints:methods.append('short_edge_against_pole_chord')
        if angle is True:methods.append('omega_plus_twice_nu_at_most_two_pi')
        if valid:
            require(bool(methods),'A possible shortest-path patch has no certified radial bound')
            choices.update(endpoints if endpoints else (a,b))
        routes.append(dict(patch=patch['index'],equator_edge=[a,b],
                           possible_shortest_path=valid,
                           corner_relations=patch['corner_relations_to_pi'],
                           certified_methods=methods,short_endpoints=endpoints,
                           face_angle_bound=angle,
                           angle_products=[[q.pair() for q in z] for z in (omega,nu)]))
    require(bool(choices),'No candidate: a strictly convex patch must exist')
    return dict(result='verified_radial_cover_hypotheses',source=v,sector_vertex=w,
                curvature_threshold='2*pi/3 (120 degrees)',routes=routes,
                candidate_slit_vertices=sorted(choices),
                diagonal_squared=diagonal2.pair(),
                squared_length_gaps={str(u):gap.pair() for u,gap in gaps.items()},
                conclusion='A shortest two-face pole-to-pole path has an endpoint u with |sector_vertex--u| at most its length. Cutting star(source) and sector_vertex--u gives a nonoverlapping edge unfolding.',
                scope='Exact hypotheses on this point or parameter region, invoking the written geometric theorem. No universal coverage or success of every candidate slit is claimed.')


def audit_failure(spec):
    """Certify that every eligible sector vertex fails this sufficient test.

    This says nothing against the full shortest-path sector criterion or
    edge unfoldability. A separate net certificate may succeed on this input.
    """
    g=Geometry(spec)
    adj={u:set().union(*(set(f)-{u} for f in g.faces if u in f)) for u in range(6)}
    require(all(len(row)==4 for row in adj.values()),'Expected octahedral graph')
    rows=[]
    for w in range(6):
        total=angle_product(g.p,g.faces,g.h,w)
        high=interval_angle_le(total,(I(-1),-I(3).sqrt()))
        require(high is not None,'Curvature threshold unresolved')
        if not high:
            rows.append(dict(vertex=w,reason='curvature_strictly_below_120_degrees'))
            continue
        v=next(x for x in range(6) if x!=w and x not in adj[w])
        nxt={}
        for face in g.faces:
            if w in face:
                j=face.index(w);nxt[face[(j+1)%3]]=face[(j+2)%3]
        ring=[min(adj[w])]
        for _ in range(3):ring.append(nxt[ring[-1]])
        patches=geometry_patches(g,dict(apex=v,antipode=w,equator=ring))
        lookup={frozenset(f):i for i,f in enumerate(g.faces)}
        diagonal2=norm2(g.vector(w,v));witness=None
        for patch in patches:
            if any(r!='<' for r in patch['corner_relations_to_pi']):continue
            a,b=patch['equator_edge']
            gaps=[norm2(g.vector(w,u))-diagonal2 for u in (a,b)]
            wi,vi=[lookup[frozenset((pole,a,b))] for pole in (w,v)]
            omega=face_angle(g.p,g.faces[wi],g.h[wi],w)
            nu=face_angle(g.p,g.faces[vi],g.h[vi],v)
            if all(d.lo>0 for d in gaps) and radial_angle_bound(omega,nu) is False:
                witness=dict(vertex=w,source=v,reason='a_valid_patch_fails_both_local_tests',
                             equator_edge=[a,b],squared_spokes_minus_chord=[d.pair() for d in gaps],
                             face_angle_bound='omega+2*nu > 2*pi',
                             angle_products=[[q.pair() for q in z] for z in (omega,nu)])
                break
        require(witness is not None,'No failing patch certified at eligible sector vertex')
        rows.append(witness)
    return dict(result='verified_failure_of_all_high_vertex_radial_covers',vertices=rows,
                scope='The mixed chord/face-angle sufficient criterion fails at every eligible vertex. No failure of the full sector criterion or of edge unfoldability is asserted.')


if __name__=='__main__':
    import argparse
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('certificate',type=Path)
    ap.add_argument('--audit-failure',action='store_true')
    args=ap.parse_args();spec=json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits',192))
    print(json.dumps((audit_failure if args.audit_failure else verify)(spec),indent=2))
