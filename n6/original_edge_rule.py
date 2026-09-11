"""Exact hypotheses for ORIGINAL_EDGE_RULE.md on original polygonal facets.

This invokes a written geometric argument; it is not a formal proof checker.
Unresolved interval comparisons are never accepted. A failed sufficient
predicate is not an overlap certificate.
"""
from n6.certify import edge, require
from n6.curvature import cmul, conjugate, cdet
from n6.flat_octahedron import original_candidates, curvature_bands
from n6.intervals import I, norm2
from n6.polycert import Geometry
from n6.prism_paths import polygon_angle_product
from n6.regimes import positive_angles_pi


def ring_for(family, v, w, c):
    full=set(map(tuple,family['original_edges']+family['artificial_diagonals']))
    equator=set(range(6))-{v,w};require(c in equator,'Slit outside equator')
    ring=[c]
    while len(ring)<4:
        choices=[x for x in equator-set(ring) if edge(ring[-1],x) in full]
        require(bool(choices),'Broken equator cycle');ring.append(min(choices))
    require(edge(ring[-1],c) in full,'Equator does not close')
    return ring


def sum_pi(totals,bands,vertices):
    """Compare a positive sum of original curvatures with pi; repeats allowed."""
    require(bool(vertices),'Empty curvature sum')
    if any(bands[x]=='>' for x in vertices):return '>'
    if any(bands[x]=='=' for x in vertices):return '=' if len(vertices)==1 else '>'
    if any(bands[x] is None for x in vertices):return None
    return positive_angles_pi([conjugate(totals[x]) for x in vertices])


def small_fan_budget(totals,bands,v,w,c):
    """Compare kappa_c+kappa_w with Gamma_v/2, without inverse trig or wrap."""
    band=sum_pi(totals,bands,[c,w])
    if band in ('>','='):return '>'  # Every genuine vertex has Gamma_v/2<pi.
    if band is None or bands[v] is None:return None
    if bands[v]=='=':half=(I(0),I(1))
    else:
        x,y=totals[v];length=norm2((x,y)).sqrt()
        cosine=((length+x)/2).sqrt();sine=((length-x)/2).sqrt()
        half=(cosine if bands[v]=='>' else -cosine,sine)
    angle=cmul(conjugate(totals[c]),conjugate(totals[w]))
    det=cdet(angle,half)
    if det.hi<0:return '>'
    if det.lo>0:return '<'
    if det.lo==det.hi==0:return '='
    return None


def predicates(g,t,family,totals=None,bands=None):
    if totals is None:totals={x:polygon_angle_product(g,x) for x in range(6)}
    if bands is None:bands=curvature_bands(g)
    v,w,c=(t[x] for x in ('source','fan','slit'));ring=ring_for(family,v,w,c)
    _,a,d,b=ring
    sums={
        'local_slit': [c,c,w],
        'first_cut': [a,c,w,w],
        'last_cut': [b,c,w,w],
        'first_no_wrap': [v,a,d],
        'last_no_wrap': [v,d,b],
    }
    comparisons={name:sum_pi(totals,bands,vertices) for name,vertices in sums.items()}
    comparisons['small_fan']=small_fan_budget(totals,bands,v,w,c)
    accepted=bands[w] in ('<','=') and all(x in ('>','=') for x in comparisons.values())
    return dict(**t,equator=ring,fan_curvature_comparison=bands[w],
                curvature_sum_comparisons=comparisons,accepted=accepted)


def verify(spec):
    g=Geometry(spec);family,trees=original_candidates(g.faces)
    cuts=sorted(edge(*e) for e in spec['cut_edges'])
    choices=[t for t in trees if t['cuts']==cuts]
    require(bool(choices),'Expected an original degree-four star and original fifth edge')
    bands=curvature_bands(g);totals={x:polygon_angle_product(g,x) for x in range(6)}
    for t in choices:
        report=predicates(g,t,family,totals,bands)
        if report['accepted']:
            return dict(result='verified_original_edge_curvature_budget_rule',**report,
                type=family['type'],curvature_comparisons_with_pi=bands,
                original_faces_remain_whole=True,whole_net_safe_by_written_theorem=True,
                full_n6_proved=False,proof='ORIGINAL_EDGE_RULE.md',
                scope='Exact sufficient hypotheses on this explicit original-face domain. The written proof is not formally verified. Numerical samples are not premises.')
    raise ValueError('Original-edge curvature budgets are not certified')


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    args=ap.parse_args();spec=json.loads(args.input.read_text());set_precision(spec.get('suggested_fractional_bits',240))
    print(json.dumps(verify(spec),indent=2))
