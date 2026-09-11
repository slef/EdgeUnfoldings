"""Exact hypotheses and fixed choices for MINUS_COMPLEMENTARY_SOURCES.md.

The written angle-sum proof guarantees pointwise existence. Selecting one
fixed tree on a whole parameter region requires a uniform exact check below.
"""
from n6.certify import require
from n6.families import MINUS_FACES
from n6.polycert import Geometry
from n6.flat_octahedron import curvature_bands,original_candidates,verify_fixed_tree
from n6.cofacial_star_reduction import verify_case_A,verify_case_B


def select(spec,corner=None):
    g=Geometry(spec)
    require({frozenset(f) for f in g.faces}=={frozenset(f) for f in MINUS_FACES},
            'Expected the stated original minus-edge vertex labels')
    bands=curvature_bands(g)
    from n6.prism_paths import polygon_angle_product
    from n6.original_edge_rule import sum_pi
    totals={x:polygon_angle_product(g,x) for x in range(6)}
    gates={c:{v:sum_pi(totals,bands,[c,v]) for v in (0,1)} for c in (2,3)}
    if corner is None:corner=next((c for c in (2,3) if all(x in ('>','=') for x in gates[c].values())),None)
    require(corner in (2,3) and all(x in ('>','=') for x in gates[corner].values()),
            'Both corner-plus-fan curvature gates must be certified')
    _,trees=original_candidates(g.faces);attempts=[]
    for t in trees:
        if t['source'] not in (0,1) or bands[t['source']] not in ('>','='):continue
        try:proof=verify_fixed_tree({**spec,'cut_edges':t['cuts']})
        except ValueError:continue
        return dict(result='verified_minus_sharp_corner_choice',route_corner=corner,corner_gate_comparisons=gates[corner],
                    cut_edges=[list(e) for e in t['cuts']],source=t['source'],
                    branch='existing_high_source',fixed_tree_proof=proof,
                    curvature_comparisons_with_pi=bands,whole_original_net_safe=True,
                    proof='MINUS_COMPLEMENTARY_SOURCES.md',full_type_proof='MINUS_EDGE_PROOF.md')
    require(bands[0]=='<' and bands[1]=='<','The low-fan alternative is unresolved on this region')
    choices=[t for t in trees if t['source'] in (0,1) and t['slit']==corner]
    require(len(choices)==2,'Expected the two complementary original source choices')
    for t in choices:
        chosen={**spec,'cut_edges':t['cuts']}
        try:proof=verify_case_B(chosen);branch='residual_Case_B'
        except ValueError:
            try:proof=verify_case_A(chosen)
            except ValueError:
                attempts.append(dict(source=t['source'],result='no_uniform_pair_test_certified'));continue
            if not proof['earlier_two_angle_condition']:
                attempts.append(dict(source=t['source'],result='two_angle_choice_not_certified'));continue
            branch='complementary_two_angle_Case_A'
        return dict(result='verified_minus_sharp_corner_choice',route_corner=corner,corner_gate_comparisons=gates[corner],
                    cut_edges=[list(e) for e in t['cuts']],source=t['source'],branch=branch,
                    fixed_tree_proof=proof,earlier_choices=attempts,
                    curvature_comparisons_with_pi=bands,whole_original_net_safe=True,
                    proof='MINUS_COMPLEMENTARY_SOURCES.md',full_type_proof='MINUS_EDGE_PROOF.md',
                    scope='One fixed original tree satisfies the written theorem throughout this exact domain. The universal existence proof does not assume a uniform tree on arbitrary regions.')
    raise ValueError('The written existence theorem applies, but no uniform fixed choice was resolved on this interval domain')


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    ap.add_argument('--corner',type=int,choices=[2,3]);args=ap.parse_args()
    spec=json.loads(args.input.read_text());set_precision(spec.get('suggested_fractional_bits',240))
    print(json.dumps(select(spec,args.corner),indent=2))
