"""Exact fixed choices for PRISM_COMPLEMENTARY_ROUTES.md, not a full prism proof."""
from n6.certify import require
from n6.families import PRISM_FACES
from n6.polycert import Geometry
from n6.flat_octahedron import original_candidates,curvature_bands,verify_fixed_tree
from n6.prism_paths import polygon_angle_product
from n6.original_edge_rule import sum_pi
from n6.cofacial_star_reduction import verify_case_B


def select(spec):
    g=Geometry(spec)
    require({frozenset(f) for f in g.faces}=={frozenset(f) for f in PRISM_FACES},
            'Expected the stated prism labels')
    bands=curvature_bands(g);totals={x:polygon_angle_product(g,x) for x in range(6)}
    require(all(bands[x] in ('<','=') for x in (2,5)),'Both fan curvatures <=pi must be certified')
    fan_sum=sum_pi(totals,bands,[2,5]);require(fan_sum in ('>','='),'Combined fan curvature >=pi must be certified')
    _,trees=original_candidates(g.faces)
    for t in trees:
        chosen={**spec,'cut_edges':t['cuts']}
        try:proof=verify_case_B(chosen);branch='complementary_route_Case_B'
        except ValueError:
            try:proof=verify_fixed_tree(chosen);branch='direct_source_threshold'
            except ValueError:continue
        return dict(result='verified_prism_complementary_route',branch=branch,
                    cut_edges=[list(e) for e in t['cuts']],fixed_tree_proof=proof,
                    curvature_comparisons_with_pi=bands,fan_curvature_sum_comparison=fan_sum,
                    whole_original_net_safe=True,full_prism_proved=False,
                    proof='PRISM_COMPLEMENTARY_ROUTES.md')
    raise ValueError('No uniform fixed choice resolved on this exact domain; the written existence proof is pointwise')
