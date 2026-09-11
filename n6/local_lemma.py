"""Verify the hypotheses of the complete geometric Lemma L proof.

The universal argument is LEMMA_L_PROOF.md. It needs only the source/fan
pole curvature order and a maximum-curvature equator slit. Independent
cone and cut-edge checks can illustrate it on exact coordinate regions.
"""
import json
from pathlib import Path

from n6.curvature import verify_order
from n6.intervals import dot
from n6.local_gate import analyze as gate_analysis, LOCAL_PAIRS
from n6.polycert import Geometry


def verify(spec):
    gate = gate_analysis(spec)
    claim = spec['local_gate']
    v, w, ring, k = (claim[n] for n in ('source', 'fan_vertex', 'equator', 'slit_index'))
    u = ring[k]
    g = Geometry(spec)
    order = verify_order(g, [(v, w)]+[(u, x) for x in ring if x != u])
    beta_dot = dot(g.vector(v, w), g.vector(v, u))
    beta_case = ('nonobtuse' if beta_dot.lo >= 0 else 'obtuse' if beta_dot.hi < 0
                 else 'both cases may occur in this interval; both are proved')
    return dict(result='verified_lemma_L_hypotheses',
                source=v, fan_vertex=w, slit_vertex=u, equator=ring,
                curvature_order=order, source_maximum_among_all_six_required=False,
                required_selections='source curvature >= fan curvature; slit curvature >= every equator curvature',
                original_pole_triangle_angle_at_source=beta_case,
                original_pole_triangle_dot_product=beta_dot.pair(),
                curvature_sum_band=gate['curvature_sum_band'],
                independent_through_fan_cone_check=gate['through_fan_cone_test'],
                all_three_local_pairs_proved=True, local_pairs=list(LOCAL_PAIRS),
                universal_proof='LEMMA_L_PROOF.md', full_net_claimed=False,
                scope='The complete geometric theorem proves these three pairs throughout this point or region. The six far pairs, full octahedron, and n=6 theorem remain separate obligations.')


if __name__ == '__main__':
    import argparse
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    args = ap.parse_args()
    spec = json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits', 240))
    print(json.dumps(verify(spec), indent=2))
