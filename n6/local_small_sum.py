"""Exact hypotheses and optional cut-edge separators for Lemma L's small-sum branch.

LEMMA_L_SMALL_SUM.md is the universal geometric proof. The hypothesis checker
does not promote either local safety or a coordinate family to a whole-net or
full-L claim. No floating-point arithmetic is used.
"""
import json
from pathlib import Path

from n6.certify import require, tree_path
from n6.curvature import verify_order
from n6.intervals import sub, det
from n6.local_gate import analyze as gate_analysis, LOCAL_PAIRS
from n6.polycert import Geometry


def verify(spec):
    gate = gate_analysis(spec)
    require(gate['curvature_sum_band'] in ('K<pi', 'K=pi'),
            'The small-sum theorem does not settle this curvature branch')
    claim = spec['local_gate']
    ring = claim['equator']
    u = ring[claim['slit_index']]
    # The theorem needs this ranking even if the original gate checker was
    # explicitly told not to check the stronger pair of selection rules.
    order = verify_order(Geometry(spec), [(u, x) for x in ring if x != u])
    return dict(result='verified_local_small_sum_theorem',
                curvature_sum_band=gate['curvature_sum_band'],
                source=claim['source'], fan_vertex=claim['fan_vertex'], slit_vertex=u,
                slit_curvature_order=order,
                source_maximum_required=False,
                all_three_local_pairs_proved=True, local_pairs=list(LOCAL_PAIRS),
                angular_gate_alone_suffices=gate['all_local_pairs_by_direct_cone_tests'],
                full_lemma_L_proved=False, full_net_claimed=False,
                scope='The written theorem proves all three local pairs throughout this point or region. This checker invokes only the small-sum theorem; the complementary branch is proved separately in LEMMA_L_PROOF.md.')


def verify_cut_separator(spec):
    """Independently check the predicted line on a slit-inward example or box."""
    theorem = verify(spec)
    gate = gate_analysis(spec)
    claim = spec['local_gate']
    v, w, ring, k = (claim[n] for n in ('source', 'fan_vertex', 'equator', 'slit_index'))
    if gate['first_flank_direction'] == 'B':
        i, j, side = k, (k-1) % 4, 'first'
    else:
        require(gate['last_flank_direction'] == 'F', 'No inward corner at the slit')
        i, j, side = (k-1) % 4, k, 'last'
    g = Geometry(spec)
    lookup = {frozenset(f): fi for fi, f in enumerate(g.faces)}
    own = lookup[frozenset((v, ring[i], ring[(i+1) % 4]))]
    u = ring[k]
    face = g.faces[own]
    a, b = next((a, b) for a, b in zip(face, face[1:]+face[:1]) if {a, b} == {u, v})
    base = g.develop([own])
    direction = sub(base[b], base[a])
    third = next(x for x in face if x not in (a, b))
    require(det(direction, sub(base[third], base[a])).lo > 0, 'Own petal orientation unresolved')
    checks = []
    for pole in (w, v):
        target = lookup[frozenset((pole, ring[j], ring[(j+1) % 4]))]
        placement = g.develop(tree_path(g.adj, own, target))
        signs = {str(x): det(direction, sub(p, base[a])) for x, p in placement.items()}
        require(all(s.hi < 0 for s in signs.values()), 'Cut-edge separator not certified')
        checks.append(dict(face=target, vertex_determinants={x: s.pair() for x, s in signs.items()}))
    return dict(result='verified_local_cut_edge_separator', theorem=theorem,
                inward_petal=side, oriented_cut_edge=[a, b], own_face=own,
                opposite_face_checks=checks,
                scope='The inward petal lies left of this line; both opposite faces lie strictly right. These exact checks illustrate the universal small-sum proof on the specified coordinates or region.')


if __name__ == '__main__':
    import argparse
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    ap.add_argument('--cut-separator', action='store_true')
    args = ap.parse_args()
    spec = json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits', 240))
    print(json.dumps((verify_cut_separator if args.cut_separator else verify)(spec), indent=2))
