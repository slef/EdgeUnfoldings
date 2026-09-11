"""Exact hypotheses for the local curvature-gate theorem in Lemma L.

LEMMA_L_CURVATURE_GATE.md contains the proof. This checker treats only the
three slit-side pairs; a full-net certificate is a separate result.
"""
import json
from pathlib import Path

from n6.certify import edge, require
from n6.curvature import angle_product, conjugate, verify_order
from n6.half_fan import setup
from n6.patch_budget import pole_angles_and_leans, sum_le
from n6.polycert import Geometry
from n6.regimes import curvature_sum_band

LOCAL_PAIRS = ('first_petal/last_petal', 'first_petal/last_fan', 'last_petal/first_fan')


def classify_routes(band, first, last):
    """The theorem's conclusions, distinct from direct cone comparisons."""
    require(first in ('', 'F', 'B') and last in ('', 'F', 'B'), 'Invalid flank directions')
    require(not (first == 'B' and last == 'F'), 'Both slit corners cannot be reflex')
    require(band in (None, 'K<pi', 'K=pi', 'pi<K<2pi', 'K=2pi', 'K>2pi'), 'Invalid curvature band')
    through_excluded = band in ('K<pi', 'K=pi')
    slit_excluded = band in ('K=pi', 'pi<K<2pi', 'K=2pi', 'K>2pi')
    # Absence of an extension rules out that route without a curvature bound.
    if first != 'B' and last != 'F':
        slit_excluded = True
    if first != 'F' and last != 'B':
        through_excluded = True
    if first == 'F' and last == 'B' and band in ('K<pi', 'K=pi', 'pi<K<2pi', 'K=2pi'):
        through_excluded = True
    first_can_enter = (not slit_excluded and first == 'B') or (not through_excluded and first == 'F')
    last_can_enter = (not slit_excluded and last == 'F') or (not through_excluded and last == 'B')
    remaining = []
    if first_can_enter or last_can_enter:
        remaining.append(LOCAL_PAIRS[0])
    if first_can_enter:
        remaining.append(LOCAL_PAIRS[1])
    if last_can_enter:
        remaining.append(LOCAL_PAIRS[2])
    return dict(across_slit_route_excluded=slit_excluded,
                through_fan_route_excluded=through_excluded,
                remaining_local_pairs=remaining,
                local_pairs_proved_safe=[p for p in LOCAL_PAIRS if p not in remaining],
                all_local_pairs_by_gate=not remaining)


def analyze(spec):
    claim = spec['local_gate']
    g = Geometry(spec)
    v, w, ring = claim['source'], claim['fan_vertex'], claim['equator']
    k = claim['slit_index']
    require(type(k) is int and 0 <= k < 4, 'Invalid slit index')
    patches, directions, lookup = setup(g, v, w, ring)
    u = ring[k]
    wanted = {edge(v, x) for x in ring} | {edge(w, u)}
    require({edge(*e) for e in spec['cut_edges']} == wanted, 'Cuts disagree with the stated slit')
    ranked = claim.get('check_rankings', True)
    require(type(ranked) is bool, 'Invalid ranking flag')
    ranking = verify_order(g, [(v, x) for x in range(6) if x != v] +
                              [(u, x) for x in ring if x != u]) if ranked else None
    totals = {p: angle_product(g.p, g.faces, g.h, p) for p in (u, w)}
    band = curvature_sum_band(totals[u], totals[w])
    first, last = directions[k], directions[(k-1) % 4]
    routes = classify_routes(band, first, last)
    angles, leans = pole_angles_and_leans(g, v, w, ring, directions, lookup)
    L = lambda i, direction: [leans[w][i % 4]] if directions[i % 4] == direction else []
    slit_test = sum_le(L(k, 'B') + L(k-1, 'F'), [conjugate(totals[w])])
    through_test = sum_le(L(k, 'F') + L(k-1, 'B'),
                          [angles[w][(k+1) % 4], angles[w][(k+2) % 4]])
    return dict(result='verified_local_curvature_gate_analysis', source=v, fan_vertex=w,
                slit_vertex=u, equator=ring, patches=patches, directions=directions,
                first_flank_direction=first, last_flank_direction=last,
                curvature_sum_band=band, curvature_rankings_checked=ranked,
                curvature_order=ranking, **routes,
                across_slit_cone_test=slit_test, through_fan_cone_test=through_test,
                all_local_pairs_by_direct_cone_tests=slit_test is True and through_test is True,
                full_lemma_L_proved=False, full_net_claimed=False,
                scope='The written theorem excludes the listed routes and local pairs on this point or region. A failed sufficient cone test does not prove face overlap. This checker invokes only the gate theorem; the full selected-rule result is proved separately in LEMMA_L_PROOF.md.')


def verify(spec):
    report = analyze(spec)
    require(report['all_local_pairs_by_gate'], 'The curvature gate leaves local pairs open')
    report['result'] = 'verified_local_pairs_by_curvature_gate'
    return report


if __name__ == '__main__':
    import argparse
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    ap.add_argument('--analyze', action='store_true')
    args = ap.parse_args()
    spec = json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits', 240))
    print(json.dumps((analyze if args.analyze else verify)(spec), indent=2))
