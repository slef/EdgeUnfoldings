"""Exact domain checks of the separate face-cap octahedron rule.

The universal selection proof is OCTA_FACE_CAP_RULE.md. This module checks
its choices and independently verifies all 28 pairs on an explicit domain.
"""
from fractions import Fraction as F

from n6.certify import edge, require
from n6.curvature import (cmul, conjugate, interval_angle_le,
                          point_angle_signature, verify_order)
from n6.flat_octahedron import curvature_bands, exact_polygon_angle_sum_pi
from n6.intervals import I
from n6.polycert import Geometry, make_certificate, verify as all_pairs
from n6.prism_paths import polygon_angle_product
from n6.regimes import positive_angles_pi
from n6.trees import incidence


def select_curvatures(values, opposite_pairs=((0, 1), (2, 3), (4, 5))):
    """Rational-angle audit of the universal selection; angles are in units of pi."""
    k = tuple(F(q) for q in values)
    require(len(k) == 6 and all(0 < q < 2 for q in k) and sum(k) == 4,
            'Expected six positive curvatures below 2*pi with total 4*pi')
    require(len(opposite_pairs) == 3 and all(len(pair) == 2 for pair in opposite_pairs) and
            sorted(v for pair in opposite_pairs for v in pair) == list(range(6)),
            'Expected three disjoint opposite pairs')
    c = max(range(6), key=lambda x: k[x])
    remaining = [tuple(sorted(pair, key=lambda x: (k[x], x)))
                 for pair in opposite_pairs if c not in pair]
    i, (w, v) = max(enumerate(remaining), key=lambda item: k[item[1][1]]-k[item[1][0]])
    other = remaining[1-i]
    sums = [k[c]+k[w]+k[u] for u in other]
    require(min(sums) > 1 and max(sums) < 3 and 2*k[c]+k[w] >= 1,
            'The written larger-difference choice failed a cap or slit bound')
    return dict(source=v, fan=w, slit=c, face_cap_sums=sums)


def triple_band(g, vertices, bands):
    """Compare three positive curvatures with pi, including complement deductions."""
    if any(bands[v] in ('>', '=') for v in vertices):
        return '>'
    complement = [v for v in range(6) if v not in vertices]
    if all(bands[v] in ('<', '=') for v in complement):
        return '=' if all(bands[v] == '=' for v in complement) else '>'
    if all(bands[v] == '<' for v in vertices):
        result = positive_angles_pi([conjugate(polygon_angle_product(g, v))
                                     for v in vertices])
        if result is not None:
            return result
    exact = [exact_polygon_angle_sum_pi(g, v) for v in vertices]
    if all(value is not None for value in exact):
        curvature = 6-sum(exact, F(0))
        return '<' if curvature < 1 else '>' if curvature > 1 else '='
    return None


def choose(g):
    require(len(g.faces) == 8 and all(len(face) == 3 for face in g.faces),
            'Expected triangular octahedron faces')
    inc = incidence(g.faces)
    adjacent = {v: {u for u in range(6) if edge(u, v) in inc} for v in range(6)}
    require(all(len(row) == 4 for row in adjacent.values()), 'Expected the octahedral graph')
    opposite = {v: next(iter(set(range(6))-{v}-adjacent[v])) for v in range(6)}
    pairs = sorted({tuple(sorted((v, opposite[v]))) for v in range(6)})
    maximum = None
    for c in range(6):
        try:
            order = verify_order(g, [(c, v) for v in range(6) if v != c])
        except ValueError:
            continue
        maximum = c, order
        break
    require(maximum is not None, 'No uniform maximum-curvature slit vertex certified')
    c, order = maximum
    remaining = [pair for pair in pairs if c not in pair]
    ordered = []
    pair_orders = []
    for pair in remaining:
        for w, v in (pair, pair[::-1]):
            try:
                comparison = verify_order(g, [(v, w)])
            except ValueError:
                continue
            ordered.append((w, v))
            pair_orders.append(comparison)
            break
        else:
            raise ValueError('No uniform smaller fan endpoint certified')
    bands = curvature_bands(g)
    gaps = []
    for w, v in ordered:
        signature = point_angle_signature(g, w)
        if signature is not None and signature == point_angle_signature(g, v):
            gaps.append((I(1), I(0)))
        else:
            # Curvature_v-curvature_w = Gamma_w-Gamma_v lies in [0,2*pi).
            gaps.append(cmul(polygon_angle_product(g, w),
                             conjugate(polygon_angle_product(g, v))))
    gap_order = interval_angle_le(gaps[0], gaps[1])
    preferred = 1 if gap_order is True else 0 if gap_order is False else None
    proposals = list(enumerate(ordered))
    if preferred is not None:
        proposals.sort(key=lambda item: item[0] != preferred)
    unresolved = []
    for i, (w, v) in proposals:
        # The exact pair order gives source >= fan. This implies the
        # half-fan alternative source >= pi or fan <= pi, without a
        # potentially unresolved comparison at pi.
        other = ordered[1-i]
        caps = []
        for u in other:
            vertices = [w, c, u]
            complement = sorted(set(range(6))-set(vertices))
            caps.append(dict(vertices=vertices, lower_pi=triple_band(g, vertices, bands),
                             complement= complement,
                             complement_lower_pi=triple_band(g, complement, bands)))
        canonical = i == preferred
        if canonical:
            # Maximum c and the two exact pair orders imply the lower cap
            # bounds; larger difference minimizes U, and U1+U2<6*pi gives
            # both upper bounds strictly. No trigonometric sum test is needed.
            require(all(cap['lower_pi'] not in ('<', '=') and cap['complement_lower_pi'] not in ('<', '=')
                        for cap in caps), 'A cap comparison contradicts the exact selection inequalities')
        elif not all(cap['lower_pi'] in ('>', '=') and
                     cap['complement_lower_pi'] in ('>', '=') for cap in caps):
            unresolved.append(dict(fan=w, reason='Uniform face-cap bounds unresolved or false', caps=caps))
            continue
        cuts = sorted({edge(v, u) for u in adjacent[v]} | {edge(w, c)})
        return dict(source=v, fan=w, slit=c, cut_edges=[list(e) for e in cuts],
                    maximum_curvature_order=order, opposite_pair_orders=pair_orders,
                    pair_difference_phases=[[x.pair() for x in gap] for gap in gaps],
                    first_pair_difference_at_most_second=gap_order,
                    canonical_larger_difference_choice=canonical,
                    cap_bounds_from_selection_identities=canonical,
                    curvature_comparisons_with_pi=bands, face_caps=caps,
                    weighted_slit_threshold='Strictly above pi because the maximum curvature is at least 2*pi/3',
                    earlier_unresolved_choices=unresolved,
                    half_fan_hypothesis='Source curvature is at least fan curvature',
                    old_high_source_or_all_low_condition_used=False)
    raise ValueError('No uniform face-cap choice certified; this does not refute pointwise existence')


def select(spec):
    decision = choose(Geometry(spec))
    clean = {k: v for k, v in spec.items()
             if k not in ('selection', 'pair_witnesses', 'overlap_witness', 'angular_claims')}
    certificate = make_certificate({**clean, 'cut_edges': decision['cut_edges']})
    replay = all_pairs(certificate)
    return dict(result='verified_octahedron_face_cap_selected_net', selection=decision,
                certificate=certificate, independent_all_28_pairs=replay,
                geometric_proof_formally_verified=False,
                scope='The cap rule selects this whole original-edge net on the explicit domain; all 28 pairs are independently checked. The universal argument is the separate written proof OCTA_FACE_CAP_RULE.md.')


def main():
    import argparse, json
    from pathlib import Path
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input', type=Path)
    ap.add_argument('--certificate', type=Path)
    args = ap.parse_args()
    set_precision(240)
    report = select(json.loads(args.input.read_text()))
    certificate = report.pop('certificate')
    if args.certificate:
        args.certificate.write_text(json.dumps(certificate, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
