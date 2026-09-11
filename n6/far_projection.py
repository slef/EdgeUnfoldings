"""Exact hypotheses for the selected-net pole-angle theorem.

LEMMA_F_POLE_ANGLE.md supplies the geometric proof. This checks explicit
coordinate domains; it does not turn numerical observations into theorems.
"""
import json
from pathlib import Path

from n6.certify import require, tree_path
from n6.curvature import angle_product, face_angle, cmul, conjugate
from n6.far_pairs import labels
from n6.intervals import dot, sub, norm2
from n6.polycert import Geometry
from n6.regimes import classify, curvature_pi, positive_angles_pi


def at_least_quarter_turn(z):
    """Compare an angle known to lie strictly in (0,2*pi) with pi/2."""
    if z[0].hi <= 0 or z[1].hi < 0:
        return True
    if z[0].lo > 0 and z[1].lo > 0:
        return False
    return None


def analyze(spec):
    classification = classify(spec)
    g = Geometry(spec)
    v, w, ring, k, V, W = labels(spec, g)
    source_band = curvature_pi(angle_product(g.p, g.faces, g.h, v))
    fan_total = angle_product(g.p, g.faces, g.h, w)
    reports = []
    # Remote petal, its possible reflex endpoint, neighboring slit patch.
    for i, a_index, m in [((k+2)%4, (k+3)%4, (k+3)%4),
                           ((k+1)%4, (k+1)%4, k)]:
        a = ring[a_index]
        corner = positive_angles_pi([
            face_angle(g.p, g.faces[f], g.h[f], a) for f in (V[i], W[i])])
        original = dot(sub(g.p[w], g.p[v]), sub(g.p[a], g.p[v]))
        fan = g.develop((W[m],))
        petal = g.develop(tree_path(g.adj, W[m], V[m]))
        M = petal[v]
        flat = dot(sub(petal[a], M), sub(fan[w], M))
        # delta = omega_m + kappa_w = 2*pi - the other three blue angles.
        # Strict convexity makes delta strictly between 0 and 2*pi.
        delta = cmul(face_angle(g.p, g.faces[W[m]], g.h[W[m]], w),
                     conjugate(fan_total))
        wide_gap = at_least_quarter_turn(delta)
        length_difference = norm2(sub(g.p[w], g.p[a]))-norm2(sub(g.p[v], g.p[a]))
        if source_band in ('>', '='):
            method = 'source_curvature_at_least_pi'
        elif corner in ('<', '='):
            method = 'no_extension_toward_gap'
        elif original.lo >= 0:
            method = 'original_pole_angle_nonobtuse'
        elif flat.lo >= 0:
            method = 'neighboring_flat_pole_angle_nonobtuse'
        elif wide_gap is True and length_difference.lo >= 0:
            method = 'short_radius_and_quarter_turn_gap'
        else:
            method = 'unresolved'
        reports.append(dict(remote_patch=i, reflex_vertex=a,
                            neighboring_patch=m, inward_corner_comparison=corner,
                            original_pole_dot=original.pair(), neighboring_flat_dot=flat.pair(),
                            gap_at_least_pi_over_two=wide_gap,
                            fan_minus_source_edge_squared=length_difference.pair(),
                            method=method, cut_segment_safe=method!='unresolved'))
    complete = all(r['cut_segment_safe'] for r in reports)
    return dict(result='verified_pole_angle_net_hypotheses' if complete else
                       'pole_angle_hypotheses_unresolved',
                parameter_dimension=len(g.box), curvature_order=classification['curvature_order'],
                source_curvature_comparison_with_pi=source_band, target_checks=reports,
                whole_selected_net_nonoverlapping=complete,
                universal_lemma_F_proved=False, whole_octahedron_case_proved=False,
                theorem_dependencies=['LEMMA_F_POLE_ANGLE.md', 'LEMMA_L_PROOF.md',
                                      'LEMMA_F_CUT_RAYS.md', 'LEMMA_F_CUT_REDUCTION.md',
                                      'CASE_PARTITION.md', 'HINGE_AUDIT.md'],
                scope='Hypotheses certified on the explicit region. The written theorem proves the whole selected net when both tests pass; the universal obtuse branch remains open.')


def verify(spec):
    report = analyze(spec)
    require(report['whole_selected_net_nonoverlapping'],
            'Pole-angle sufficient hypotheses unresolved; no whole-net certificate')
    return report


def main():
    import argparse
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    ap.add_argument('--analyze', action='store_true')
    args = ap.parse_args()
    spec = json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits', 240))
    print(json.dumps((analyze if args.analyze else verify)(spec), indent=2))


if __name__ == '__main__':
    main()
