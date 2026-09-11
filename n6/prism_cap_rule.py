"""Exact explicit-domain checks of the five-candidate prism cap rule.

The universal geometric proof is PRISM_CAP_RULE.md. These checks classify
the supplied domain and independently verify one whole original-edge net.
An unresolved interval comparison is not a counterexample to the proof.
"""
from fractions import Fraction

from n6.certify import require
from n6.curvature import conjugate
from n6.families import PRISM_CUTS, PRISM_FACES
from n6.flat_octahedron import (curvature_bands, exact_polygon_angle_sum_pi,
                                original_candidates)
from n6.polycert import Geometry, make_certificate, verify as all_pairs
from n6.polynomials import Poly
from n6.prism_paths import polygon_angle_product
from n6.regimes import positive_angles_pi


CAPS = {'A': (0, 1, 2), 'F': (3, 4, 5)}


def identities():
    """Four cap identities and total curvature, with every rational coefficient checked."""
    n = sum(len(face)-1 for face in PRISM_FACES)
    angles, index = {}, 0
    for label, face in zip('ABCDEF', PRISM_FACES):
        for vertex in face[:-1]:
            angles[label, vertex] = Poly.variable(n, index)
            index += 1
        angles[label, face[-1]] = len(face)-2-sum(
            angles[label, v] for v in face[:-1])
    k = {v: 2-sum(angles[label, v] for label, face in zip('ABCDEF', PRISM_FACES)
                 if v in face) for v in range(6)}
    residuals = [sum(k.values())-4]
    for cap, pole, base in (('A', 2, (0, 1)), ('F', 5, (3, 4))):
        nu, lam, rho = (angles[label, pole] for label in (cap, 'B', 'D'))
        K = sum(k[v] for v in base)
        C = K+k[pole]
        residuals += [2*lam+nu-2-K-(lam-rho-C),
                      2*rho+nu-2-K-(rho-lam-C)]
    require(all(p.is_zero() for p in residuals), 'A prism cap identity is false')
    return dict(result='verified_exact_prism_cap_identities', cap_identities=4,
                total_curvature_identity=True, independent_angle_indeterminates=n,
                arithmetic='Exact rational polynomial coefficients',
                geometric_proof_formally_verified=False)


def cap_bands(g):
    """Compare the two positive curvature sums to pi, without phase wrapping."""
    bands = curvature_bands(g)
    result = {}
    for name, vertices in CAPS.items():
        if any(bands[v] in ('>', '=') for v in vertices):
            # The other two curvatures are strictly positive.
            result[name] = '>'
            continue
        value = None
        if all(bands[v] == '<' for v in vertices):
            value = positive_angles_pi([conjugate(polygon_angle_product(g, v))
                                        for v in vertices])
        if value is None:
            exact = [exact_polygon_angle_sum_pi(g, v) for v in vertices]
            if all(q is not None for q in exact):
                curvature = 6-sum(exact, Fraction(0))
                value = '<' if curvature < 1 else '>' if curvature > 1 else '='
        result[name] = value
    for name, vertices in CAPS.items():
        opposite = [v for v in range(6) if v not in vertices]
        if all(bands[v] in ('<', '=') for v in opposite):
            # Total curvature is 4*pi. This also certifies the exact cap
            # boundary when the complementary three curvatures all equal pi.
            deduction = '=' if all(bands[v] == '=' for v in opposite) else '>'
            require(result[name] in (None, deduction), 'Inconsistent cap curvature bounds')
            result[name] = deduction
    require(not all(value == '<' for value in result.values()),
            'Both cap sums cannot be below pi on a convex polyhedron')
    return result, bands


def candidates():
    _, near = original_candidates(PRISM_FACES)
    allowed = {(1, 2), (1, 4), (3, 0), (3, 5)}
    return [dict(name='source_%s_slit_%s' % (t['source'], t['slit']),
                 source=t['source'], slit=t['slit'],
                 cut_edges=[list(e) for e in t['cuts']])
            for t in near if (t['source'], t['slit']) in allowed] + [
        dict(name='triangular_chain_fallback', source=None, slit=None,
             cut_edges=[list(e) for e in PRISM_CUTS])]


def choose_candidates(g):
    require(tuple(g.faces) == PRISM_FACES, 'Expected the stated original prism facets')
    caps, bands = cap_bands(g)
    family = candidates()
    fallback = family[-1]
    if all(value in ('>', '=') for value in caps.values()):
        return dict(branch='both_cap_sums_at_least_pi', cap_comparisons=caps,
                    vertex_curvature_comparisons=bands, candidates=[fallback])
    if caps['F'] == '<':
        # C_A=4*pi-C_F>3*pi. Its original degree-three endpoint is 2.
        pole, orientation = 2, 'A'
        sharp, gate = (1, 2), (3, 0)
    elif caps['A'] == '<':
        pole, orientation = 5, 'F'
        sharp, gate = (3, 5), (1, 4)
    else:
        raise ValueError('No uniform cap branch certified on this domain')
    require(bands[pole] in ('<', '=', '>'),
            'No uniform end-curvature branch certified on this domain')
    is_sharp = bands[pole] in ('>', '=')
    pair = sharp if is_sharp else gate
    chosen = next(t for t in family if (t['source'], t['slit']) == pair)
    return dict(branch='large_cap_%s_%s_switch' %
                (orientation, 'sharp_end' if is_sharp else 'curvature_gate'),
                cap_comparisons=caps, vertex_curvature_comparisons=bands,
                large_cap_above_three_pi_by_total_curvature=orientation,
                candidates=[chosen, fallback])


def select(spec):
    g = Geometry(spec)
    selection = choose_candidates(g)
    attempts = []
    for candidate in selection['candidates']:
        # Old pair or overlap witnesses are never reused after changing the cuts.
        clean = {k: v for k, v in spec.items()
                 if k not in ('pair_witnesses', 'overlap_witness')}
        try:
            certificate = make_certificate({**clean, 'cut_edges': candidate['cut_edges']})
            replay = all_pairs(certificate)
        except ValueError as error:
            attempts.append(dict(candidate=candidate['name'], reason=str(error)))
            continue
        return dict(result='verified_prism_cap_selected_net', selection=selection,
                    selected_candidate=candidate['name'], cut_edges=candidate['cut_edges'],
                    earlier_unresolved_candidates=attempts, certificate=certificate,
                    independent_all_original_pairs=replay, fixed_family_size=5,
                    geometric_proof_formally_verified=False, proof='PRISM_CAP_RULE.md',
                    scope='One original-edge tree independently certified throughout this explicit domain. The universal five-candidate theorem is a separate written geometric argument.')
    raise ValueError('Neither selected candidate certified uniformly on this domain; this is not a counterexample to pointwise existence')


def main():
    import argparse
    import json
    from pathlib import Path
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input', nargs='?', type=Path)
    ap.add_argument('--certificate', type=Path)
    args = ap.parse_args()
    set_precision(240)
    if args.input:
        report = select(json.loads(args.input.read_text()))
        certificate = report.pop('certificate')
        if args.certificate:
            args.certificate.write_text(json.dumps(certificate, indent=2)+'\n')
    else:
        report = identities()
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
