"""Exact algebra and explicit-domain checks for the streamlined proof.

The geometric proof is in TIDY_CORE.md and TIDY_PROOF.md. These checks
verify identities or individual coordinate domains; they do not formally
verify the geometry or infer a universal theorem from examples.
"""
from n6.certify import require
from n6.curvature import angle_product, cmul, interval_angle_le
from n6.families import MINUS_FACES
from n6.flat_octahedron import curvature_bands
from n6.half_fan import setup
from n6.patch_budget import pole_angles_and_leans
from n6.polynomials import Poly
from n6.polycert import Geometry


def complement_classification():
    """Independent finite check of the elementary complement classification.

    This enumerates graphs, not metric shapes. The exclusions use explicit
    K_3,3 subgraphs or a two-vertex separator, as in the written proof.
    """
    from itertools import combinations, permutations
    from n6.families import PRISM_FACES
    edges = tuple(combinations(range(6), 2))
    representatives = {}
    labeled_count = 0
    for mask in range(1 << len(edges)):
        adj = [set() for _ in range(6)]
        for i, (a, b) in enumerate(edges):
            if mask & (1 << i):
                adj[a].add(b)
                adj[b].add(a)
        if not all(1 <= len(a) <= 2 for a in adj):
            continue
        labeled_count += 1
        remaining = set(range(6))
        components = []
        while remaining:
            component, stack = set(), [min(remaining)]
            while stack:
                x = stack.pop()
                if x not in component:
                    component.add(x)
                    stack.extend(adj[x]-component)
            remaining -= component
            kind = 'C' if all(len(adj[x]) == 2 for x in component) else 'P'
            components.append((kind+str(len(component)), component))
        key = '+'.join(sorted(kind for kind, _ in components))
        representatives.setdefault(key, (adj, components))

    expected = {'P2+P2+P2', 'P2+P4', 'P6', 'C6',
                'P3+P3', 'C3+P3', 'C3+C3', 'C4+P2'}
    require(set(representatives) == expected, 'Missing complement component type')
    def facet_edges(faces):
        return {tuple(sorted((a, b))) for f in faces
                for a, b in zip(f, f[1:]+f[:1])}
    standard = {
        'P2+P2+P2': ('octahedron', set(edges)-{(0, 1), (2, 3), (4, 5)}),
        'P2+P4': ('octahedron minus an edge', facet_edges(MINUS_FACES)),
        'P6': ('prism with one diagonal', facet_edges(PRISM_FACES)),
        'C6': ('triangular prism', facet_edges(
            ((0, 1, 2), (3, 5, 4), (0, 3, 4, 1), (1, 4, 5, 2), (2, 5, 3, 0))))}
    rows = []
    for key, (adj, components) in sorted(representatives.items()):
        original = {(a, b) for a, b in edges if b not in adj[a]}
        if len(components) == 2 and all(len(c) == 3 for _, c in components):
            left, right = [c for _, c in components]
            require(all(tuple(sorted((a, b))) in original for a in left for b in right),
                    'Missing claimed K_3,3 subgraph')
            rows.append(dict(complement=key, excluded_by='K_3,3 subgraph'))
        elif key == 'C4+P2':
            cycle = next(c for kind, c in components if kind == 'C4')
            residual = {(a, b) for a, b in original if a in cycle and b in cycle}
            require(len(residual) == 2 and set.union(*(set(e) for e in residual)) == cycle,
                    'The claimed two-vertex deletion is not two disjoint edges')
            rows.append(dict(complement=key, excluded_by='two-vertex separator'))
        else:
            name, target = standard[key]
            mapping = next((p for p in permutations(range(6)) if
                {tuple(sorted((p[a], p[b]))) for a, b in original} == target), None)
            require(mapping is not None, 'Incorrect original facet-graph identification')
            rows.append(dict(complement=key, original_type=name, relabeling=list(mapping)))
    return dict(result='verified_complement_graph_classification',
                labeled_complements_checked=labeled_count, component_types=rows,
                retained_types=4, geometry_or_unfolding_formally_verified=False,
                scope='Finite graph classification only; not a metric-shape sample.',
                proof='TIDY_PROOF.md')


def minus_identity():
    """Eliminate one angle per ORIGINAL facet; check every coefficient."""
    n = sum(len(face)-1 for face in MINUS_FACES)
    angles = {}
    index = 0
    for f, face in enumerate(MINUS_FACES):
        for vertex in face[:-1]:
            angles[f, vertex] = Poly.variable(n, index)
            index += 1
        angles[f, face[-1]] = len(face)-2-sum(
            angles[f, vertex] for vertex in face[:-1])
    curvature = {vertex: 2-sum(angles[f, vertex]
        for f, face in enumerate(MINUS_FACES) if vertex in face)
        for vertex in range(6)}
    K = curvature[3]+curvature[5]
    theta_a, theta_b = 1-angles[3, 0]+K, 1-angles[4, 1]+K
    outer_a, outer_b = angles[0, 0]+angles[2, 0], angles[0, 1]+angles[5, 1]
    positive_remainder = K+angles[0, 2]+angles[2, 4]+angles[5, 4]
    identity = theta_a+theta_b-outer_a-outer_b-positive_remainder
    require(identity.is_zero(), 'The streamlined minus-edge identity is false')
    return dict(result='verified_exact_minus_single_identity',
                independent_angle_indeterminates=n,
                arithmetic='Exact rational polynomial coefficients',
                positivity_or_geometry_formally_verified=False,
                proof='TIDY_PROOF.md')


def shorter_prism_identities():
    """Check the new positive-remainder forms over every original face sum."""
    from fractions import Fraction as F
    from n6.families import PRISM_FACES
    n = sum(len(face)-1 for face in PRISM_FACES)
    a, index = {}, 0
    for label, face in zip('ABCDEF', PRISM_FACES):
        for vertex in face[:-1]:
            a[label+str(vertex)] = Poly.variable(n, index)
            index += 1
        a[label+str(face[-1])] = len(face)-2-sum(a[label+str(v)] for v in face[:-1])
    k = {v: 2-sum(a[label+str(v)] for label, face in zip('ABCDEF', PRISM_FACES)
                  if v in face) for v in range(6)}
    K = k[3]+k[4]
    fC = 2*a['C1']+a['E1']-2-K
    fD = 2*a['D1']+a['E1']-2-K
    gB = 2*a['B5']+a['F5']-2-K
    gD = 2*a['D5']+a['F5']-2-K
    slack = lambda name: 2-k[int(name[1:])]-2*a[name]
    identities = [
        fC+a['C0']+a['F5']+(1-a['B3'])+(1-a['C1'])+(1-a['D4']),
        fD+gD+2*a['D2']+a['E1']+a['F5']+2*(1-a['B3'])+2*(1-a['C3']),
        fD+gB+slack('A0')+slack('A2')+slack('B5')+k[1]+2*a['C1']
        +(1-a['B3'])+(1-a['C3'])+(1-a['D4'])+2*(a['E1']-F(1, 2))]
    require(all(p.is_zero() for p in identities), 'A shorter prism identity is false')
    return dict(result='verified_exact_shorter_prism_identities', identities=3,
                independent_angle_indeterminates=n,
                arithmetic='Exact rational polynomial coefficients',
                geometry_or_positivity_formally_verified=False,
                proof='TIDY_PROOF.md')


def half_fan(spec):
    """Directly compare twice each actual patch span with the whole fan."""
    selection = spec['selection']
    v, w, ring = (selection[k] for k in ('apex', 'antipode', 'equator'))
    g = Geometry(spec)
    bands = curvature_bands(g)
    require(bands[v] in ('>', '=') or bands[w] in ('<', '='),
            'Expected source curvature >=pi or fan curvature <=pi')
    patches, directions, lookup = setup(g, v, w, ring)
    angles, leans = pole_angles_and_leans(g, v, w, ring, directions, lookup)
    total = angle_product(g.p, g.faces, g.h, w)
    comparisons = []
    for i in range(4):
        span = angles[w][i] if not directions[i] else cmul(angles[w][i], leans[w][i])
        doubled = cmul(span, span)
        # A simple patch's angular span lies in (0,pi), so twice its span
        # and the complete fan angle both lie in (0,2*pi). No phase wrap
        # is silently ignored in these comparisons.
        below = interval_angle_le(doubled, total)
        reverse = interval_angle_le(total, doubled)
        require(below is True and reverse is False,
                'Strict half-fan comparison unresolved on this domain')
        comparisons.append(dict(patch=i, direction=directions[i],
                                twice_span_strictly_below_fan=True))
    return dict(result='verified_direct_half_fan_spans', source=v, fan=w,
                parameter_dimension=len(g.box), curvature_bands=bands,
                patches=patches, comparisons=comparisons,
                whole_net_claimed=False, geometric_proof_formally_verified=False,
                scope='Direct exact angular inequalities on this explicit domain only.',
                proof='TIDY_CORE.md')


def finite_entry_counterexample(spec):
    """Check both new necessary inequalities on an actual exact entry.

    The retained historical witness is outside the selected rule's source
    assumptions. Its entry and all other 27 pairs are rechecked first.
    """
    from n6.hinge_audit import verify
    from n6.curvature import conjugate, face_angle
    from n6.regimes import positive_angles_pi
    old = verify(spec)
    g = Geometry(spec)
    require((old['source'], old['opposite'], old['slit_vertex']) == (0, 1, 2),
            'Expected the documented historical witness labels')
    require(set(g.faces[7]) == {0, 2, 5}, 'Wrong neighboring petal')
    bands = curvature_bands(g)
    require(all(bands[x] == '<' for x in (0, 1, 2, 5)),
            'Required curvature range is unresolved')
    mu = face_angle(g.p, g.faces[7], g.h[7], 5)
    k = {x: conjugate(angle_product(g.p, g.faces, g.h, x)) for x in (1, 2, 5)}
    necessary = positive_angles_pi([k[5], k[2], k[1], k[1], mu, mu])
    require(necessary == '<', 'The combined finite-entry budget is not verified')
    return dict(result='verified_actual_entry_satisfies_both_obstructions',
                source_curvature_below_pi=True, equal_radius_budget_below_pi=True,
                curvature_bands=bands, original_overlap_rechecked=True,
                other_pairs_rechecked=old['nonoverlapping_pairs'],
                universal_geometric_proof_formally_verified=False,
                scope='One exact historical counterexample; the chosen source does not meet the selected rule.',
                proof='TIDY_CORE.md')


def review_report():
    import json
    from pathlib import Path
    from n6.selected_octahedron_examples import specification
    from n6.prism_angle_identities import verify as prism_identities
    root = Path(__file__).parent
    names = ('regular-ties', 'high-curvature', 'low-curvature', 'obtuse',
             'curvature-equality', 'crossing-threshold')
    return dict(result='verified_streamlined_proof_checks',
                complement_classification=complement_classification(),
                minus_identity=minus_identity(), prism_identities=prism_identities(),
                shorter_prism_identities=shorter_prism_identities(),
                half_fan_domains={name: half_fan(specification(name)) for name in names},
                actual_finite_entry=finite_entry_counterexample(json.loads(
                    (root/'results/hinge-boundary-counterexample.certificate.json').read_text())),
                universal_geometric_proof_formally_verified=False)


def main():
    import argparse, json
    from pathlib import Path
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input', nargs='?', type=Path)
    ap.add_argument('--review', action='store_true')
    args = ap.parse_args()
    if args.review:
        set_precision(240)
        result = review_report()
    elif args.input:
        spec = json.loads(args.input.read_text())
        set_precision(spec.get('suggested_fractional_bits', 240))
        result = half_fan(spec)
    else:
        result = minus_identity()
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
