"""Compare small octahedral cut rules and enumerate four-slit failure patterns.

The combinatorial enumeration is exhaustive for the stated family. Shape
sampling is floating-point exploration, never a certificate of nonoverlap.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path
import time
import numpy as np
from durer_small_n.octa import Octa, rand_points, octa_structure
from n6.minus_patterns import TreeBatch
from n6.original_star_probe import apex_curvature
from n6.sector_probe import sector_choices, two_face_paths
from n6.trees import degree_four_stars, tree_path

FACES = [(1, 2+i, 2+(i+1)%4) for i in range(4)] + [
    (0, 2+(i+1)%4, 2+i) for i in range(4)]
ADJ = {v: set().union(*(set(f)-{v} for f in FACES if v in f)) for v in range(6)}


def canonical_points(raw):
    """Relabel a strictly screened octahedron; normalize its diameter to one."""
    p = np.asarray(raw, dtype=float)
    structure = octa_structure(p)
    if structure is None:
        return None
    faces, adj = structure
    w = next(v for v in range(1, 6) if v not in adj[0])
    nxt = {}
    for f in faces:
        if w in f:
            i = f.index(w)
            nxt[f[(i+1)%3]] = f[(i+2)%3]
    ring = [min(adj[w])]
    for _ in range(3):
        ring.append(nxt[ring[-1]])
    p = p[[0, w] + ring]
    return (p-p[0])/np.max(np.linalg.norm(p[:, None]-p[None], axis=-1))


def four_slit_obligations(local_opposite=False):
    """Minimal sets of bad relative face placements covering all four slits.

    Face positions relative to one another depend only on their unique hinge
    path. Identify the same path in different trees, then quotient the cover
    list by the eight ring symmetries fixing both poles. This does not show
    which covers can occur geometrically.
    """
    events = {}
    raw_checks = 0
    for t in degree_four_stars(FACES):
        if t['apex'] != 0:
            continue
        adj = {i: [] for i in range(8)}
        for a, b in t['hinges']:
            adj[a].append(b)
            adj[b].append(a)
        for a, b in t['pairs']:
            # A far-fan failure forces a local or opposite-petal failure by
            # a formerly claimed conditional hinge lemma, now refuted. This
            # option preserves the historical hypothetical enumeration only.
            if local_opposite and a < 4 <= b and (b-4-a)%4 == 2:
                continue
            raw_checks += 1
            path = tuple(tree_path(adj, a, b))
            key = min(path, path[::-1])
            events.setdefault(key, set()).add(t['slit_vertex'])
    paths = sorted(events)
    covers = set()
    universe = {2, 3, 4, 5}
    for size in range(1, 5):
        for c in combinations(range(len(paths)), size):
            if set().union(*(events[paths[i]] for i in c)) != universe:
                continue
            if any(set().union(*(events[paths[i]] for i in c if i != omit)) == universe for omit in c):
                continue
            covers.add(c)
    face_index = {frozenset(f): i for i, f in enumerate(FACES)}
    actions = []
    for sign in (1, -1):
        for shift in range(4):
            perm = [0, 1] + [2+(sign*i+shift)%4 for i in range(4)]
            mapped = [face_index[frozenset(perm[v] for v in f)] for f in FACES]
            action = []
            for path in paths:
                q = tuple(mapped[f] for f in path)
                action.append(paths.index(min(q, q[::-1])))
            actions.append(action)
    remaining = set(covers)
    orbits = []
    while remaining:
        representative = min(remaining)
        orbit = {tuple(sorted(a[i] for i in representative)) for a in actions}
        if not orbit <= covers:
            raise AssertionError('Symmetry left the cover family')
        remaining -= orbit
        orbits.append(dict(representative=list(representative), size=len(orbit)))
    return dict(scope=('Historical hypothetical enumeration using a refuted conditional lemma; not a valid sufficient reduction.'
                       if local_opposite else 'Exact combinatorial enumeration; no geometric class excluded.'),
                apex=0, antipode=1, slits=[2, 3, 4, 5],
                raw_pair_checks=raw_checks, distinct_placements=len(paths),
                events=[dict(id=i, hinge_path=list(p), bad_slits=sorted(events[p])) for i, p in enumerate(paths)],
                minimal_covers=len(covers), cover_sizes=dict(sorted(Counter(map(len, covers)).items())),
                symmetry_classes=len(orbits), classes=orbits)


def failure_case_analysis():
    """Check slit repairs and retain only local/opposite failure witnesses.

    This applies existing geometric lemmas to verified hinge paths; it is not
    a formal proof of those lemmas or an exclusion of the remaining classes.
    """
    full = four_slit_obligations()
    reduced = four_slit_obligations(local_opposite=True)
    path_to_id = {tuple(e['hinge_path']): e['id'] for e in full['events']}
    original_ids = {tuple(c['representative']): i for i, c in enumerate(full['classes'], 1)}
    for c in reduced['classes']:
        original_events = [path_to_id[tuple(reduced['events'][i]['hinge_path'])] for i in c['representative']]
        c['original_class_id'] = original_ids[tuple(original_events)]
        paths = [reduced['events'][i]['hinge_path'] for i in c['representative']]
        # The sole two-event class is the same opposite-petal pair around both
        # routes. Its two middle fan-angle sums add to 2*pi + curvature(w),
        # whereas both overlaps would require each sum < pi under (H).
        opposite_routes = (len(paths) == 2 and all(len(p) == 5 and min(p[0], p[-1]) >= 4 for p in paths)
                           and {paths[0][0], paths[0][-1]} == {paths[1][0], paths[1][-1]}
                           and (paths[0][2]-paths[1][2])%4 == 2)
        forced_nonconvex = {max(p[0],p[-1])-4 for p in paths if min(p[0],p[-1])<4<=max(p[0],p[-1])}
        c['status'] = ('excluded_by_opposite_route_angle_sum' if opposite_routes else
                       'excluded_by_convex_patch_existence' if forced_nonconvex == set(range(4)) else 'open')
        c['forced_nonconvex_patches'] = sorted(forced_nonconvex)
    trees = {t['slit_vertex']: t for t in degree_four_stars(FACES) if t['apex'] == 0}
    repairs = []
    for event in full['events']:
        if len(event['bad_slits']) != 1:
            continue
        old_slit = event['bad_slits'][0]
        a, b = event['hinge_path'][0], event['hinge_path'][-1]
        alternatives = []
        for slit, t in trees.items():
            if slit == old_slit:
                continue
            adj = {i: [] for i in range(8)}
            for f, g in t['hinges']:
                adj[f].append(g)
                adj[g].append(f)
            path = tree_path(adj, a, b)
            common = set.intersection(*(set(FACES[f]) for f in path))
            if common != {old_slit} or (a, b) in t['pairs']:
                raise AssertionError('Local pair did not regain the common uncut vertex')
            alternatives.append(dict(slit_vertex=slit, hinge_path=path, shared_vertex=old_slit))
        repairs.append(dict(original_event=event['id'], old_slit=old_slit,
                            face_pair=[a, b], alternatives=alternatives))
    # Check the symbolic angle identity: each route uses the four base angles
    # beside its middle edge; opposite routes use all eight exactly once.
    route_terms = lambda j: [((j-1)%4, 'right'), (j, 'left'), (j, 'right'), ((j+1)%4, 'left')]
    all_terms = Counter((i, side) for i in range(4) for side in ('left', 'right'))
    identities = []
    for j in range(2):
        if Counter(route_terms(j)+route_terms(j+2)) != all_terms:
            raise AssertionError('Opposite routes do not exhaust the fan base angles')
        identities.append(dict(middle_faces=[j,j+2], sum='2*pi + curvature(w)',
                               base_angle_terms=route_terms(j)+route_terms(j+2)))
    closed = sum(c['status'] != 'open' for c in reduced['classes'])
    reduced['scope'] = 'Withdrawn as a sufficient reduction: the conditional far-fan lemma is refuted. These 24 historical classes and their arithmetic enumeration are retained for reference.'
    reduced['sufficient_reduction_valid'] = False
    for original_id,c in enumerate(full['classes'],1):
        c['original_class_id'] = original_id
        c['status'] = ('excluded_by_convex_patch_existence' if original_id == 20 else
                       'excluded_by_opposite_route_angle_sum' if original_id == 49 else 'open')
    full['scope'] = 'Current sufficient target: original 49 classes, with classes 20 and 49 excluded by independent geometric proofs; 47 remain open.'
    corner_assignments = [list(c) for c in product(*[(i,(i+1)%4) for i in range(4)]) if len(set(c))==4]
    if sorted(corner_assignments) != [[0,1,2,3],[1,2,3,0]]:
        raise AssertionError('Unexpected reflex-corner assignment')
    return dict(schema='n6-octa-failure-analysis-v1',
                scope='The two switching implications survive. The conditional far-fan reduction is refuted; use the original 49 classes, with 2 excluded and 47 open.',
                dependencies=['Shared-vertex fan lemma for convex polyhedra',
                              'Audit correction: the former conditional far-fan lemma is false; its 24-class target is historical, not sufficient',
                              'Case A opposite-petal exclusion under maximum apex curvature and the base-cone lemma',
                              'Triangle angle sums and strictly positive curvature at w',
                              'At least one convex two-triangle patch: reflex corners force strict increases of |wu|+|vu|, and adjacent patches cannot both be reflex at their shared equator vertex'],
                original_classes=full['symmetry_classes'], current=full, reduced=reduced,
                local_pair_repairs=repairs, opposite_route_identities=identities,
                impossible_all_reflex_assignments=corner_assignments,
                geometric_classes_excluded=closed, remaining_classes=full['symmetry_classes']-closed,
                original_classes_retained=[c['original_class_id'] for c in reduced['classes']])


def selection_rules(p, trees, curvature):
    sharp = int(np.argmax(curvature))
    opposite = next(t['antipode'] for t in trees if t['apex'] == sharp)
    at = lambda v: [i for i, t in enumerate(trees) if t['apex'] == v]
    ranked = sorted(at(sharp), key=lambda i: (-curvature[trees[i]['slit_vertex']], trees[i]['slit_vertex']))
    result = dict(all_nearstars=list(range(24)), fixed_apex_four=at(0),
                  fixed_opposite_pair_eight=at(0)+at(1), sharpest_apex_four=at(sharp),
                  sharpest_opposite_four=at(opposite), sharpest_pair_eight=at(sharp)+at(opposite),
                  sharpest_apex_sharpest_slit=ranked[:1], sharpest_apex_top_two_slits=ranked[:2])
    paths = two_face_paths(p, FACES, sharp, opposite)
    if paths:
        _, a, b, *_ = min(paths, key=lambda t: t[0])
        result['sharpest_apex_geodesic_endpoints'] = [i for i in at(sharp) if trees[i]['slit_vertex'] in (a, b)]
    else:
        result['sharpest_apex_geodesic_endpoints'] = []
    o = Octa(p, sharp, FACES, ADJ)
    sums = np.roll(o.bWp, 1)+o.bW+o.bWp+np.roll(o.bW, -1)
    allowed = [o.u[k] for k in range(4) if min(sums[(k+1)%4], sums[(k+2)%4]) >= np.pi-1e-12]
    result['sharpest_apex_large_fan_sums'] = [i for i in at(sharp) if trees[i]['slit_vertex'] in allowed]
    return result


def run(samples, seed, max_attempts):
    rng = np.random.default_rng(seed)
    trees = degree_four_stars(FACES)
    batch = TreeBatch(trees, faces=FACES)
    plans = [(t['apex'], t['antipode'], t['slit_vertex'], None) for t in trees]
    lookup = {t[:3]: i for i, t in enumerate(plans)}
    totals = {}
    count = attempts = 0
    histogram = Counter()
    sector_counts = Counter()
    first_failures = {}
    start = time.monotonic()
    while count < samples and attempts < max_attempts:
        attempts += 1
        p = canonical_points(rand_points(6, rng))
        if p is None:
            continue
        curvature = [apex_curvature(p, FACES, v) for v in range(6)]
        margin = batch.margins(p)
        if not np.isfinite(margin).all():
            raise ValueError('Nonfinite numerical development')
        # Positive means a separating supporting line. Keep borderline shapes
        # separate rather than silently interpreting a tolerance as a proof.
        clear = margin > 1e-10
        possible = margin >= -1e-10
        rules = selection_rules(p, trees, curvature)
        for name, indices in rules.items():
            row = totals.setdefault(name, dict(clear=0, borderline=0, failed=0, minimum_clear_choices=24))
            successful = int(sum(clear[indices]))
            row['minimum_clear_choices'] = min(row['minimum_clear_choices'], successful)
            state = 'clear' if successful else 'borderline' if any(possible[indices]) else 'failed'
            row[state] += 1
            if state == 'failed' and name not in first_failures:
                first_failures[name] = dict(sample=count, points=p.tolist(), curvature=curvature,
                                           choices=indices, margins=margin.tolist())
        sector = sector_choices(p, FACES, plans, 2*np.pi-np.array(curvature))
        sector_counts['any_choice'] += bool(sector)
        sector_counts['at_sharpest_apex'] += any(v == int(np.argmax(curvature)) for v, w, u in sector)
        sector_counts['at_sharpest_opposite'] += any(w == int(np.argmax(curvature)) for v, w, u in sector)
        if any(margin[lookup[t]] < -1e-8 for t in sector):
            raise AssertionError('Numerical sector condition disagrees with net development')
        histogram[int(sum(clear))] += 1
        count += 1
        if count % 250 == 0:
            print('samples', count, 'elapsed', round(time.monotonic()-start, 1), flush=True)
    return dict(scope='Numerical evidence only. No universal rule is proved; even clear sample results are not exact certificates.',
                seed=seed, requested_samples=samples, samples=count, attempts=attempts,
                status='complete' if count == samples else 'incomplete',
                distribution='Claude octa.rand_points: Gaussian, sphere, cube, or one distant point; anisotropic scales exp[-4,4], then strict octahedral facet screen.',
                separation_tolerance=1e-10, normalization='diameter one',
                elapsed_seconds=time.monotonic()-start, rules=totals,
                clear_nearstars_histogram=dict(sorted(histogram.items())),
                numerical_sector_condition=sector_counts, first_numerical_failures=first_failures)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--samples', type=int, default=3000)
    ap.add_argument('--seed', type=int, default=6090931)
    ap.add_argument('--max-attempts', type=int, default=100000)
    ap.add_argument('--output', type=Path, default=Path('n6/results/octa-patterns.json'))
    ap.add_argument('--obligations', action='store_true')
    ap.add_argument('--case-analysis', action='store_true')
    args = ap.parse_args()
    if args.samples <= 0 or args.max_attempts <= 0:
        ap.error('Counts must be positive')
    if args.case_analysis:
        report = failure_case_analysis()
    else:
        report = four_slit_obligations() if args.obligations else run(args.samples, args.seed, args.max_attempts)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('first_numerical_failures', 'events', 'classes')}, indent=2))


if __name__ == '__main__':
    main()
