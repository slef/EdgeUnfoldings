"""Compare small octahedral cut rules and enumerate four-slit failure patterns.

The combinatorial enumeration is exhaustive for the stated family. Shape
sampling is floating-point exploration, never a certificate of nonoverlap.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import time
import numpy as np
from durer_small_n.octa import rand_points, octa_structure
from n6.minus_patterns import TreeBatch
from n6.original_star_probe import apex_curvature
from n6.sector_probe import sector_choices, two_face_paths
from n6.trees import degree_four_stars, tree_path

FACES = [(1, 2+i, 2+(i+1)%4) for i in range(4)] + [
    (0, 2+(i+1)%4, 2+i) for i in range(4)]


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


def four_slit_obligations():
    """Minimal sets of bad relative face placements covering all four slits.

    Face positions relative to one another depend only on their unique hinge
    path. Identify the same path in different trees, then quotient the cover
    list by the eight ring symmetries fixing both poles. This does not show
    which covers can occur geometrically.
    """
    events = {}
    for t in degree_four_stars(FACES):
        if t['apex'] != 0:
            continue
        adj = {i: [] for i in range(8)}
        for a, b in t['hinges']:
            adj[a].append(b)
            adj[b].append(a)
        for a, b in t['pairs']:
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
    return dict(scope='Exact combinatorial enumeration; no geometric class excluded.',
                apex=0, antipode=1, slits=[2, 3, 4, 5],
                raw_pair_checks=36, distinct_placements=len(paths),
                events=[dict(id=i, hinge_path=list(p), bad_slits=sorted(events[p])) for i, p in enumerate(paths)],
                minimal_covers=len(covers), cover_sizes=dict(sorted(Counter(map(len, covers)).items())),
                symmetry_classes=len(orbits), classes=orbits)


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
    args = ap.parse_args()
    if args.samples <= 0 or args.max_attempts <= 0:
        ap.error('Counts must be positive')
    report = four_slit_obligations() if args.obligations else run(args.samples, args.seed, args.max_attempts)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('first_numerical_failures', 'events', 'classes')}, indent=2))


if __name__ == '__main__':
    main()
