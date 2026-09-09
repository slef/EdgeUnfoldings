"""Bounded numerical searches for simultaneous four-slit failure.

Every reported shape is a proposal for exact checking. Optimizer failure,
timeouts, numerical margins, and absence of a candidate are not proofs.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import minimize
from durer_small_n.octa import random_octahedra, sharpest_apex
from n6.axis_probe import quantities, pack
from n6.octa_patterns import FACES, failure_case_analysis
from n6.minus_patterns import TreeBatch
from n6.trees import degree_four_stars


def run(seconds_per_class, seed, output, classes=None, starts=100, guard=1e-7):
    rng = np.random.default_rng(seed)
    initial = [pack(sharpest_apex(p, faces, adj), 0)
               for p, faces, adj in random_octahedra(rng, starts)]
    analysis = failure_case_analysis()
    rows = [c for c in analysis['current']['classes'] if c['status'] == 'open' and c['original_class_id'] != 20]
    if classes:
        rows = [c for c in rows if c['original_class_id'] in classes]
    trees = [t for t in degree_four_stars(FACES) if t['apex'] == 0]
    batch = TreeBatch(trees, faces=FACES)
    tree_by_slit = {t['slit_vertex']: i for i, t in enumerate(trees)}
    report = dict(scope=__doc__, seed=seed, seconds_per_class=seconds_per_class,
                  guard=guard, starts=starts,
                  target='Current original 49-class list, with two excluded classes omitted',
                  coordinate_bounds='log radii [-6,6], axial heights [-50,50], three azimuth turns (0,pi); fourth turn closes the axis',
                  proof_classes_excluded_here=0, status='running', classes=[])
    for case in rows:
        start = time.monotonic()
        wanted = []
        for event_id in case['representative']:
            event = analysis['current']['events'][event_id]
            p = event['hinge_path']
            wanted.append((tree_by_slit[event['bad_slits'][0]], batch.pairs.index((p[0], p[-1]))))
        best = None
        attempts = calls = 0
        while time.monotonic()-start < seconds_per_class:
            x = initial[attempts % len(initial)].copy()
            if attempts >= len(initial):
                x[:8] += rng.normal(0, .02, 8)
            @lru_cache(maxsize=128)
            def evaluate(t):
                nonlocal calls
                if time.monotonic()-start >= seconds_per_class:
                    raise TimeoutError
                calls += 1
                x = np.array(t)
                q = quantities(x)
                turns = np.r_[x[8:], 2*np.pi-sum(x[8:])]
                constraints = np.r_[turns-guard, np.pi-turns-guard,
                                     q['support']-guard, q['totals'][1:]-q['totals'][0]-guard]
                with np.errstate(all='ignore'):
                    scores = batch.pair_scores(q['points'])/q['scale']
                value = min(scores[i,j] for i,j in wanted)
                if not np.isfinite(value):
                    value = -1000.
                return float(value), constraints, q['points']
            try:
                result = minimize(lambda z: -evaluate(tuple(z))[0], x, method='SLSQP',
                                  bounds=[(-6,6)]*4+[(-50,50)]*4+[(1e-6,np.pi-1e-6)]*3,
                                  constraints=[{'type':'ineq', 'fun':lambda z:evaluate(tuple(z))[1]}],
                                  options={'ftol':1e-11, 'maxiter':400})
                value, constraints, points = evaluate(tuple(result.x))
                feasible = float(min(constraints))
            except TimeoutError:
                break
            attempts += 1
            if feasible >= -1e-9 and (best is None or value > best['minimum_overlap_score']):
                best = dict(points=points.tolist(), apex=0, minimum_overlap_score=value,
                            minimum_constraint=feasible, optimizer_success=bool(result.success))
            if best and best['minimum_overlap_score'] > 1e-7:
                break
        row = dict(original_class_id=case['original_class_id'], seconds=time.monotonic()-start,
                   attempts=attempts, objective_evaluations=calls, best=best,
                   verdict='Numerical candidate; exact audit required' if best and best['minimum_overlap_score']>0 else 'No positive candidate found; class remains open')
        report['classes'].append(row)
        output.write_text(json.dumps(report, indent=2)+'\n')
        print('class', row['original_class_id'], 'attempts', attempts, 'evaluations', calls,
              'best', None if best is None else best['minimum_overlap_score'], flush=True)
    report['status'] = 'complete'
    output.write_text(json.dumps(report, indent=2)+'\n')
    return report


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--seconds-per-class', type=float, default=120)
    ap.add_argument('--seed', type=int, default=6090941)
    ap.add_argument('--starts', type=int, default=100)
    ap.add_argument('--guard', type=float, default=1e-7)
    ap.add_argument('--classes', type=int, nargs='*')
    ap.add_argument('--output', type=Path, default=Path('n6/results/octa-targeted-session.json'))
    args = ap.parse_args()
    if min(args.seconds_per_class, args.starts, args.guard) <= 0:
        ap.error('Search budgets and guard must be positive')
    run(args.seconds_per_class, args.seed, args.output, args.classes, args.starts, args.guard)
