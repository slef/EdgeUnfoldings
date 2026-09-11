"""Exploratory attacks on the conjectural cut-gap angular inequalities.

Every output is floating-point evidence, never a proof or a certified
counterexample. The exact checker for saved regions is n6.cut_rays.
"""
import argparse
import json
from pathlib import Path

import numpy as np
from durer_small_n import octa as O


def robust_angle(b, a, c):
    x, y = a-b, c-b
    cross = np.cross(x, y) if len(x) == 3 else x[0]*y[1]-x[1]*y[0]
    return np.arctan2(np.linalg.norm(cross), np.dot(x, y))


def evaluate(points):
    structure = O.octa_structure(points)
    if structure is None:
        return None
    o = O.sharpest_apex(points, *structure)
    k = int(np.argmax(o.ku))
    values = [o.B[(k+1)%4]-o.omega[k]-o.kw,
              o.F[(k+2)%4]-o.omega[(k+3)%4]-o.kw]
    # Discourage numerical collapse; these are search guards, not exact bounds.
    guard = max(0., .0005-min(o.kappa.values()))
    edge = min(o.r.min(), o.s.min(), o.l.min())/o.scale
    guard += max(0., .0005-edge)
    area = min(np.linalg.norm(np.cross(points[b]-points[a], points[c]-points[a]))
               for a,b,c in structure[0])/o.scale**2
    guard += max(0., .000005-area)*100
    value = max(values)
    return value-20*guard, dict(value=float(value), guard=float(guard),
                                v=o.v, w=o.w, k=k, ring=o.u,
                                values=list(map(float, values)))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--samples', type=int, default=1500)
    ap.add_argument('--restarts', type=int, default=12)
    ap.add_argument('--steps', type=int, default=1600)
    ap.add_argument('--seed', type=int, default=938583)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    old_angle = O.angle_at
    O.angle_at = robust_angle
    report = dict(scope='Floating-point exploration only; no universal proof or certified counterexample.',
                  seed=args.seed, initial_samples=args.samples,
                  requested_restarts=args.restarts, steps_per_restart=args.steps,
                  objective='max(B[k+1]-omega[k]-kappa_w, F[k+2]-omega[k+3]-kappa_w)',
                  completed=[])
    try:
        seeds = []
        for points, _, _ in O.random_octahedra(rng, args.samples):
            score, _ = evaluate(points)
            seeds.append((score, points))
        seeds.sort(key=lambda q: -q[0])

        def objective(points):
            e = evaluate(points)
            return None if e is None else e[0]

        for run, (_, points) in enumerate(seeds[:args.restarts]):
            points, _ = O.hill_climb(objective, points, rng, steps=args.steps, step=.07)
            result = evaluate(points)[1]
            result['points'] = points.tolist()
            report['completed'].append(result)
            args.output.write_text(json.dumps(report, indent=2)+'\n')
            print(run, result['value'], 'guard', result['guard'], flush=True)
            if result['value'] > 1e-5 and result['guard'] == 0:
                break
    finally:
        O.angle_at = old_angle


if __name__ == '__main__':
    main()
