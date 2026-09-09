"""Reproducible numerical regression for the two-pole cone rules; never a proof."""
import argparse
from collections import Counter
import json
from pathlib import Path

import numpy as np

from durer_small_n.octa import Octa, random_octahedra, sharpest_apex
from n6.patch_budget import pattern


CHECKED_REGIMES = {
    'two-opposite-same', 'two-opposite-facing', 'three-mixed', 'three-same',
}


def angular(octa, k):
    angles, forward, backward, gap = octa.omega, octa.F, octa.B, octa.kw
    j = lambda offset: (k + offset) % 4
    return [
        forward[j(0)] + backward[j(2)] <= angles[j(1)] + 1e-9,
        backward[j(0)] + forward[j(2)] <= angles[j(3)] + gap + 1e-9,
        forward[j(1)] + backward[j(3)] <= angles[j(2)] + 1e-9,
        backward[j(1)] + forward[j(3)] <= gap + angles[j(0)] + 1e-9,
        backward[j(0)] + forward[j(3)] <= gap + 1e-9,
        forward[j(0)] + backward[j(3)] <= angles[j(1)] + angles[j(2)] + 1e-9,
    ]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--samples', type=int, default=2000)
    ap.add_argument('--seed', type=int, default=6091002)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if args.samples <= 0:
        ap.error('Sample count must be positive')
    rng = np.random.default_rng(args.seed)
    counts, first, failure, checked = Counter(), {}, None, 0
    for n, (points, faces, adjacency) in enumerate(random_octahedra(rng, args.samples), 1):
        octa = sharpest_apex(points, faces, adjacency)
        directions = [
            'B' if e > np.pi + 1e-8 else 'F' if f > np.pi + 1e-8 else ''
            for e, f in zip(octa.e, octa.f)
        ]
        regime = pattern(directions)
        counts[regime] += 1
        if regime not in CHECKED_REGIMES:
            continue
        checked += 1
        other = Octa(points, octa.w, faces, adjacency)
        good = [(pole, k) for pole in (octa, other) for k in range(4)
                if all(angular(pole, k))]
        example = dict(points=points[[octa.v, octa.w] + octa.u].tolist(),
                       directions=directions,
                       curvatures=[octa.kv, octa.kw] + octa.ku.tolist())
        first.setdefault(regime, example)
        if not good:
            failure = dict(example, regime=regime, sample=n)
            print('No angular net:', failure, flush=True)
            break
        for pole, k in good:
            overlaps = pole.overlaps(k)
            if overlaps:
                raise ValueError(('Numerical angular false positive', regime, overlaps))
    report = dict(seed=args.seed, samples=n, counts=dict(counts),
                  angular_shapes_checked=checked,
                  checked_regimes=sorted(CHECKED_REGIMES), first=first,
                  no_angular_net=failure,
                  scope='Numerical regression and discovery only; no proof or global coverage estimate')
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'first'}, indent=2), flush=True)


if __name__ == '__main__':
    main()
