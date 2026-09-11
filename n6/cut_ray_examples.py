"""Replay exact two-cut-segment certificates on existing certified domains."""
import json
from pathlib import Path

from n6.cut_rays import make_certificate, verify
from n6.far_pair_examples import EXAMPLES, source
from n6.intervals import set_precision
from n6.polycert import verify as verify_all_pairs

ROOT = Path(__file__).resolve().parent


def main():
    set_precision(240)
    for name in EXAMPLES:
        original = source(name)
        cert = make_certificate(original)
        report = dict(cut_segment_reduction=verify(cert),
                      independent_all_28_pairs=verify_all_pairs(original))
        for suffix, value in [('certificate', cert), ('verification', report)]:
            (ROOT/f'results/cut-rays-{name}.{suffix}.json').write_text(
                json.dumps(value, indent=2)+'\n')
        r = report['cut_segment_reduction']
        print(name, r['parameter_dimension'], 'rays also clear:',
              r['both_infinite_rays_also_clear'], flush=True)


if __name__ == '__main__':
    main()
