"""Replay two-pair certificates against independent all-28-pair certificates."""
import json
from pathlib import Path

from n6.far_pairs import make_certificate, verify
from n6.intervals import set_precision
from n6.polycert import verify as verify_all_pairs

ROOT = Path(__file__).resolve().parent
EXAMPLES = {
    'apex-entry': 'caseB-apex-entry.certificate.json',
    'apex-entry-family': 'caseB-apex-entry-region.certificate.json',
    'radial-family': 'local-gate-radial-family.certificate.json',
    'large-sum': 'local-gate-away.certificate.json',
}


def source(name):
    spec = json.loads((ROOT/'results'/EXAMPLES[name]).read_text())
    if 'selection' not in spec:
        s = spec['local_gate']
        spec['selection'] = dict(apex=s['source'], antipode=s['fan_vertex'],
                                 equator=s['equator'], slit_index=s['slit_index'])
    return spec


def main():
    set_precision(240)
    for name in EXAMPLES:
        original = source(name)
        cert = make_certificate(original)
        report = dict(two_pair_reduction=verify(cert),
                      independent_all_28_pairs=verify_all_pairs(original))
        for suffix, value in [('certificate', cert), ('verification', report)]:
            (ROOT/f'results/far-pair-{name}.{suffix}.json').write_text(json.dumps(value,indent=2)+'\n')
        print(name, report['two_pair_reduction']['parameter_dimension'],
              [(t['fan_angle_sum'], t.get('slit_far_vertex')) for t in report['two_pair_reduction']['small_fan_cases']], flush=True)


if __name__ == '__main__':
    main()
