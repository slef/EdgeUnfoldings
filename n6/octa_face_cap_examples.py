"""Preserved metric examples for the shorter octahedron face-cap selection."""
import json
from pathlib import Path

from n6.intervals import set_precision
from n6.octa_face_caps import select
from n6.selected_octahedron_examples import SOURCES, NEW_EXAMPLES, specification


def main():
    set_precision(240)
    root = Path(__file__).parent/'results'
    report = dict(result='verified_octahedron_face_cap_examples', domains={},
                  universal_geometric_proof_formally_verified=False)
    for name in (*SOURCES, *NEW_EXAMPLES):
        result = select(specification(name))
        certificate = result.pop('certificate')
        filename = 'octa-face-cap-'+name+'.certificate.json'
        (root/filename).write_text(json.dumps(certificate, indent=2)+'\n')
        result['certificate_file'] = filename
        report['domains'][name] = result
        print(name, 'all 28 pairs verified', flush=True)
    report['domains_checked'] = len(report['domains'])
    (root/'octa-face-cap-rule.verification.json').write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
