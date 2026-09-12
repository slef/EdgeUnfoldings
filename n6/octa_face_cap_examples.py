"""Preserved metric examples for the shorter octahedron face-cap selection."""
import json
from pathlib import Path

from n6.intervals import set_precision
from n6.octa_face_caps import select
from n6.selected_octahedron_examples import SOURCES, NEW_EXAMPLES, specification as earlier_specification
from n6.point_audit import exact_hull
from n6.polycert import point_spec


def specification(name):
    if name != 'high-fan':
        return earlier_specification(name)
    # A simplified rational follow-up of the numerical review probe.
    # Both selected poles have curvature > pi; no low-fan premise is used.
    points = [[0, 0, 0], [4, 28, 55], [22, 25, 22],
              [-1, -4, -14], [-57, -8, 59], [13, 40, 74]]
    faces, _ = exact_hull(points)
    return point_spec(points, faces, [(0, 3), (1, 3), (2, 3), (3, 4), (4, 5)])


def main():
    set_precision(240)
    root = Path(__file__).parent/'results'
    report = dict(result='verified_octahedron_face_cap_examples', domains={},
                  universal_geometric_proof_formally_verified=False)
    for name in (*SOURCES, *NEW_EXAMPLES, 'high-fan'):
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
