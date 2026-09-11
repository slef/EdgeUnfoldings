"""Rebuild exact illustrations of the complete local theorem, not its proof."""
import json
from pathlib import Path

from n6.intervals import set_precision
from n6.local_lemma import verify
from n6.point_audit import exact_hull
from n6.polycert import point_spec, make_certificate, verify as verify_net

ROOT = Path(__file__).resolve().parent


def obtuse_example():
    points = [[-14,3,-1], [21,29,4], [-21,-28,-19], [-4,-16,10],
              [4,-7,29], [-29,-29,-13]]
    faces, _ = exact_hull(points)
    spec = point_spec(points, faces, [[0,x] for x in (1,4,5,2)]+[[3,1]])
    # The stronger theorem needs only the pole comparison. This source is
    # not globally sharpest; do not label it an example of the original H.
    spec['local_gate'] = dict(source=0, fan_vertex=3, equator=[1,4,5,2],
                              slit_index=0, check_rankings=False)
    spec['suggested_fractional_bits'] = 240
    return make_certificate(spec)


def main():
    set_precision(240)
    for name, cert in [('large-sum', json.loads((ROOT/'results/local-gate-away.certificate.json').read_text())),
                       ('radial-family', json.loads((ROOT/'results/local-gate-radial-family.certificate.json').read_text())),
                       ('obtuse', obtuse_example())]:
        result = verify(cert)
        report = dict(lemma_L=result, independently_checked_net=verify_net(cert))
        if name == 'obtuse':
            (ROOT/'results/lemma-L-obtuse.certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
        (ROOT/f'results/lemma-L-{name}.verification.json').write_text(json.dumps(report,indent=2)+'\n')
        print(name, result['original_pole_triangle_angle_at_source'],
              result['independent_through_fan_cone_check'], flush=True)


if __name__ == '__main__':
    main()
