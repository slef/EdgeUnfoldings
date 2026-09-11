"""Exact examples for the pole-angle and quarter-turn Lemma F theorems."""
import json
from pathlib import Path

from n6.far_projection import verify
from n6.intervals import set_precision
from n6.point_audit import exact_hull, cuts_for
from n6.polycert import point_spec, make_certificate, verify as verify_all_pairs

ROOT = Path(__file__).resolve().parent
EXAMPLES = ('high-curvature', 'low-curvature', 'low-curvature-family', 'obtuse-repaired')


def specification(name):
    if name == 'high-curvature':
        spec = json.loads((ROOT/'results/local-gate-three-chain.certificate.json').read_text())
        s = spec['local_gate']
        # The older certificate's selection predates its change of slit.
        spec['selection'] = dict(apex=s['source'], antipode=s['fan_vertex'],
                                 equator=s['equator'], slit_index=s['slit_index'])
        return spec
    if name in ('low-curvature', 'low-curvature-family'):
        points = [[-1,14,1], [9,-16,14], [-2,-5,-13], [4,-11,17], [10,-2,-5], [7,5,17]]
        v, w, ring, k = 2, 5, [0,3,1,4], 0
    elif name == 'obtuse-repaired':
        points = [[-925,-29,773], [603,1268,302], [-115,1329,-408],
                  [-507,309,-522], [-942,-17,746], [686,365,612]]
        v, w, ring, k = 5, 4, [0,1,2,3], 0
    else:
        raise ValueError('Unknown pole-angle example')
    faces, adj = exact_hull(points)
    spec = point_spec(points, faces, cuts_for(v, ring[k], adj))
    spec['selection'] = dict(apex=v, antipode=w, equator=ring, slit_index=k)
    spec['suggested_fractional_bits'] = 240
    if name.endswith('-family'):
        spec['parameter_box'] = [['-1/10000', '1/10000'] for _ in range(18)]
        for i, point in enumerate(points):
            for j, value in enumerate(point):
                powers = [0]*18
                powers[3*i+j] = 1
                spec['coordinate_polynomials'][i][j] = [[str(value), [0]*18], ['1', powers]]
    return spec


def main():
    set_precision(240)
    for name in EXAMPLES:
        cert = make_certificate(specification(name))
        report = dict(pole_angle_theorem=verify(cert), independent_all_28_pairs=verify_all_pairs(cert))
        for suffix, value in [('certificate', cert), ('verification', report)]:
            (ROOT/f'results/far-projection-{name}.{suffix}.json').write_text(
                json.dumps(value, indent=2)+'\n')
        r = report['pole_angle_theorem']
        print(name, r['parameter_dimension'], [c['method'] for c in r['target_checks']], flush=True)


if __name__ == '__main__':
    main()
