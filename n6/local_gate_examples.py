"""Rebuild exact local-gate examples and a box needing radial separation."""
import json
from pathlib import Path

from n6.intervals import set_precision
from n6.local_gate import analyze, verify
from n6.local_radial import verify as verify_intrusion, verify_clearance
from n6.polycert import make_certificate, verify as verify_net

ROOT = Path(__file__).resolve().parent


def radial_specification(family=False):
    spec = json.loads((ROOT / 'results/local-radial-failure.certificate.json').read_text())
    spec.update(local_gate=dict(source=0, fan_vertex=4, equator=[2,5,1,3], slit_index=0),
                suggested_fractional_bits=240)
    if family:
        spec['local_radial_clearance']['minimum_distance_ratio'] = '6/5'
        spec['parameter_box'] = [['-1/10000', '1/10000'] for _ in range(18)]
        for i, point in enumerate(spec['coordinate_polynomials']):
            for j, coordinate in enumerate(point):
                powers = [0]*18
                powers[3*i+j] = 1
                point[j] = [[coordinate[0][0], [0]*18], ['1', powers]]
    return spec


def three_chain_specification():
    spec = json.loads((ROOT / 'results/three-chain-uncovered.certificate.json').read_text())
    # Retain the same solid but move the fifth cut to the maximum-curvature equator vertex.
    spec.pop('three_chain')
    spec.pop('radial_obstruction')
    spec['cut_edges'] = [[0, x] for x in range(2,6)] + [[1,5]]
    spec['local_gate'] = dict(source=0, fan_vertex=1, equator=[2,3,4,5], slit_index=3)
    return spec


def away_specification():
    spec = json.loads((ROOT / 'results/patch-budget-adjacent-below-pi.certificate.json').read_text())
    spec['cut_edges'] = [[0, x] for x in range(2,6)] + [[1,5]]
    spec['local_gate'] = dict(source=0, fan_vertex=1, equator=[2,3,4,5], slit_index=3)
    return spec


def main():
    set_precision(240)
    for suffix, spec in [('three-chain', three_chain_specification()),
                         ('away', away_specification()),
                         ('radial-point', radial_specification()),
                         ('radial-family', radial_specification(True))]:
        cert = make_certificate(spec)
        gate = analyze(cert) if suffix.startswith('radial') else verify(cert)
        report = dict(local_gate=gate, net=verify_net(cert))
        if suffix.startswith('radial'):
            report.update(angular_intrusion=verify_intrusion(cert), radial_clearance=verify_clearance(cert))
            assert not gate['all_local_pairs_by_gate']
            assert gate['across_slit_cone_test'] is False
            assert gate['through_fan_route_excluded']
        for kind, data in [('certificate', cert), ('verification', report)]:
            (ROOT / f'results/local-gate-{suffix}.{kind}.json').write_text(json.dumps(data, indent=2)+'\n')
        print(suffix, gate['curvature_sum_band'], gate['remaining_local_pairs'], report['net']['result'], flush=True)


if __name__ == '__main__':
    main()
