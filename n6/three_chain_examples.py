"""Rebuild the exact three-chain illustrations and their independent net checks."""
import json
from pathlib import Path

from n6.intervals import set_precision
from n6.polycert import point_spec, make_certificate, verify as verify_net
from n6.three_chain import analyze, verify, audit_curvature_pair_failure

ROOT = Path(__file__).resolve().parent
POINTS = {
    'switch': [[-1603,-427,-4399],[1423,191,3156],[2180,377,4998],
               [549,597,2992],[-1410,-369,-3561],[-1139,-370,-3186]],
    'simple': [[-1583,-450,-4406],[1389,108,3232],[2273,320,5030],
               [529,601,3029],[-1430,-383,-3559],[-1143,-410,-3116]],
}


def specification(criterion):
    faces = [[1,2+i,2+(i+1)%4] for i in range(4)] + [[0,2+(i+1)%4,2+i] for i in range(4)]
    spec = point_spec(POINTS[criterion], faces, [[0,u] for u in range(2,6)]+[[1,4]])
    spec.update(patch_budget=dict(source=0, opposite=1, equator=[2,3,4,5], sharpest_pole=0),
                three_chain=dict(criterion=criterion), suggested_fractional_bits=240)
    return spec


def family_specification():
    spec = specification('switch')
    spec['parameter_box'] = [['-1/100', '1/100'] for _ in range(18)]
    for i, point in enumerate(POINTS['switch']):
        for j, value in enumerate(point):
            powers = [0]*18
            powers[3*i+j] = 1
            spec['coordinate_polynomials'][i][j] = [[str(value), [0]*18], ['1', powers]]
    return spec


def save(spec, suffix):
    cert = make_certificate(spec)
    report = dict(hypotheses=verify(cert), net=verify_net(cert),
                  older_curvature_criterion=audit_curvature_pair_failure(cert))
    for kind, data in [('certificate', cert), ('verification', report)]:
        (ROOT / f'results/three-chain-{suffix}.{kind}.json').write_text(json.dumps(data, indent=2)+'\n')
    print(suffix, report['hypotheses']['result'], report['net']['result'])


def main():
    set_precision(240)
    for criterion in POINTS:
        save(specification(criterion), criterion)
    save(family_specification(), 'family')
    previous = json.loads((ROOT / 'results/patch-budget-three-same.certificate.json').read_text())
    previous_report = dict(source_certificate='patch-budget-three-same.certificate.json',
                           hypotheses=analyze(previous), net=verify_net(previous))
    assert previous_report['hypotheses']['simple_criterion_certified']
    (ROOT / 'results/three-chain-previous-example.verification.json').write_text(json.dumps(previous_report, indent=2)+'\n')
    cert = json.loads((ROOT / 'results/sector-three-patch-radial-failure.certificate.json').read_text())
    selection = cert['selection']
    cert['patch_budget'] = dict(source=selection['apex'], opposite=selection['antipode'],
                                equator=selection['equator'], sharpest_pole=selection['apex'])
    cert['three_chain'] = dict(criterion='switch')
    cert['source_certificate'] = 'sector-three-patch-radial-failure.certificate.json'
    (ROOT / 'results/three-chain-uncovered.certificate.json').write_text(json.dumps(cert, indent=2)+'\n')
    report = dict(source_certificate=cert['source_certificate'],
                  hypotheses=analyze(cert), net=verify_net(cert))
    assert not report['hypotheses']['subfamily_hypotheses_certified']
    (ROOT / 'results/three-chain-uncovered.verification.json').write_text(json.dumps(report, indent=2)+'\n')
    print('uncovered example: sufficient hypotheses fail; its selected net still verifies')


if __name__ == '__main__':
    main()
