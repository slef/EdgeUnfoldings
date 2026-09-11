"""Replay preserved prism domains using the new cap rule; never replace old evidence."""
import json
from pathlib import Path

from n6.intervals import set_precision
from n6.prism_cap_rule import identities, select


NAMES = (
    'low-curvature-prism', 'low-curvature-prism-family',
    'prism-two-pair-failure', 'prism-one-sharp-failure',
    'prism-switch-sharp-point', 'prism-switch-sharp-family',
    'prism-switch-gate-point', 'prism-switch-gate-family',
    'prism-two-sharp-one-boundary', 'prism-two-sharp-both-boundaries',
    'prism-complementary-point', 'prism-complementary-family',
    'prism-complementary-reflected', 'original-rule-prism-selected-failure',
    'cofacial-case-A-prism-family',
)


def main():
    set_precision(240)
    root = Path(__file__).parent/'results'
    report = dict(result='verified_prism_cap_rule_examples', algebra=identities(),
                  domains={}, universal_geometric_proof_formally_verified=False)
    for name in NAMES:
        result = select(json.loads((root/(name+'.certificate.json')).read_text()))
        certificate = result.pop('certificate')
        out = 'prism-cap-'+name
        (root/(out+'.certificate.json')).write_text(json.dumps(certificate, indent=2)+'\n')
        result['certificate_file'] = out+'.certificate.json'
        report['domains'][name] = result
        print(name, result['selection']['branch'], result['selected_candidate'], flush=True)
    report['domains_checked'] = len(report['domains'])
    (root/'prism-cap-rule.verification.json').write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
