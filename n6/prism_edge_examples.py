"""Reproduce the independent seven-candidate checks retained with the proof."""
import json
from pathlib import Path
from n6.intervals import set_precision
from n6.prism_edge_theorem import select
from n6.prism_angle_identities import verify as identities

INPUTS=['prism-two-pair-failure','prism-one-sharp-failure',
        'original-rule-prism-selected-failure','cofacial-case-A-prism-family',
        'prism-complementary-family','prism-two-sharp-family']


def main():
    set_precision(240);root=Path(__file__).parent/'results';reports={}
    for name in INPUTS:
        spec=json.loads((root/(name+'.certificate.json')).read_text())
        report=select(spec);certificate=report.pop('certificate');reports[name]=report
        (root/('prism-seven-'+name+'.certificate.json')).write_text(json.dumps(certificate,indent=2)+'\n')
        print(name,report['candidate'],'verified',flush=True)
    (root/'prism-seven-candidates.verification.json').write_text(json.dumps(reports,indent=2)+'\n')
    (root/'prism-angle-identities.verification.json').write_text(json.dumps(identities(),indent=2)+'\n')


if __name__=='__main__':main()
