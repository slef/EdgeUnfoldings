"""Reproduce exact selected-net examples for the paired-pole theorem."""
import json
from pathlib import Path
from n6.intervals import set_precision
from n6.paired_poles import select,wide_identities
from n6.octa_face_cap_examples import specification,SOURCES,NEW_EXAMPLES
from n6.minus_complementary_examples import specification as minus
from n6.trees import incidence


def main():
    set_precision(240);root=Path(__file__).parent/'results'
    report=dict(scope='Exact identity and explicit-domain net checks; not formal verification of the universal geometry.',
                identities=wide_identities(),selected_nets={},unresolved_uniform_choices={})
    tasks=[]
    for name in (*SOURCES,*NEW_EXAMPLES,'high-fan'):
        spec=specification(name);inc=incidence(spec['faces'])
        pairs=[(v,w) for v in range(6) for w in range(v+1,6) if (v,w) not in inc]
        tasks.extend(('octa-'+name+'-pair'+str(v)+str(w),spec,(v,w)) for v,w in pairs)
    for kind,family in [('strict',False),('strict',True),('reflected',False),('boundary',False),('fallback',False),('fallback',True),('fallback_reflected',False)]:
        tasks.append(('minus-'+kind+('-family' if family else ''),minus(kind,family),(0,1)))
    tasks.append(('former-cap-failure',json.loads((root/'octa-unranked-cap-failure.certificate.json').read_text()),(3,5)))
    for name,spec,pair in tasks:
        try:r=select(spec,pair)
        except ValueError as e:
            report['unresolved_uniform_choices'][name]=str(e);print(name,'UNRESOLVED',e,flush=True);continue
        cert=r.pop('certificate');filename='paired-poles-'+name+'.certificate.json'
        (root/filename).write_text(json.dumps(cert,indent=2)+'\n');r['certificate_file']=filename
        report['selected_nets'][name]=r
        print(name,'verified',flush=True)
    report['selected_nets_checked']=len(report['selected_nets'])
    report['uniform_choices_unresolved']=len(report['unresolved_uniform_choices'])
    (root/'paired-poles.verification.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':main()
