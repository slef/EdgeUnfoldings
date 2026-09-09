"""Read progress measures from saved exact certificates and their replay reports.

This is build-time bookkeeping. It does not replace the geometric verifier.
Proof-obligation statuses are curated separately, with links to their arguments.
"""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from n6.cover import read_cover,summary,leaves


def load_progress(notes,research):
    result=json.loads((notes/'proof_progress.json').read_text())
    results=research/'results'
    def cover(cert_name,report_name):
        cert=read_cover(results/cert_name);report=json.loads((results/report_name).read_text());s=summary(cert)
        assert report['result']=='verified_complete_region_cover'
        assert not s.get('unresolved') and s['parameter_volume_fractions']['certified']=='1'
        assert report['leaves']==s['certified']
        trees={tuple(sorted(map(tuple,node['cuts']))) for node,_,_ in leaves(cert)}
        assert len(trees)==report['distinct_cut_trees']
        assert sum(report['checked_face_pairs'].values())==report['leaves']*len(cert['geometry']['faces'])*(len(cert['geometry']['faces'])-1)//2
        return {**report,**domain(cert['geometry']), 'certificate':cert_name,'report':report_name}
    def domain(g):
        origin=g.get('parameter_origin',[0]*len(g['parameter_box']))
        return dict(parameter_names=g['parameter_names'],
                    center=[str(F(c)+(F(a)+F(b))/2) for c,(a,b) in zip(origin,g['parameter_box'])],
                    half_widths=[str((F(b)-F(a))/2) for a,b in g['parameter_box']])
    result['minus']=cover('minus-merged-cover.certificate.json.gz','minus-merged-cover.verification.json')
    result['prism']=cover('prism-affine-cover.certificate.json.gz','prism-affine-cover.verification.json')
    history=[]
    first=read_cover(results/'minus-wide-affine.certificate.json')
    assert json.loads((results/'minus-wide-affine.verification.json').read_text())['result']=='verified'
    assert domain(first)['center']==result['minus']['center'] and len(set(domain(first)['half_widths']))==1
    history.append(dict(half_width=domain(first)['half_widths'][0],leaves=1,trees=1,report='minus-wide-affine.verification.json'))
    for stem in ['minus-doubled-cover','minus-tripled-cover','minus-quadrupled-cover','minus-merged-cover']:
        data=cover(stem+'.certificate.json.gz',stem+'.verification.json')
        assert len(set(data['half_widths']))==1 and data['center']==result['minus']['center']
        history.append(dict(half_width=data['half_widths'][0],leaves=data['leaves'],trees=data['distinct_cut_trees'],report=data['report']))
    result['minus']['history']=history
    path=results/'prism-balanced-cover.partial.json.gz'
    partial=read_cover(path);s=summary(partial)
    result['prism_partial']={
        **domain(partial['geometry']),
        'candidate_cells':s['certified'],'unresolved_cells':s['unresolved'],
        'candidate_parameter_fraction':s['parameter_volume_fractions']['certified'],
        'unresolved_parameter_fraction':s['parameter_volume_fractions']['unresolved'],
        'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'certificate':path.name,'report':None,
        'verification':'pending',
        'scope':'Structural accounting of saved candidate cells; independent full geometric replay has not completed.'
    }
    return result
