"""Exact positive families and failures of a deterministic original-edge rule."""
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
from n6.certify import require
from n6.curvature import interval_angle_le
from n6.families import MINUS_FACES,PRISM_FACES
from n6.flat_octahedron import original_candidates,curvature_bands
from n6.intervals import set_precision
from n6.low_curvature_examples import specification as low_spec
from n6.original_edge_rule import verify as rule_verify
from n6.polycert import Geometry,point_spec,make_certificate,make_overlap,verify,verify_overlap
from n6.polynomials import Poly
from n6.prism_paths import polygon_angle_product

ROOT=Path(__file__).parent/'results'


def specification(kind,region=False):
    spec=low_spec(kind,region);n=len(spec['parameter_box'])
    if region:spec['arithmetic_mode']='affine'
    axis=[-1,1,0] if kind=='minus' else [-1,-1,1]
    rows=[[Poly(n,q) for q in row] for row in spec['coordinate_polynomials']]
    spec['coordinate_polynomials']=[[(row[i]+axis[i]*sum(axis[j]*row[j] for j in range(3))).json()
                                    for i in range(3)] for row in rows]
    spec['cut_edges']=([[0,2],[0,3],[0,4],[0,5],[1,2]] if kind=='minus'
                       else [[0,3],[1,3],[2,5],[3,4],[3,5]])
    return spec


def failure_specification(kind):
    report=json.loads((ROOT/f'original-rule-{kind}-probe.json').read_text())
    ex=report['examples']['selected_failure'];t=report['trees'][ex['selected_tree']]
    points=[[str(F(x,d)) for x in row] for row,d in zip(ex['numerators'],ex['denominators'])]
    spec=point_spec(points,MINUS_FACES if kind=='minus' else PRISM_FACES,t['cuts'])
    spec['original_rule_selection']={k:t[k] for k in ('source','fan','slit')}
    repair=deepcopy(spec);repair.pop('original_rule_selection')
    repair['cut_edges']=report['trees'][ex['best_net_tree']]['cuts']
    return spec,repair


def verify_selected_failure(cert):
    g=Geometry(cert);family,trees=original_candidates(g.faces)
    chosen=cert['original_rule_selection'];v,w,c=(chosen[x] for x in ('source','fan','slit'))
    options=[t for t in trees if t['source']==v]
    require(any(t['fan']==w and t['slit']==c and t['cuts']==sorted(map(tuple,cert['cut_edges']))
                for t in options),'Selected original tree mismatch')
    totals={x:polygon_angle_product(g,x) for x in range(6)}
    def sharper(x,y):
        require(interval_angle_le(totals[x],totals[y]) is True and
                interval_angle_le(totals[y],totals[x]) is False,
                'Strict curvature ranking is not certified')
    sources=sorted({t['source'] for t in trees})
    for x in sources:
        if x!=v:sharper(v,x)
    allowed=sorted({t['slit'] for t in options})
    for x in allowed:
        if x!=c:sharper(c,x)
    forbidden=[b if a==w else a for a,b in family['artificial_diagonals'] if w in (a,b)]
    require(len(forbidden)==1,'Expected exactly one artificial fifth-edge option')
    sharper(forbidden[0],c)
    overlap=verify_overlap(cert)
    return dict(result='verified_sharper_original_source_allowed_maximum_failure',
                **chosen,source_candidates=sources,allowed_slit_candidates=allowed,
                forbidden_slit=forbidden[0],forbidden_strictly_sharper_than_allowed=True,
                rankings_strict=True,overlap=overlap,full_n6_refuted=False,
                scope='This deterministic selection rule fails. A different original tree on the same solid has an independent nonoverlap certificate.')


def main():
    set_precision(240)
    for kind in ('minus','prism'):
        for region in (False,True):
            label=f'original-rule-{kind}'+('-family' if region else '')
            cert=make_certificate(specification(kind,region))
            g=Geometry(cert);_,trees=original_candidates(g.faces);bands=curvature_bands(g)
            require(all(bands[t['source']]=='<' for t in trees),'An old high source is eligible')
            require('>' in bands.values(),'Old all-low condition applies')
            report=dict(new_rule=rule_verify(cert),independent_all_original_pairs=verify(cert),
                        all_old_candidates_fail_source_condition=True)
            for suffix,data in [('certificate',cert),('verification',report)]:
                (ROOT/f'{label}.{suffix}.json').write_text(json.dumps(data,indent=2)+'\n')
            print(label,'verified',flush=True)
        spec,repair=failure_specification(kind);cert=None
        for a in range(len(spec['faces'])):
            for b in range(a+1,len(spec['faces'])):
                try:cert=make_overlap(spec,a,b)
                except ValueError:continue
                break
            if cert is not None:break
        require(cert is not None,'No exact overlap found')
        failure=verify_selected_failure(cert);repair_cert=make_certificate(repair)
        for label,data in [('selected-failure.certificate',cert),('repair.certificate',repair_cert),
                           ('selection.verification',dict(failure=failure,repair=verify(repair_cert)))]:
            (ROOT/f'original-rule-{kind}-{label}.json').write_text(json.dumps(data,indent=2)+'\n')
        print(kind,'selection failure and repair verified',flush=True)


if __name__=='__main__':main()
