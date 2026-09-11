"""Exact nonmaximum slit examples for the direct curvature threshold."""
import json
from pathlib import Path
from n6.intervals import set_precision
from n6.low_far_examples import specification as low_spec
from n6.selected_octahedron_examples import specification as selected_spec
from n6.slit_threshold import verify
from n6.polycert import Geometry,make_certificate,verify as all_pairs
from n6.curvature import angle_product,interval_angle_le


def specification(name):
    if name in ('low','low-family'):return low_spec('family' if name.endswith('family') else 'point')
    if name not in ('high','high-family','safe-below-threshold'):raise ValueError('Unknown threshold example')
    if name=='safe-below-threshold':
        spec=selected_spec('high-curvature');s=spec['selection'];k=0
    else:
        spec=selected_spec('curvature-equality');s=spec['selection'];k=3
        # Move the source slightly outward from its exact pi-curvature position.
        spec['coordinate_polynomials'][0]=[[['-1',[]]] for _ in range(3)]
    spec.pop('pair_witnesses',None)
    spec['selection']={**s,'slit_index':k}
    spec['cut_edges']=[[s['apex'],u] for u in s['equator']]+[[s['antipode'],s['equator'][k]]]
    if name=='high-family':
        spec['parameter_box']=[['-1/10000','1/10000'] for _ in range(18)]
        for i,p in enumerate(spec['coordinate_polynomials']):
            for j,c in enumerate(p):
                powers=[0]*18;powers[3*i+j]=1
                spec['coordinate_polynomials'][i][j]=[[c[0][0],[0]*18],['1',powers]]
    return spec


def check_nonmaximum_slit(spec):
    g=Geometry(spec);s=spec['selection'];c=s['equator'][s['slit_index']]
    z={x:angle_product(g.p,g.faces,g.h,x) for x in s['equator']}
    sharper=[x for x in s['equator'] if x!=c and interval_angle_le(z[c],z[x]) is False]
    if not sharper:raise ValueError('Strictly nonmaximum slit must be certified')
    return dict(slit=c,strictly_sharper_equator_vertices=sharper)


def main():
    set_precision(240);root=Path(__file__).parent/'results'
    for name in ('low','low-family','high','high-family'):
        cert=make_certificate(specification(name))
        report=dict(threshold_hypotheses=verify(cert),nonmaximum_slit=check_nonmaximum_slit(cert),
                    independent_all_28_pairs=all_pairs(cert))
        for suffix,data in [('certificate',cert),('verification',report)]:
            (root/f'slit-threshold-{name}.{suffix}.json').write_text(json.dumps(data,indent=2)+'\n')
        print(name,'verified',flush=True)
    from n6.low_local_failure import specification as failure_spec
    from n6.slit_threshold import weighted_slit_pi
    records=[]
    for k in range(4):
        spec=failure_spec();s=spec['selection'];c=s['equator'][k]
        spec['selection']={**s,'slit_index':k}
        spec['cut_edges']=[[s['apex'],u] for u in s['equator']]+[[s['antipode'],c]]
        g=Geometry(spec);totals={x:angle_product(g.p,g.faces,g.h,x) for x in (c,s['antipode'])}
        comparison=weighted_slit_pi(totals[c],totals[s['antipode']])
        record=dict(slit=c,weighted_threshold_comparison=comparison)
        if comparison in ('>','='):
            cert=make_certificate(spec);filename=f'slit-threshold-choice-{c}.certificate.json'
            (root/filename).write_text(json.dumps(cert,indent=2)+'\n')
            record.update(theorem=verify(cert),independent_all_28_pairs=all_pairs(cert),certificate=filename)
        else:
            if comparison!='<':raise ValueError('Failure of this example threshold must be strict')
            record.update(theorem_does_not_apply=True,separate_exact_report='low-local-failure.verification.json')
        records.append(record)
    (root/'slit-threshold-four-choices.verification.json').write_text(json.dumps(
        dict(scope='The four slits at source 5 in one explicit exact octahedron, not a universal count of safe choices.',
             choices=records,threshold_passes=3),indent=2)+'\n')


if __name__=='__main__':main()
