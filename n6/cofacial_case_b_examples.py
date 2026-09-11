"""Exact original-face domains for the cofacial sharp-route Case B theorem."""
import json
from pathlib import Path
from n6.cofacial_star_reduction import verify_case_B
from n6.families import MINUS_FACES
from n6.intervals import set_precision
from n6.low_curvature_examples import specification as low_spec
from n6.polycert import point_spec,make_certificate,verify as all_pairs
from n6.polynomials import Poly

CUTS={'minus':[[0,2],[0,3],[0,4],[0,5],[1,2]],
      'prism':[[0,1],[1,2],[1,3],[1,4],[2,5]]}


def specification(kind,region=False):
    if kind=='minus_boundary':
        return point_spec([[3,0,3],[3,3,0],[0,0,0],[6,3,3],[0,3,3],[2,4,4]],
                          MINUS_FACES,CUTS['minus'])
    spec=low_spec(kind,region);n=len(spec['parameter_box'])
    if region:spec['arithmetic_mode']='affine'
    axis=[-1,1,0] if kind=='minus' else [1,2,2]
    rows=[[Poly(n,q) for q in row] for row in spec['coordinate_polynomials']]
    spec['coordinate_polynomials']=[[(row[i]+2*axis[i]*sum(axis[j]*row[j] for j in range(3))).json()
                                    for i in range(3)] for row in rows]
    spec['cut_edges']=CUTS[kind]
    return spec


def main():
    set_precision(240);root=Path(__file__).parent/'results'
    for kind,region in [('minus',False),('minus',True),('prism',False),('prism',True),('minus_boundary',False)]:
        cert=make_certificate(specification(kind,region))
        report=dict(hypotheses=verify_case_B(cert),independent_all_original_pairs=all_pairs(cert))
        name='cofacial-case-B-'+kind.replace('_','-')+('-family' if region else '')
        for suffix,data in [('certificate',cert),('verification',report)]:
            (root/f'{name}.{suffix}.json').write_text(json.dumps(data,indent=2)+'\n')
        print(name,'verified',flush=True)


if __name__=='__main__':main()
