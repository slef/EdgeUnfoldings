"""Exact hypotheses for the original two-pair net in PRISM_TWO_SHARP_ENDS.md.

This checks an explicit domain against a written theorem. It does not formally
verify the theorem, and numerical experiments are not proof premises.
"""
from fractions import Fraction as F
import json
from pathlib import Path
from n6.certify import edge, require
from n6.families import PRISM_FACES, PRISM_CUTS, region, center_parameters
from n6.flat_octahedron import curvature_bands
from n6.polycert import Geometry, point_spec, make_certificate, verify as all_pairs
from n6.polynomials import Poly
from n6.trees import tree_data


def verify(spec):
    g=Geometry(spec)
    require(tuple(g.faces)==PRISM_FACES,'Expected the stated original prism face labels')
    require(sorted(edge(*e) for e in spec['cut_edges'])==list(PRISM_CUTS),
            'Expected the original two-pair cut tree')
    bands=curvature_bands(g)
    require(all(bands[x] in ('>','=') for x in (2,5)),
            'Both end curvatures >= pi must be certified')
    remaining=tree_data(g.faces,PRISM_CUTS)['pairs']
    require(remaining==[(0,5),(1,3)],'Unexpected residual face pairs')
    return dict(result='verified_prism_two_sharp_ends',
        curvature_comparisons_with_pi=bands,cut_edges=[list(e) for e in PRISM_CUTS],
        residual_pairs=[list(p) for p in remaining],original_faces_remain_whole=True,
        equality_included=True,whole_net_safe_by_written_theorem=True,
        full_prism_type_proved=False,full_n6_proved=False,proof='PRISM_TWO_SHARP_ENDS.md',
        scope='Exact hypotheses on this explicit original-face domain. The written geometric proof awaits independent review and is not formally verified.')


def specification(kind='point'):
    if kind in ('point','family'):
        if kind=='point':
            p=[[5,0,5],[0,5,5],[0,0,0],[6,0,15],[0,5,15],[0,0,20]]
            spec=point_spec(p,PRISM_FACES,PRISM_CUTS)
        else:
            # Axial chart: the two quads stay in the planes spanned by 25 and
            # their lower edge. Nine independent shape parameters, modulo
            # Euclidean similarities, retain the original facet identities.
            values=['1','0','1','1','6/5','3','1','3','4']
            radius=F(1,1000)
            box=[[str(F(x)-radius),str(F(x)+radius)] for x in values]
            z0,x,y,z1,A,z3,C,z4,h=[Poly.variable(9,i) for i in range(9)]
            zero=Poly.constant(9,0);one=Poly.constant(9,1)
            p=[(one,zero,z0),(x,y,z1),(zero,zero,zero),
               (A,zero,z3),(C*x,C*y,z4),(zero,zero,h)]
            spec=center_parameters(region(box,p,PRISM_FACES,PRISM_CUTS,
                    ('z0','x1','y1','z1','x3','z3','radial_ratio4','z4','height5')))
            spec['arithmetic_mode']='affine'
    elif kind in ('one_boundary','both_boundaries'):
        # At 2, all three original facet angles are exactly 60 degrees.
        # The both-boundaries model also has three 60-degree angles at 5.
        p=([[4,0,4],[4,4,0],[0,0,0],[5,8,13],[4,12,8],[0,16,16]]
           if kind=='one_boundary' else
           [[4,0,4],[4,4,0],[0,0,0],[5,11,16],[4,16,12],[0,16,16]])
        spec=point_spec(p,PRISM_FACES,PRISM_CUTS)
    else:raise ValueError('Unknown example kind')
    return {**spec,'suggested_fractional_bits':240}


def main():
    from n6.intervals import set_precision
    set_precision(240);root=Path(__file__).parent/'results'
    for kind in ('point','family','one_boundary','both_boundaries'):
        cert=make_certificate(specification(kind))
        report=dict(hypotheses=verify(cert),independent_all_original_pairs=all_pairs(cert))
        name='prism-two-sharp-'+kind.replace('_','-')
        for suffix,data in [('certificate',cert),('verification',report)]:
            (root/f'{name}.{suffix}.json').write_text(json.dumps(data,indent=2)+'\n')
        print(name,'verified',flush=True)


if __name__=='__main__':main()
