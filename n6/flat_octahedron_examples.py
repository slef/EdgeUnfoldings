"""Exact original-face boundary and high-curvature examples with flat hinges."""
import json
from pathlib import Path
from n6.families import MINUS_FACES,PRISM_FACES
from n6.low_curvature_examples import specification as low_spec
from n6.flat_octahedron import (original_candidates,verify_fixed_tree,verify_low_existence,
                                curvature_bands)
from n6.polycert import point_spec,make_certificate,verify as all_pairs,Geometry
from n6.polynomials import Poly
from n6.intervals import set_precision


def specification(name,region=False):
    kind='minus' if name.startswith('minus') else 'prism'
    if name.endswith('boundary'):
        if region:raise ValueError('An exact boundary point is not a surrounding all-low box')
        points=([[10,10,0],[10,0,10],[0,0,0],[20,10,10],[0,10,10],[10,15,15]] if kind=='minus'
                else [[0,0,0],[5,5,0],[5,0,5],[0,5,5],[6,10,6],[6,5,11]])
        faces=[list(reversed(f)) for f in (MINUS_FACES if kind=='minus' else PRISM_FACES)]
        _,trees=original_candidates(faces);spec=point_spec(points,faces,trees[0]['cuts'])
    elif name.endswith('high'):
        spec=low_spec(kind,region);n=len(spec['parameter_box'])
        if region:spec['arithmetic_mode']='affine'
        axis=[1,1,-1] if kind=='minus' else [0,1,-1]
        p=[[Poly(n,q) for q in row] for row in spec['coordinate_polynomials']]
        # Positive-definite affine stretch I+3*a*a^T preserves original facets.
        spec['coordinate_polynomials']=[[(row[i]+3*axis[i]*sum(axis[j]*row[j] for j in range(3))).json()
                                         for i in range(3)] for row in p]
    else:raise ValueError('Unknown flat-hinge example')
    spec['suggested_fractional_bits']=240
    _,trees=original_candidates(spec['faces'])
    for t in trees:
        spec['cut_edges']=[list(e) for e in t['cuts']]
        try:
            report=verify_fixed_tree(spec)
            if name.endswith('high') and not report['source_curvature_at_least_pi']:continue
            make_certificate(spec)
        except ValueError:continue
        return spec
    raise ValueError('No example tree is certified')


def main():
    set_precision(240);root=Path(__file__).parent/'results'
    for name,region in [('minus-boundary',False),('prism-boundary',False),
                        ('minus-high',False),('prism-high',False),
                        ('minus-high',True),('prism-high',True)]:
        label=name+('-family' if region else '')
        cert=make_certificate(specification(name,region))
        report=dict(fixed_original_tree=verify_fixed_tree(cert),independent_all_original_pairs=all_pairs(cert))
        if name.endswith('boundary'):report['closed_low_family']=verify_low_existence(cert)
        for suffix,data in [('certificate',cert),('verification',report)]:
            (root/f'flat-hinges-{label}.{suffix}.json').write_text(json.dumps(data,indent=2)+'\n')
        print(label,'verified',flush=True)


if __name__=='__main__':main()
