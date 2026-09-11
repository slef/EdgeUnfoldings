"""Three-local-pair certificates at a slit satisfying neither H nor R."""
import json
from pathlib import Path
from n6.intervals import set_precision
from n6.selected_octahedron_examples import specification as selected_spec
from n6.low_far import make_certificate,verify
from n6.polycert import Geometry,make_certificate as all_certificate,verify as all_pairs
from n6.curvature import angle_product,interval_angle_le


def specification(name):
    if name not in ('point','family'):raise ValueError('Unknown low-far example')
    spec=selected_spec('low-curvature'+('-family' if name=='family' else ''))
    spec.pop('pair_witnesses',None)
    spec['selection']=dict(apex=0,antipode=1,equator=[2,4,5,3],slit_index=1)
    spec['cut_edges']=[[0,u] for u in (2,4,5,3)]+[[1,4]]
    return spec


def check_strict_rank_failures(spec):
    g=Geometry(spec);z={x:angle_product(g.p,g.faces,g.h,x) for x in (0,2,4)}
    # An inconclusive comparison is not evidence of a failed ranking.
    if not all(interval_angle_le(z[x],z[2]) is False for x in (0,4)):
        raise ValueError('Strict failure of H and R must both be certified')
    return dict(H_fails=True,R_fails=True,source=0,slit_vertex=4,
                vertex_strictly_sharper_than_both=2)


def main():
    set_precision(240);root=Path(__file__).parent/'results'
    for name in ('point','family'):
        spec=specification(name);cert=make_certificate(spec)
        full=all_certificate(spec)
        report=dict(conditional_theorem=verify(cert),
                    strict_rank_failures=check_strict_rank_failures(cert),
                    independent_all_28_pairs=all_pairs(full))
        for suffix,data in [('certificate',cert),('all-pairs.certificate',full),('verification',report)]:
            (root/f'low-far-{name}.{suffix}.json').write_text(json.dumps(data,indent=2)+'\n')
        print(name,'verified',flush=True)


if __name__=='__main__':main()
