"""Exact hypotheses of OCTA_SOURCE_CHOICE.md, retaining R but not H.

The written geometric proof is a dependency, not formally verified here.
Explicit all-pair certificates provide an independent check on examples.
"""
from n6.certify import require
from n6.curvature import angle_product,verify_order
from n6.regimes import octahedron_frame,curvature_pi


def verify(spec):
    g,v,w,ring,k,_,_=octahedron_frame(spec)
    order=verify_order(g,[(ring[k],x) for x in ring if x!=ring[k]])
    bands={x:curvature_pi(angle_product(g.p,g.faces,g.h,x)) for x in range(6)}
    high=bands[v] in ('>','=')
    low=all(b in ('<','=') for b in bands.values())
    require(high or low,'Neither source-choice curvature condition is certified')
    return dict(result='verified_source_choice_hypotheses',
                source=v,fan=w,slit=ring[k],equator=ring,
                source_curvature_at_least_pi=high,all_curvatures_at_most_pi=low,
                curvature_comparisons_with_pi=bands,slit_order=order,
                globally_sharpest_source_required=False,
                maximum_curvature_slit_required=True,
                all_28_pairs_proved_by_written_theorem=True,
                proof='OCTA_SOURCE_CHOICE.md',
                scope='The explicit domain satisfies the written source-choice theorem. This is not formal verification of the geometric proof and does not assert every slit works.')


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('certificate',type=Path)
    args=ap.parse_args();spec=json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits',240))
    print(json.dumps(verify(spec),indent=2))
