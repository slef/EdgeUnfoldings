"""Exact one-sided Case A hypotheses, without a source or slit ranking.

The written planar lemma is CASE_A_ONE_SIDED.md. This verifies its use on
one specified opposite-petal pair of an exact convex octahedral domain;
it does not claim that the rest of that net is safe.
"""
from n6.certify import require
from n6.curvature import angle_product,face_angle,cmul,conjugate,cdet
from n6.intervals import norm2,sub
from n6.regimes import octahedron_frame,two_curvatures_angle


def comparison(x):
    if x.lo==x.hi==0:return '='
    if x.lo>0:return '>'
    if x.hi<0:return '<'
    return None


def planar_tests(alpha,beta,left_angle,right_angle,s,sprime,ell):
    """Tests assuming alpha,beta>0 and theta=alpha+beta<pi.

    Phases may have any positive scale. Multiplying by their norms retains
    that scale in the sine-rule length comparison; no inverse trig is used.
    Return sufficient predicates, not a converse test for actual overlap.
    """
    theta=cmul(alpha,beta)
    short_left=ell*beta[1]*norm2(alpha).sqrt()-s*theta[1]
    short_right=ell*alpha[1]*norm2(beta).sqrt()-sprime*theta[1]
    nowrap_left=cdet(left_angle,theta);nowrap_right=cdet(right_angle,theta)
    def ge(x):return x.lo>=0
    return dict(left_short_comparison=comparison(short_left),
                right_short_comparison=comparison(short_right),
                left_no_wrap_comparison=comparison(nowrap_left),
                right_no_wrap_comparison=comparison(nowrap_right),
                left_condition=ge(short_left) and ge(nowrap_left),
                right_condition=ge(short_right) and ge(nowrap_right),
                earlier_two_angle_condition=ge(nowrap_left) and ge(nowrap_right))


def classify(spec):
    g,v,w,ring,k,V,W=octahedron_frame(spec)
    i=spec['case_A_triple_index']
    require(type(i) is int and i in (k,(k+1)%4),'Expected an actual opened opposite-petal triple')
    j,h=(i+1)%4,(i+2)%4;u,up=ring[j],ring[h]
    totals={x:angle_product(g.p,g.faces,g.h,x) for x in (u,up)}
    def angle(f,x):return face_angle(g.p,g.faces[f],g.h[f],x)
    band=two_curvatures_angle(totals[u],totals[up],angle(V[j],v))
    require(band=='<','The specified pair is not certified in strict Case A')
    alpha=cmul(angle(V[j],u),conjugate(totals[u]))
    beta=cmul(angle(V[j],up),conjugate(totals[up]))
    tests=planar_tests(alpha,beta,angle(V[i],v),angle(V[h],v),
                       norm2(sub(g.p[v],g.p[u])).sqrt(),
                       norm2(sub(g.p[v],g.p[up])).sqrt(),
                       norm2(sub(g.p[u],g.p[up])).sqrt())
    return dict(**tests,source=v,fan=w,equator=ring,slit_index=k,
                triple_index=i,pair=[V[i],V[h]],case_A_comparison=band)


def verify(spec):
    report=classify(spec)
    require(report['left_condition'] or report['right_condition'],
            'Neither one-sided Case A separator is certified')
    return dict(result='verified_one_sided_case_A_pair',**report,
                pair_nonoverlap_by_written_lemma=True,whole_net_claimed=False,
                proof='CASE_A_ONE_SIDED.md',
                scope='This exact domain satisfies the one-sided planar separator for one actual opposite-petal pair. The written proof is not formally verified. A failed sufficient test does not certify overlap.')


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    args=ap.parse_args();spec=json.loads(args.input.read_text())
    set_precision(spec.get('suggested_fractional_bits',240))
    print(json.dumps(verify(spec),indent=2))
