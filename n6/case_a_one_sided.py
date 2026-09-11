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


def wide_planar_tests(alpha,beta,left_angle,right_angle,s,sprime,ell):
    """Wider sufficient test from CASE_A_WIDE_CONES.md.

    Assumes the same strict Case A geometry and lambda+rho<pi+theta.
    The latter follows from positive source curvature for actual petals.
    No angle-product wrapping or approximate inverse trig is used.
    """
    tests=planar_tests(alpha,beta,left_angle,right_angle,s,sprime,ell)
    theta=cmul(alpha,beta)
    def half_bound(angle):
        if angle[0].lo>=0:return '>'  # Nonobtuse angle; the bound exceeds pi/2.
        if angle[0].hi<0:
            square=cmul(angle,angle)
            return comparison(cdet((-square[0],-square[1]),theta))
        return None
    left,right=half_bound(left_angle),half_bound(right_angle)
    return dict(**tests,left_wide_angle_comparison=left,right_wide_angle_comparison=right,
                both_short_condition=tests['left_short_comparison'] in ('>','=') and tests['right_short_comparison'] in ('>','='),
                left_wide_condition=tests['left_short_comparison'] in ('>','=') and left in ('>','='),
                right_wide_condition=tests['right_short_comparison'] in ('>','=') and right in ('>','='))


def triangle_planar_tests(alpha,beta,left_angle,right_angle,s,sprime,ell):
    """Support-triangle bound from CASE_A_SUPPORT_TRIANGLE.md."""
    tests=wide_planar_tests(alpha,beta,left_angle,right_angle,s,sprime,ell)
    theta=cmul(alpha,beta)
    def bound(angle,total):
        # total is theta+alpha or theta+beta, strictly between 0 and 2pi.
        if total[1].hi<=0 or angle[0].lo>=0:return '>'
        if total[1].lo>0 and angle[0].hi<0:
            square=cmul(angle,angle)
            return comparison(cdet((-square[0],-square[1]),total))
        return None
    left=bound(left_angle,cmul(theta,alpha))
    right=bound(right_angle,cmul(theta,beta))
    return dict(**tests,left_triangle_angle_comparison=left,right_triangle_angle_comparison=right,
                left_triangle_condition=tests['left_short_comparison'] in ('>','=') and left in ('>','='),
                right_triangle_condition=tests['right_short_comparison'] in ('>','=') and right in ('>','='))


def length_planar_tests(alpha,beta,left_angle,right_angle,s,sprime,ell):
    """Exact full-apex-cone separators from CASE_A_LENGTH_SEPARATORS.md.

    The geometric premises are the same as wide_planar_tests. Positive
    phase scales are retained in every sine product. Failure means that
    these unbounded cones have not been separated, not that faces overlap.
    """
    tests=triangle_planar_tests(alpha,beta,left_angle,right_angle,s,sprime,ell)
    theta=cmul(alpha,beta)
    na,nb=norm2(alpha).sqrt(),norm2(beta).sqrt();nt=na*nb
    A=ell*beta[1]*na-s*theta[1]
    B=sprime*theta[1]-ell*alpha[1]*nb
    def margin(angle,left):
        order=cdet(angle,theta)
        if order.lo>=0:return A if left else -B
        if order.hi<=0:
            return A*angle[1]*nt-B*cdet(theta,angle) if left else A*cdet(theta,angle)-B*angle[1]*nt
        return None
    lm,rm=margin(left_angle,True),margin(right_angle,False)
    return dict(**tests,left_length_margin=comparison(lm) if lm is not None else None,
                right_length_margin=comparison(rm) if rm is not None else None,
                left_length_condition=lm is not None and lm.lo>=0,
                right_length_condition=rm is not None and rm.lo>=0)


def classify(spec,wide=False,lengths=False):
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
    test=length_planar_tests if lengths else wide_planar_tests if wide else planar_tests
    tests=test(alpha,beta,angle(V[i],v),angle(V[h],v),
                       norm2(sub(g.p[v],g.p[u])).sqrt(),
                       norm2(sub(g.p[v],g.p[up])).sqrt(),
                       norm2(sub(g.p[u],g.p[up])).sqrt())
    result=dict(**tests,source=v,fan=w,equator=ring,slit_index=k,
                triple_index=i,pair=[V[i],V[h]],case_A_comparison=band)
    if wide or lengths:result['middle_nonobtuse_condition']=angle(V[j],v)[0].lo>=0
    return result


def verify_lengths(spec):
    report=classify(spec,lengths=True)
    require(report['left_length_condition'] or report['right_length_condition'],
            'Neither actual-length Case A separator is certified')
    return dict(result='verified_length_case_A_pair',**report,
                pair_nonoverlap_by_written_lemma=True,whole_net_claimed=False,
                angle_sum_condition='Follows strictly from positive source curvature and the fourth petal angle.',
                proof='CASE_A_LENGTH_SEPARATORS.md',
                scope='Actual edge lengths separate the full apex cones for this specified pair. A failed sufficient test does not certify finite-face overlap.')


def verify_wide(spec):
    report=classify(spec,wide=True)
    require(any(report[key] for key in ('left_wide_condition','right_wide_condition','both_short_condition','middle_nonobtuse_condition')),
            'Neither wider Case A separator is certified')
    return dict(result='verified_wider_case_A_pair',**report,
                pair_nonoverlap_by_written_lemma=True,whole_net_claimed=False,
                angle_sum_condition='Follows strictly from positive source curvature and the fourth petal angle.',
                proof='CASE_A_WIDE_CONES.md',
                scope='This exact domain satisfies the wider planar separator for the specified pair, not a claim about all low-fan Case A geometry.')


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
