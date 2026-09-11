"""Exact hypotheses of OCTA_SLIT_THRESHOLD.md; no H/R curvature ranking."""
from n6.certify import require
from n6.curvature import angle_product,conjugate
from n6.regimes import octahedron_frame,curvature_pi,positive_angles_pi


def weighted_slit_pi(c,w):
    """Compare 2*kappa_c+kappa_w with pi, retaining unresolved signs."""
    kc,kw=curvature_pi(c),curvature_pi(w)
    if kc in ('>','=') or kw in ('>','='):return '>'
    if kc==kw=='<':
        return positive_angles_pi([conjugate(c),conjugate(c),conjugate(w)])
    return None


def verify(spec):
    g,v,w,ring,k,_,_=octahedron_frame(spec)
    totals={x:angle_product(g.p,g.faces,g.h,x) for x in range(6)}
    bands={x:curvature_pi(z) for x,z in totals.items()}
    high=bands[v] in ('>','=');low=all(b in ('<','=') for b in bands.values())
    require(high or low,'Neither source curvature condition is certified')
    threshold=weighted_slit_pi(totals[ring[k]],totals[w])
    require(threshold in ('>','='),'Weighted slit threshold is not certified')
    return dict(result='verified_weighted_slit_threshold_hypotheses',
                source=v,fan=w,slit=ring[k],source_curvature_at_least_pi=high,
                all_curvatures_at_most_pi=low,curvature_comparisons_with_pi=bands,
                twice_slit_plus_fan_curvature_compared_with_pi=threshold,
                H_required=False,R_required=False,whole_net_nonoverlapping=True,
                every_slit_lemma_F_proved=False,proof='OCTA_SLIT_THRESHOLD.md',
                scope='This explicit domain passes the source condition and 2*kappa_slit+kappa_fan>=pi. The written geometric theorem supplies the whole net; it is not formally verified here. Failing the sufficient check is not evidence of overlap.')


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('certificate',type=Path)
    args=ap.parse_args();spec=json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits',240))
    print(json.dumps(verify(spec),indent=2))
