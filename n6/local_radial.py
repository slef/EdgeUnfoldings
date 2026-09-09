"""Prove that a local petal ray enters the opposite flank's angular cone.

This rules out separation by any line through w for that pair. It does not
assert overlap: independent all-pairs verification can still prove a simple
net because the triangles occupy different distances along their common rays.
"""
from n6.certify import require
from n6.intervals import sub,det
from n6.bisector import selected_flanks,opposite_flank_development


def interior_petal_point(petal,apex):
    """A fixed point with positive barycentric weights 3/4, 1/8, 1/8."""
    others=[v for v in petal if v!=apex]
    return tuple((6*petal[apex][j]+sum(petal[v][j] for v in others))/8 for j in range(2))


def verify(cert):
    claim=cert['local_radial_failure'];g,v,w,u,ring,ranking=selected_flanks(cert,claim)
    A,B,(a,b)=opposite_flank_development(g,v,w,ring,claim['petal'])
    left,right,ray=sub(A[a],A[w]),sub(A[b],A[w]),sub(B[v],A[w])
    orientation=det(left,right);signs=[det(left,ray),det(ray,right)]
    require(orientation.lo>0,'Opposite fan cone orientation not certified')
    require(all(s.lo>0 for s in signs),'Petal apex ray is not certified strictly inside the opposite fan cone')
    inner=sub(interior_petal_point(B,v),A[w]);inner_signs=[det(left,inner),det(inner,right)]
    require(all(s.lo>0 for s in inner_signs),'Interior petal ray is not certified in the fan cone')
    return dict(result='verified_failure_of_local_radial_separator',apex=v,antipode=w,slit_vertex=u,
                petal=claim['petal'],opposite_fan_vertices=[w,a,b],
                strict_cone_determinants=[s.pair() for s in signs],curvature_order=ranking,
                interior_ray_determinants=[s.pair() for s in inner_signs],
                scope='No line through w separates this petal from the opposite fan triangle. Angular overlap alone does not imply face overlap or a failure of Lemma L.')


def main():
    import argparse,json
    from pathlib import Path
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    ap.add_argument('--bits',type=int,default=80);args=ap.parse_args();set_precision(args.bits)
    cert=json.loads(args.input.read_text())
    result=verify(cert)
    if 'local_radial_clearance' in cert:result['distance_clearance']=verify_clearance(cert)
    print(json.dumps(result,indent=2))





def verify_clearance(cert):
    """Certify distance separation despite angular intrusion, for one sign pattern.

    In fan coordinates x=lambda*a+mu*b, the outer fan edge is lambda+mu=1.
    If all petal vertices have mu>0 and only its apex has lambda>0, clipping
    the petal to the fan's cone gives a triangle. Its vertices are the apex
    and the intersections of the two apex edges with lambda=0. A linear
    function has its minimum at one of these three vertices.
    """
    from fractions import Fraction as F
    claim=cert['local_radial_clearance'];g,v,w,u,ring,ranking=selected_flanks(cert,claim)
    A,B,(a,b)=opposite_flank_development(g,v,w,ring,claim['petal'])
    x,y=sub(A[a],A[w]),sub(A[b],A[w]);D=det(x,y)
    require(D.lo>0,'Fan basis orientation not certified')
    q={k:(det(sub(p,A[w]),y)/D,det(x,sub(p,A[w]))/D) for k,p in B.items()}
    require(all(p[1].lo>0 for p in q.values()),'Petal is not strictly above the second cone boundary')
    apex=q[v];others=[p for k,p in q.items() if k!=v]
    require(apex[0].lo>0 and all(p[0].hi<0 for p in others),'Expected only the apex inside the first cone boundary')
    ratios=[apex[0]+apex[1]]+[(apex[0]*p[1]-p[0]*apex[1])/(apex[0]-p[0]) for p in others]
    lower=F(claim['minimum_distance_ratio'])
    require(lower>1,'Clearance ratio must exceed one')
    require(all(r.lo>=lower for r in ratios),'Requested radial distance clearance not certified')
    return dict(result='verified_local_radial_clearance',apex=v,antipode=w,slit_vertex=u,
                minimum_distance_ratio=str(lower),three_extreme_ratios=[r.pair() for r in ratios],
                scope='On every shared ray, the petal starts at least this factor farther from w than the opposite fan edge. Only the stated point or parameter region is covered.',
                curvature_order=ranking)


if __name__=='__main__':main()
