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
    print(json.dumps(verify(json.loads(args.input.read_text())),indent=2))


if __name__=='__main__':main()
