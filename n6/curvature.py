"""Curvature comparisons without inverse trigonometric functions.

At a strictly convex vertex the sum of incident face angles is in (0,2*pi).
Multiply the positive-scale complex numbers (edge dot product, face area)
for its angles. Half-plane and determinant signs then compare the sums exactly.
Only symbolic predicates import Z3; interval checking uses the standard library.
"""
from n6.intervals import I,sub


def cmul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])


def conjugate(a):return a[0],-a[1]


def cdet(a,b):return a[0]*b[1]-a[1]*b[0]


def face_angle(points,face,height,vertex):
    if len(face)!=3 or vertex not in face:raise ValueError('Expected a triangular face angle')
    a,b=[v for v in face if v!=vertex]
    e,f=sub(points[a],points[vertex]),sub(points[b],points[vertex])
    return sum(x*y for x,y in zip(e,f)),height


def angle_product(points,faces,heights,vertex):
    result=(1,0)
    for i,f in enumerate(faces):
        if vertex in f:result=cmul(result,face_angle(points,f,heights[i],vertex))
    return result


def angle_le(a,b):
    """Symbolic sum-angle comparison, assuming each argument is in (0,2*pi)."""
    import z3
    upper_a=z3.Or(a[1]>0,z3.And(a[1]==0,a[0]<0))
    upper_b=z3.Or(b[1]>0,z3.And(b[1]==0,b[0]<0))
    return z3.Or(z3.And(upper_a,z3.Not(upper_b)),
                 z3.And(upper_a==upper_b,cdet(a,b)>=0))


def sum_angles_lt_pi(angles):
    """Symbolic comparison for a sum of positive angles individually below pi."""
    import z3
    if not angles:raise ValueError('Expected at least one positive angle')
    acc=angles[0];wrapped=z3.BoolVal(False)
    for angle in angles[1:]:
        nxt=cmul(acc,angle)
        # A positive increment below pi crosses 2*pi only from the lower
        # half-plane to the upper half-plane (including the positive real ray).
        wrapped=z3.Or(wrapped,z3.And(acc[1]<0,nxt[1]>=0))
        acc=nxt
    return z3.And(z3.Not(wrapped),acc[1]>0)


def curvature_sum_lt_pi(a,b):
    """a,b represent incident angle sums, so conjugates represent curvatures."""
    import z3
    return z3.And(a[1]<0,b[1]<0,cmul(conjugate(a),conjugate(b))[1]>0)


def curvature_sum_lt_angle(a,b,angle):
    import z3
    total=cmul(conjugate(a),conjugate(b))
    return z3.And(curvature_sum_lt_pi(a,b),cdet(total,angle)>0)


def face_plus_curvature_lt_pi(angle,total):
    import z3
    return z3.And(total[1]<0,cmul(angle,conjugate(total))[1]>0)


def interval_angle_le(a,b):
    """Certify an ordering by signs; inconclusive intervals return None."""
    def half(z):
        if z[1].lo>=0:return 0
        if z[1].hi<0:return 1
        return None
    ha,hb=half(a),half(b)
    if ha is None or hb is None:return None
    if ha!=hb:return ha<hb
    determinant=cdet(a,b)
    if determinant.lo>=0:return True
    if determinant.hi<0:return False
    return None


def verify_order(geometry,comparisons):
    """Each (a,b) asks for kappa_a >= kappa_b over the geometry's full region."""
    from n6.certify import require
    products={v:angle_product(geometry.p,geometry.faces,geometry.h,v) for v in range(6)}
    records=[]
    for a,b in comparisons:
        require(a in products and b in products,'Invalid curvature comparison')
        if a==b:records.append(dict(vertices=[a,b],reason='identical vertex'));continue
        require(interval_angle_le(products[a],products[b]) is True,'Curvature comparison not certified')
        records.append(dict(vertices=[a,b],angle_sum_products=[
            [q.pair() for q in products[a]],[q.pair() for q in products[b]]],
            determinant=cdet(products[a],products[b]).pair()))
    return dict(result='verified_curvature_order',meaning='For each (a,b), kappa_a >= kappa_b',comparisons=records)


def main():
    import argparse,json
    from pathlib import Path
    from n6.certify import Geometry as OctaGeometry
    from n6.polycert import Geometry as PolyGeometry
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input',type=Path);ap.add_argument('--sharpest',type=int)
    ap.add_argument('--compare',type=int,nargs=2,action='append',default=[])
    args=ap.parse_args();spec=json.loads(args.input.read_text())
    comparisons=list(args.compare)
    if args.sharpest is not None:comparisons += [(args.sharpest,v) for v in range(6) if v!=args.sharpest]
    if not comparisons:ap.error('--sharpest or --compare required')
    g=(OctaGeometry if spec.get('schema')=='n6-octahedron-box-v1' else PolyGeometry)(spec)
    print(json.dumps(verify_order(g,comparisons),indent=2))


if __name__=='__main__':main()
