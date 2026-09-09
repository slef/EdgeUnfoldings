"""Exact necessary closure around the line joining octahedral antipodes.

A convex octahedron with the prescribed twelve edge lengths must close four
positive azimuth turns around v--w. An interval certificate can rule out every
possible value of |vw|^2. Failure to find that certificate is inconclusive.
The checker uses only rational arithmetic and outward square-root bounds.
"""
from fractions import Fraction as F
from math import comb,isqrt
from n6.certify import require
from n6.curvature import cmul
from n6.intervals import I
from n6.polynomials import Poly


def expressions(lengths, t):
    """Polynomial expressions, also usable with symbolic real variables.

    s,r,l are squared edge lengths. A_i=4t*rho_i^2, and
    (B_i,sqrt(C_i)) represents the positive azimuth turn to u_{i+1}.
    """
    s,r,l=(lengths[n] for n in ('s','r','l'))
    z=[s[i]-r[i]+t for i in range(4)]
    A=[4*t*s[i]-z[i]*z[i] for i in range(4)]
    B=[2*t*(s[i]+s[(i+1)%4]-l[i])-z[i]*z[(i+1)%4] for i in range(4)]
    C=[A[i]*A[(i+1)%4]-B[i]*B[i] for i in range(4)]
    return A,B,C


def centered_value(poly,lo,hi):
    """Exact Taylor shift followed by interval Horner evaluation."""
    require(poly.n==1,'Expected a univariate polynomial')
    degree=max((e[0] for e in poly.terms),default=0)
    mid=(lo+hi)/2;dx=I(lo-mid,hi-mid)
    shifted=[sum(c*comb(e[0],j)*mid**(e[0]-j)
                 for e,c in poly.terms.items() if e[0]>=j) for j in range(degree+1)]
    out=I(0)
    for c in reversed(shifted):out=out*dx+c
    return out


def metric_data(metric):
    from n6.intrinsic import metric_angles
    lengths=metric['squared_edge_lengths']
    metric_angles(lengths)  # Require eight nondegenerate Euclidean triangles.
    q={n:[F(x) for x in lengths[n]] for n in ('s','r','l')}
    def length_bounds(x):
        a,b=isqrt(x.numerator),isqrt(x.denominator)
        if a*a==x.numerator and b*b==x.denominator:return F(a,b),F(a,b)
        interval=I(x).sqrt();return interval.lo,interval.hi
    s,r=([length_bounds(x) for x in q[n]] for n in ('s','r'))
    lo=max(max(F(0),a[0]-b[1],b[0]-a[1]) for a,b in zip(s,r))**2
    hi=min(a[1]+b[1] for a,b in zip(s,r))**2
    require(lo<hi,'Empty opposite-vertex distance interval')
    return expressions(q,Poly.variable(1,0)),(lo,hi)


def bounds(polynomials,box):
    return [[centered_value(p,*box) for p in row] for row in polynomials]


def closure_imag(B,C):
    # Only actual candidates with C_i>0 matter. Clipping the lower interval
    # bound to zero includes all of them, even if a box also contains C_i<0.
    require(all(c.hi>0 for c in C),'No strictly positive tetrahedron square')
    acc=(I(1),I(0))
    for b,c in zip(B,C):acc=cmul(acc,(b,I(max(F(0),c.lo),c.hi).sqrt()))
    return acc[1]


def propose_leaf(polynomials,box):
    A,B,C=bounds(polynomials,box)
    for name,row in [('radial_square_nonpositive',A),('tetrahedron_square_nonpositive',C)]:
        for i,x in enumerate(row):
            if x.hi<=0:return dict(kind=name,index=i)
    imag=closure_imag(B,C)
    if imag.lo>0:return dict(kind='closure_imag_positive')
    if imag.hi<0:return dict(kind='closure_imag_negative')
    return None


def make_certificate(metric,max_depth=20):
    polynomials,domain=metric_data(metric)
    def build(box,depth):
        leaf=propose_leaf(polynomials,box)
        if leaf:return leaf
        if depth>=max_depth:raise ValueError('Axis closure remains unresolved at depth limit')
        lo,hi=box;mid=(lo+hi)/2
        return dict(split=str(mid),left=build((lo,mid),depth+1),right=build((mid,hi),depth+1))
    return dict(schema='n6-axis-nonclosure-v1',metric=metric,
                axis_squared_domain=list(map(str,domain)),tree=build(domain,0))


def verify(cert):
    require(cert.get('schema')=='n6-axis-nonclosure-v1','Unknown axis-closure schema')
    polynomials,necessary_domain=metric_data(cert['metric'])
    domain=tuple(F(x) for x in cert['axis_squared_domain'])
    require(len(domain)==2 and domain[0]<=necessary_domain[0]<necessary_domain[1]<=domain[1],
            'Root does not cover every possible opposite-vertex distance')
    counts={};records=[]
    def walk(node,box,depth):
        if 'split' in node:
            lo,hi=box;mid=F(node['split'])
            require(lo<mid<hi,'Invalid axis subdivision')
            walk(node['left'],(lo,mid),depth+1);walk(node['right'],(mid,hi),depth+1)
            return
        A,B,C=bounds(polynomials,box);kind=node.get('kind')
        if kind in ('radial_square_nonpositive','tetrahedron_square_nonpositive'):
            i=node['index'];require(type(i) is int and 0<=i<4,'Invalid axis witness index')
            value=(A if kind=='radial_square_nonpositive' else C)[i]
            require(value.hi<=0,'Axis infeasibility not certified')
        elif kind in ('closure_imag_positive','closure_imag_negative'):
            value=closure_imag(B,C)
            require(value.lo>0 if kind=='closure_imag_positive' else value.hi<0,
                    'Nonzero axis closure product not certified')
        else:raise ValueError('Unknown axis witness kind')
        counts[kind]=counts.get(kind,0)+1
        records.append(dict(axis_squared_interval=list(map(str,box)),kind=kind,bound=value.pair(),depth=depth))
    walk(cert['tree'],domain,0)
    return dict(result='verified_no_convex_octahedron_with_prescribed_edges',
                scope='These twelve lengths cannot be the original edges of a strictly convex octahedron. This is not a counterexample to edge unfolding.',
                axis_squared_domain=list(map(str,domain)),closed_intervals=len(records),checks=counts,leaves=records)


def symbolic_conditions(lengths):
    """Necessary global conditions for a convex original-facet realization."""
    import z3
    t=z3.Real('axis_squared');H=[z3.Real(f'axis_turn_area_{i}') for i in range(4)]
    A,B,C=expressions(lengths,t)
    conditions=[t>0]+[a>0 for a in A]+[h>0 for h in H]+[h*h==c for h,c in zip(H,C)]
    first=cmul((B[0],H[0]),(B[1],H[1]))
    last=cmul((B[2],H[2]),(B[3],H[3]))
    # The two arcs to the opposite equator ray have magnitude ratio A1/A3.
    # Cross-multiplying their normalized complex coordinates gives closure
    # with lower-degree expressions than multiplying all four turns.
    conditions += [A[3]*first[0]==A[1]*last[0], A[3]*first[1]==-A[1]*last[1]]
    return conditions


def main():
    import argparse,json
    from pathlib import Path
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action',choices=('generate','verify'));ap.add_argument('input',type=Path)
    ap.add_argument('--output',type=Path);ap.add_argument('--max-depth',type=int,default=20)
    args=ap.parse_args();data=json.loads(args.input.read_text())
    if args.action=='generate':
        if not args.output:ap.error('generate needs --output')
        data=make_certificate(data,args.max_depth)
        report=verify(data)
        args.output.write_text(json.dumps(data,indent=2)+'\n')
    else:report=verify(data)
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
