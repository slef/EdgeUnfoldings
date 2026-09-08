"""Exact interval witnesses for the angular cases in the octahedron argument.

These checks classify an explicit point or parameter region. They do not assert
that a case is impossible merely because no example has been found.
"""
from n6.certify import require,edge
from n6.curvature import angle_product,face_angle,cmul,conjugate,cdet,verify_order
from n6.polycert import Geometry


def phase_pi(z):
    """Compare an angle known to lie in (0,2*pi) with pi."""
    if z[1].lo>0:return '<'
    if z[1].hi<0:return '>'
    if z[1].lo==z[1].hi==0 and z[0].hi<0:return '='
    return None


def curvature_pi(total):
    result=phase_pi(total)
    return {'<':'>','>':'<','=':'=',None:None}[result]


def face_plus_curvature_pi(angle,total):
    k=curvature_pi(total)
    if k in ('>','='):return '>'
    if k=='<':return phase_pi(cmul(angle,conjugate(total)))
    return None


def two_curvatures_pi(a,b):
    ka,kb=curvature_pi(a),curvature_pi(b)
    if ka in ('>','=') or kb in ('>','='):return '>'
    if ka==kb=='<':return phase_pi(cmul(conjugate(a),conjugate(b)))
    return None


def two_curvatures_angle(a,b,angle):
    k=two_curvatures_pi(a,b)
    if k in ('>','='):return '>'
    if k=='<':
        d=cdet(cmul(conjugate(a),conjugate(b)),angle)
        if d.lo>0:return '<'
        if d.hi<0:return '>'
        if d.lo==d.hi==0:return '='
    return None


def positive_angles_pi(angles):
    """Compare a sum of positive angles below pi with pi, without wrapping."""
    require(bool(angles),'Empty angle list')
    acc=angles[0]
    for i,angle in enumerate(angles[1:],start=1):
        # The previous partial sum is known to be below pi. Thus this new
        # partial sum is below 2*pi, where the phase test is unambiguous.
        acc=cmul(acc,angle);result=phase_pi(acc)
        if result=='>':return '>'
        if result=='=':return '=' if i==len(angles)-1 else '>'
        if result is None:return None
    return '<'


def curvature_sum_band(a,b):
    """Five-way partition of K: below/equal pi, between, equal/above 2*pi."""
    ka,kb=curvature_pi(a),curvature_pi(b)
    if None in (ka,kb):return None
    if ka==kb=='<':
        return {'<':'K<pi','=':'K=pi','>':'pi<K<2pi',None:None}[two_curvatures_pi(a,b)]
    if ka==kb=='>':return 'K>2pi'
    if ka==kb=='=':return 'K=2pi'
    if '=' in (ka,kb):return 'K>2pi' if '>' in (ka,kb) else 'pi<K<2pi'
    # One summand is below pi and the other is above pi; pi<K<3*pi.
    z=cmul(conjugate(a),conjugate(b))
    if z[1].lo>0:return 'K>2pi'
    if z[1].hi<0:return 'pi<K<2pi'
    if z[1].lo==z[1].hi==0 and z[0].lo>0:return 'K=2pi'
    return None


def classify(spec):
    g=Geometry(spec);selection=spec['selection'];v,w=selection['apex'],selection['antipode']
    ring=selection['equator'];k=selection['slit_index']
    require(isinstance(k,int) and 0<=k<4,'Invalid slit index')
    require(len(ring)==len(set(ring))==4 and set(ring)|{v,w}==set(range(6)) and v!=w,'Invalid bipyramid labels')
    lookup={frozenset(f):i for i,f in enumerate(g.faces)}
    require(len(g.faces)==8 and all(len(f)==3 for f in g.faces),'Expected triangular octahedron')
    V=[lookup[frozenset((v,ring[i],ring[(i+1)%4]))] for i in range(4)]
    W=[lookup[frozenset((w,ring[i],ring[(i+1)%4]))] for i in range(4)]
    for i,findex in enumerate(W):
        f=g.faces[findex];j=f.index(w)
        require(f[(j+1)%3]==ring[i] and f[(j+2)%3]==ring[(i+1)%4],'Equator orientation disagrees with facets')
    require({edge(*e) for e in spec['cut_edges']}=={edge(v,u) for u in ring}|{edge(w,ring[k])},'Cuts disagree with selected near-star tree')
    products={x:angle_product(g.p,g.faces,g.h,x) for x in range(6)}
    order=verify_order(g,[(v,x) for x in range(6) if x!=v]+[(ring[k],x) for x in ring if x!=ring[k]])
    def angle(f,x):return face_angle(g.p,g.faces[f],g.h[f],x)
    triples=[]
    for i in (k,(k+1)%4):
        j,jj=(i+1)%4,(i+2)%4
        triples.append(dict(i=i,case_A_comparison=two_curvatures_angle(products[ring[j]],products[ring[jj]],angle(V[j],v)),
                            left_D_comparison=face_plus_curvature_pi(angle(V[j],ring[j]),products[ring[j]]),
                            right_D_comparison=face_plus_curvature_pi(angle(V[j],ring[jj]),products[ring[jj]]),
                            sum_W_comparison=positive_angles_pi([angle(W[i],ring[j]),angle(W[j],ring[j]),angle(W[j],ring[jj]),angle(W[jj],ring[jj])]),
                            opposite_faces=[V[i],V[jj]]))
    return dict(result='verified_angular_classification',scope='Only the specified point or parameter region; no universal exclusion',
                curvature_order=order,slit_curvature_band=curvature_sum_band(products[ring[k]],products[w]),triples=triples)


def verify(spec):
    actual=classify(spec);expected=spec['angular_claims']
    require(actual['slit_curvature_band'] is not None and actual['slit_curvature_band']==expected['slit_curvature_band'],'Unverified slit-curvature band')
    for a,e in zip(actual['triples'],expected['triples']):
        require(set(e)==set(a),'Incomplete angular claims')
        require(all(a.get(key)==value and value is not None for key,value in e.items()),'Angular claim not certified')
    require(len(expected['triples'])==len(actual['triples']),'Missing triple claims')
    return actual


def main():
    import argparse,json
    from pathlib import Path
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    args=ap.parse_args();print(json.dumps(verify(json.loads(args.input.read_text())),indent=2))


if __name__=='__main__':main()
