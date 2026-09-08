"""Exact follow-up of numerical octahedron candidates, including thin ones.

Decimal coordinates are interpreted as exact rationals and scaled together to
integers. This avoids losing small geometric quantities to the fixed absolute
interval grid. Hull facets and the curvature selection are recomputed exactly.
"""
from fractions import Fraction as F
from itertools import combinations
import math
from n6.intervals import sub,cross
from n6.polycert import point_spec,Geometry,make_certificate,verify,make_overlap,verify_overlap
from n6.curvature import angle_product,interval_angle_le,verify_order
from n6.certify import edge


def integer_points(points):
    rational=[[F(str(x)) for x in p] for p in points]
    scale=math.lcm(*(x.denominator for p in rational for x in p))
    return [[int(x*scale) for x in p] for p in rational],scale


def exact_hull(points):
    faces=[]
    for a,b,c in combinations(range(6),3):
        N=cross(sub(points[b],points[a]),sub(points[c],points[a]))
        signs=[sum(x*y for x,y in zip(N,sub(points[v],points[a]))) for v in range(6) if v not in (a,b,c)]
        if all(x<0 for x in signs):faces.append((a,b,c))
        elif all(x>0 for x in signs):faces.append((a,c,b))
    if len(faces)!=8:raise ValueError('Rational candidate is not a strictly simplicial eight-facet hull')
    adj={v:set() for v in range(6)}
    for f in faces:
        for a,b in combinations(f,2):adj[a].add(b);adj[b].add(a)
    if any(len(vs)!=4 for vs in adj.values()):raise ValueError('Rational candidate is not an octahedron')
    return faces,adj


def cuts_for(apex,slit,adj):
    antipode=next(v for v in adj if v!=apex and v not in adj[apex])
    if slit not in adj[antipode]:raise ValueError('Invalid slit vertex')
    return [edge(apex,v) for v in sorted(adj[apex])]+[edge(antipode,slit)]


def exact_selection(g,adj):
    products={v:angle_product(g.p,g.faces,g.h,v) for v in range(6)}
    def maximum(vertices):
        for v in vertices:
            if all(v==w or interval_angle_le(products[v],products[w]) is True for w in vertices):return v
        raise ValueError('Curvature ranking remains unresolved at this precision')
    apex=maximum(list(range(6)));antipode=next(v for v in adj if v!=apex and v not in adj[apex])
    slit=maximum(sorted(adj[antipode]))
    return apex,antipode,slit


def audit(candidate):
    p,scale=integer_points(candidate['points']);faces,adj=exact_hull(p)
    v=candidate['apex'];slit=candidate.get('slit_vertex')
    if slit is None:slit=candidate['equator'][candidate.get('slit_index',candidate.get('k'))]
    initial=point_spec(p,faces,cuts_for(v,slit,adj));g=Geometry(initial)
    exact_v,w,exact_u=exact_selection(g,adj)
    report=dict(scope='Exact audit of the decimal-rational candidate, not a universal unfolding theorem',integer_scale=str(scale),
                original_selection=dict(apex=v,slit=slit),exact_selection=dict(apex=exact_v,antipode=w,slit=exact_u),
                curvature_order=verify_order(g,[(exact_v,x) for x in range(6) if x!=exact_v]+[(exact_u,x) for x in adj[w] if x!=exact_u]))
    certificates={};same_selection=(v,slit)==(exact_v,exact_u)
    for name,a,u in [('original',v,slit),('exact',exact_v,exact_u)]:
        if name=='exact' and same_selection:
            report['exact_net']=report['original_net']
            if 'original' in certificates:certificates['selected']=certificates.pop('original')
            continue
        spec=point_spec(p,faces,cuts_for(a,u,adj))
        try:
            cert=make_certificate(spec);report[name+'_net']=verify(cert);certificates[name]=cert
        except ValueError as error:
            report[name+'_net']=dict(result='unresolved',reason=str(error))
            for f,h in combinations(range(8),2):
                try:cert=make_overlap(spec,f,h)
                except ValueError:continue
                report[name+'_net']=verify_overlap(cert);certificates[name]=cert;break
    return report,certificates


def main():
    import argparse,json
    from pathlib import Path
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--bits',type=int,default=320)
    args=ap.parse_args();source=json.loads(args.input.read_text(),parse_float=str)
    from n6.intervals import set_precision
    set_precision(args.bits)
    report,certificates=audit(source.get('best',source))
    report['fractional_bits']=args.bits
    args.output.with_suffix('.verification.json').write_text(json.dumps(report,indent=2)+'\n')
    for name,cert in certificates.items():
        cert['suggested_fractional_bits']=args.bits
        args.output.with_suffix('.'+name+'.certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='curvature_order'},indent=2))


if __name__=='__main__':main()
