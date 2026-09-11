"""Exact examples with a source that is not globally sharpest."""
import json
from pathlib import Path
from n6.intervals import set_precision
from n6.point_audit import exact_hull,cuts_for
from n6.polycert import Geometry,point_spec,make_certificate,verify as all_pairs
from n6.curvature import verify_order,angle_product,interval_angle_le
from n6.source_choice import verify


def specification(name):
    if name=='low':
        points=[[0,0,10],[0,0,-11],[10,0,0],[0,10,0],[-10,0,0],[0,-10,0]]
    elif name=='high':
        points=[[0,0,2],[0,0,-3],[1,0,0],[0,1,0],[-1,0,0],[0,-1,0]]
    else:raise ValueError('Unknown source-choice example')
    faces,adj=exact_hull(points);nxt={}
    for f in faces:
        if 1 in f:
            j=f.index(1);nxt[f[(j+1)%3]]=f[(j+2)%3]
    ring=[2]
    while len(ring)<4:ring.append(nxt[ring[-1]])
    return {**point_spec(points,faces,cuts_for(0,2,adj)),
            'selection':dict(apex=0,antipode=1,equator=ring,slit_index=0),
            'suggested_fractional_bits':240}


def main():
    set_precision(240);results=Path(__file__).parent/'results'
    for name in ['low','high']:
        cert=make_certificate(specification(name));g=Geometry(cert)
        report=dict(hypotheses=verify(cert),independent_all_28_pairs=all_pairs(cert),
                    fan_at_least_as_sharp_as_source=verify_order(g,[(1,0)]))
        totals={x:angle_product(g.p,g.faces,g.h,x) for x in (0,1)}
        if interval_angle_le(totals[0],totals[1]) is not False:
            raise ValueError('Strict failure of the reverse ordering must be certified')
        report['fan_strictly_sharper_than_source']=True
        for suffix,data in [('certificate',cert),('verification',report)]:
            (results/f'source-choice-{name}.{suffix}.json').write_text(json.dumps(data,indent=2)+'\n')
        print(name,'verified',flush=True)


if __name__=='__main__':main()
