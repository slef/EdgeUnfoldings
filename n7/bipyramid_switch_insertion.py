"""Exact geometry and unique slit-switch certificate for one insertion.

The universal family and finite-switch theorem is in BIPYRAMID_SWITCH_INSERTION.md.
"""
import json
from fractions import Fraction as F
from n7.bipyramid_morph import ROOT,FACES,I,exact_points,support,sub,dot,cross,cut_at,check_net
from n7.angle_intervals import pi,face_angle
from n7.bipyramid_rule_checks import patch_pattern

def geometry(row):
    ex=exact_points(row['points']);sr=support(ex)
    if any(a[2]!=0 for a in ex[:5]) or not ex[5][2]<0<ex[6][2]:raise ValueError('Use the prescribed planar-ring normalization')
    q=ex[6];p=ex[5];c=[(q[j]*(-p[2])+p[j]*q[2])/(q[2]-p[2]) for j in range(3)];direction=sub(p,c)
    start=[a[:] for a in ex];start[5]=c;values=[];area=[]
    for f,(sgn,_) in zip(FACES,sr):
        a,b,d=[start[v] for v in f];n=cross(sub(b,a),sub(d,a));area.append(dot(n,n));values.extend(sgn*dot(n,sub(start[v],a)) for v in range(7) if v not in f)
    if min(values)<0 or min(area)<=0:raise ValueError('Invalid flat six-vertex start')
    plane=[dot(sub(a,q),sub(p,q)) for a in ex[:5]]
    if min(plane)<0:raise ValueError('Source supporting plane fails')
    return ex,c,direction,{'start_point':list(map(str,c)),'endpoint_support_minimum':str(min(x for _,v in sr for x in v)),
        'start_support_minimum':str(min(values)),'start_area_squared_minimum':str(min(area)),
        'source_plane_margins':list(map(str,plane))}

def certify(row):
    ex,c,direction,out=geometry(row);fixed=[I.bounds(dot(sub(ex[6],a),sub(ex[6],a))).sqrt() for a in ex[:5]]
    def at(t):return [[I.bounds(x) for x in a] for a in ex[:5]]+[[I.bounds(c[j])+t*direction[j] for j in range(3)],[I.bounds(x) for x in ex[6]]]
    def lengths(t):
        v=at(t);rr=[sub(v[5],v[a]) for a in range(5)];lens=[dot(r,r).sqrt() for r in rr]
        return [fixed[a]+lens[a] for a in range(5)],[dot(r,direction)/lens[a] for a,r in enumerate(rr)]
    cells=[];N=row['cell_count']
    for i in range(N):
        lo,hi=F(i,N),F(i+1,N);d,der=lengths(I.bounds(lo,hi));slope=der[0]-der[2]
        if slope.lo<=0:raise ValueError('Switch difference is not certified increasing')
        dominating=[]
        for a in (1,3,4):
            good=next((b for b in (0,2) if(d[b]-d[a]).lo>0),None)
            if good is None:raise ValueError('A third possible maximum remains')
            dominating.append({'vertex':a,'dominated_by':good,'margin':(d[good]-d[a]).export()})
        cells.append({'interval':[str(lo),str(hi)],'difference_derivative':slope.export(),'other_vertices':dominating})
    d0,_=lengths(I.bounds(0));d1,_=lengths(I.bounds(1))
    if(d0[2]-d0[0]).lo<=0 or(d1[0]-d1[2]).lo<=0:raise ValueError('No certified change from slit 2 to slit 0')
    lo,hi=map(F,row['switch_bracket']);dl,_=lengths(I.bounds(lo));dh,_=lengths(I.bounds(hi))
    if not 0<lo<hi<1 or(dl[2]-dl[0]).lo<=0 or(dh[0]-dh[2]).lo<=0:raise ValueError('Switch bracket does not straddle the unique tie')
    target=at(I.bounds(1));curv=[2*pi()-sum(face_angle(target,f,a) for f in FACES if a in f) for a in range(7)]
    comparisons=[curv[a]-curv[5] for a in range(7) if a!=5]
    if any(x.lo<=0 for x in comparisons):raise ValueError('Inserted vertex not uniquely least curved at the endpoint')
    pattern,_=patch_pattern(target);checks=[]
    for t in (lo,hi,F(1)):
        slit=2 if t==lo else 0;n=check_net(at(I.bounds(t)),cut_at(6,slit));checks.append({'t':str(t),'slit':slit,'shared_vertex_pairs':len(n['shared_vertex_pairs']),'strict_separators':n['strict_separators']})
    out.update({'target_pattern':pattern,'slit_order':[2,0],'switch_bracket':[str(lo),str(hi)],
        'bracket_sign_margins':[(dl[2]-dl[0]).export(),(dh[0]-dh[2]).export()],
        'closed_interval_cells':cells,'target_curvatures':[x.export() for x in curv],
        'inserted_minimum_margins':[x.export() for x in comparisons],'independent_net_checks':checks,
        'scope':'Exact geometry, maximum-slit schedule, and specified nets; safety for the whole insertion follows from the written Source Plane and insertion theorems.'})
    return out

def replay_saved():
    row=json.loads((ROOT/'results/bipyramid-switch-insertion.json').read_text())
    if json.loads(json.dumps(certify(row)))!=row['certificate']:raise ValueError('Insertion replay mismatch')
    return {'closed_interval_cells':row['cell_count'],'slit_changes':1,'inserted_vertex_minimum':True,'specified_net_checks':3}
if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
