"""Exact applications of the supporting-plane source rule.

The universal implication is a written geometric proof in
BIPYRAMID_SOURCE_PLANE.md. The finite net checks are independent applications.
"""
import json
from n7.bipyramid_morph import ROOT,FACES,I,exact_points,support,cut_at,sub,dot,check_net
from n7.angle_intervals import pi,face_angle
from n7.bipyramid_rule_checks import patch_pattern

def certify(row):
    ex=exact_points(row['points']);sr=support(ex);q=row['source'];p=11-q
    if q not in (5,6):raise ValueError('Source must be a pole')
    axis=sub(ex[p],ex[q]);plane=[dot(sub(a,ex[q]),axis) for a in ex[:5]]
    if min(plane)<0:raise ValueError('Ring projects beyond the source plane')
    v=[[I.bounds(x) for x in a] for a in ex];dist=[];sq=[]
    for a in range(5):
        ab=[dot(sub(ex[s],ex[a]),sub(ex[s],ex[a])) for s in (5,6)];sq.append(sorted(ab))
        dist.append(sum(I.bounds(x).sqrt() for x in ab))
    slit=max(range(5),key=lambda a:dist[a].mid());comparisons=[]
    for a in range(5):
        if a==slit:continue
        if sq[a]==sq[slit]:comparisons.append({'vertex':a,'equal_squared_lengths':list(map(str,sq[a]))})
        elif (dist[slit]-dist[a]).lo>0:comparisons.append({'vertex':a,'positive_margin':(dist[slit]-dist[a]).export()})
        else:raise ValueError('Maximum distance-sum comparison uncertain; equality belongs to the written proof')
    pattern,_=patch_pattern(v);net=check_net(v,cut_at(q,slit));curvature={}
    for s in (5,6):curvature[s]=2*pi()-sum(face_angle(v,FACES[(s-5)*5+i],s) for i in range(5))
    return {'pattern':pattern,'source':q,'fan':p,'slit':slit,'source_plane_margins':list(map(str,plane)),
        'slit_comparisons':comparisons,'strict_support_minimum':str(min(x for _,vs in sr for x in vs)),
        'pole_curvatures':{s:x.export() for s,x in curvature.items()},
        'both_poles_below_pi':all((pi()-x).lo>0 for x in curvature.values()),
        'independent_net_check':{'shared_vertex_pairs':len(net['shared_vertex_pairs']),'strict_separators':net['strict_separators']}}

def replay_saved():
    report=json.loads((ROOT/'results/bipyramid-source-plane.json').read_text())
    for row in report['examples']:
        if json.loads(json.dumps(certify(row)))!=row['certificate']:raise ValueError('Source plane replay mismatch: '+row['id'])
    return {'exact_examples':len(report['examples']),'patterns':[r['certificate']['pattern'] for r in report['examples']],
        'scope':'Exact applications of a sufficient geometric rule, not certification of every bipyramid.'}
if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
