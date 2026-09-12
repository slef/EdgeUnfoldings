"""Exact applications of the conditional Ordered Run theorem.

The universal implication and equality cases are proved in BIPYRAMID_RUNS.md.
This module does not assert that one of the two poles always passes.
"""
import json
from n7.bipyramid_morph import ROOT,FACES,I,exact_points,support,develop,cut_at,sub,check_net
from n7.angle_intervals import pi,face_angle,vector_angle
from n7.bipyramid_rule_checks import patch_pattern

def certify(row):
    ex=exact_points(row['points']);sr=support(ex);p=[[I.bounds(x) for x in v] for v in ex]
    pattern,_=patch_pattern(p);k=pattern.count('F')
    if k not in (3,4) or pattern!='F'*k+'C'*(5-k):raise ValueError('Normalize to FFFCC or FFFFC')
    ang={(f,v):face_angle(p,FACES[f],v) for f in range(10) for v in FACES[f]};gates={};curvature={}
    for fan in (5,6):
        fb=(fan-5)*5;sb=(6-fan)*5;n=develop(p,cut_at(11-fan,0));ell=[]
        for i in range(k):ell.append(vector_angle(sub(n[fb+i][2],n[fb+i][0]),sub(n[sb+i][0],n[fb+i][0])))
        gates[fan]=[ang[fb+i+1,fan]+ell[i+1]-ell[i] for i in range(k-1)]+[ang[fb+k,fan]-ell[-1]]
        curvature[fan]=2*pi()-sum(ang[fb+i,fan] for i in range(5))
    good=[s for s in (5,6) if all(x.lo>=0 for x in gates[s])]
    if not good:raise ValueError('Neither pole is certified by the sufficient ordering test')
    fan=good[0];net=check_net(p,cut_at(11-fan,0))
    return {'pattern':pattern,'run_length':k,'good_fans':good,'selected_fan':fan,'slit':0,
        'strict_support_minimum':str(min(x for _,vs in sr for x in vs)),
        'gates':{s:[x.export() for x in a] for s,a in gates.items()},
        'pole_curvatures':{s:x.export() for s,x in curvature.items()},
        'both_poles_below_pi':all((pi()-x).lo>0 for x in curvature.values()),
        'independent_net_check':{'shared_vertex_pairs':len(net['shared_vertex_pairs']),'strict_separators':net['strict_separators']}}

def replay_saved():
    report=json.loads((ROOT/'results/bipyramid-runs.json').read_text())
    for row in report['examples']:
        if json.loads(json.dumps(certify(row)))!=row['certificate']:raise ValueError('Ordered run replay mismatch: '+row['id'])
    return {'exact_examples':len(report['examples']),'run_lengths':[r['certificate']['run_length'] for r in report['examples']],
        'scope':'Specified rational applications of a proved sufficient rule; common-pole existence is not asserted.'}
if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
