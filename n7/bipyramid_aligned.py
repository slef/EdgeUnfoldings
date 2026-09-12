"""Exact finite checks for the written aligned-pole family theorem.

The all-height argument is in BIPYRAMID_ALIGNED.md. These certificates
check selected rational shapes, the convex completion, and all face pairs.
"""
import json
from n7.bipyramid_morph import ROOT,FACES,I,exact_points,support,develop,cut_at,sub,dot,cross2,check_net
from n7.bipyramid_rule_checks import patch_pattern
from n7.angle_intervals import pi,face_angle

def positive(x,label):
    if x.lo<=0:raise ValueError(label+' is not strictly certified')
    return x.export()

def certify(row):
    e=exact_points(row['points']);fan=row['fan_pole'];source=11-fan;k=row['slit']
    if any(e[i][2]!=0 for i in range(5)):raise ValueError('This finite checker uses an equator in z=0')
    if e[fan][:2]!=e[source][:2] or e[fan][2]*e[source][2]>=0:raise ValueError('Poles must align on opposite sides of the equator')
    h,H=abs(e[fan][2]),abs(e[source][2])
    if not 0<h<=H:raise ValueError('Use the lower-height pole as fan')
    C=H*H-h*h;center=e[fan][:2]
    orient=[cross2(sub(e[(i+1)%5][:2],e[i][:2]),sub(center,e[i][:2])) for i in range(5)]
    if not(min(orient)>0 or max(orient)<0):raise ValueError('Common projection must lie strictly inside the convex base')
    sp=support(e);r2=[dot(sub(v,e[fan]),sub(v,e[fan])) for v in e[:5]]
    gaps=[r2[k]-v for v in r2]
    if min(gaps)<0:raise ValueError('Selected slit is not farthest from the fan pole')
    distance_differences=[dot(sub(e[source],e[i]),sub(e[source],e[i]))-r2[i] for i in range(5)]
    if any(x!=C for x in distance_differences):raise ValueError('Constant squared-distance identity failed')
    p=[[I.bounds(x) for x in v] for v in e];fb=(fan-5)*5
    a={(i,v):face_angle(p,FACES[fb+i],v) for i in range(5) for v in FACES[fb+i]}
    gamma=sum(a[i,fan] for i in range(5));curvature=2*pi()-gamma
    ring_margins=[positive(pi()-a[(i-1)%5,i]-a[i,i],'Convex fan-chain corner') for i in range(5)]
    acute=[positive(pi()/2-a[(k-1)%5,k],'First slit corner is acute'),positive(pi()/2-a[k,k],'Second slit corner is acute')]
    n=develop(p,cut_at(source,k));O=n[fb+k][0]
    boundary=[n[fb+(k+i)%5][1] for i in range(5)]+[n[fb+(k+4)%5][2]]
    if (gamma-pi()).lo>0:
        branch='complete the missing gap';B=boundary
    elif (pi()-gamma).lo>0:
        branch='fan already convex';B=[O]+boundary
    else:raise ValueError('Threshold equality is included in the written proof, not this strict finite checker')
    turns=[cross2(sub(B[(i+1)%len(B)],B[i]),sub(B[(i+2)%len(B)],B[(i+1)%len(B)])) for i in range(len(B))]
    sign=1 if turns[0].lo>0 else -1
    convex=[positive(sign*x,'Convex completed polygon turn') for x in turns]
    interior=[]
    if branch=='complete the missing gap':
        interior=[positive(sign*cross2(sub(B[(i+1)%len(B)],B[i]),sub(O,B[i])),'Fan center inside completion') for i in range(len(B))]
    net=check_net(p,cut_at(source,k));pattern,pattern_evidence=patch_pattern(p)
    return {'strict_support_minimum':str(min(x for _,v in sp for x in v)),
            'fan_pole':fan,'source_pole':source,'slit':k,'heights':[str(h),str(H)],
            'squared_auxiliary_height':str(C),'squared_slit_distance_gaps':[str(x) for x in gaps],
            'squared_pole_distance_differences':[str(x) for x in distance_differences],
            'base_projection_margins':[str(abs(x)) for x in orient],
            'fan_curvature':curvature.export(),'pattern':pattern,'patch_signs':pattern_evidence,
            'convex_chain_margins':ring_margins,'acute_slit_margins':acute,
            'completion_branch':branch,'convex_completion_turns':convex,'center_interior_margins':interior,
            'independent_net_check':net}

def replay_saved():
    d=json.loads((ROOT/'results/bipyramid-aligned.json').read_text())
    for row in d['examples']:
        if json.loads(json.dumps(certify(row)))!=row['certificate']:raise ValueError('Aligned certificate mismatch: '+row['id'])
    return {'exact_examples':len(d['examples']),'completion_branches':sorted(set(r['certificate']['completion_branch'] for r in d['examples'])),
            'scope':'Specified rational instances of the written all-height geometric family theorem.'}
if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
