"""Exact instances of shortest-patch edge replacement; no sample is a proof.

Written universal results and their published dependency are in
BIPYRAMID_STAR_PATCH.md. Strict finite checks deliberately reject ties.
"""
import json
from fractions import Fraction as F
from n7.bipyramid_morph import ROOT,FACES,I,exact_points,support,develop,cut_at,sub,dot,check_net,inside
from n7.bipyramid_rule_checks import patch_pattern,phase
from n7.angle_intervals import pi,vector_angle,face_angle

def positive(x,label):
    if x.lo<=0:raise ValueError(label+' is not strictly certified')
    return x.export()

def patches(p):
    pattern,evidence=patch_pattern(p);out={}
    for i,c in enumerate(pattern):
        if c!='C':continue
        j=(i+1)%5;L2=dot(sub(p[j],p[i]),sub(p[j],p[i]));L=L2.sqrt();points={i:[I.bounds(0),I.bounds(0)],j:[L,I.bounds(0)]}
        for pole,sign in((5,1),(6,-1)):
            r2=dot(sub(p[pole],p[i]),sub(p[pole],p[i]));s2=dot(sub(p[pole],p[j]),sub(p[pole],p[j]));x=(r2-s2+L2)/(2*L)
            points[pole]=[x,sign*(r2-x*x).sqrt()]
        delta=sub(points[5],points[6]);out[i]={'points':points,'D2':dot(delta,delta)}
    return pattern,evidence,out

def shortest(p,k):
    pattern,evidence,options=patches(p)
    if k not in options:raise ValueError('Selected patch must be strictly convex')
    gaps={str(i):positive(r['D2']-options[k]['D2'],'Unique shortest convex diagonal') for i,r in options.items() if i!=k}
    return options[k],{'pattern':pattern,'patch_signs':evidence,'shortest_patch':k,'squared_diagonal_length':options[k]['D2'].export(),'squared_length_gaps':gaps}

def half_data(p,k,fan,slit,patch):
    if slit not in(k,(k+1)%5):raise ValueError('The slit must be at a shortest-patch endpoint')
    source=11-fan;u=patch['points'];a=sub(u[source],u[fan]);b=sub(u[slit],u[fan]);D=patch['D2'].sqrt();r=dot(b,b).sqrt()
    alpha=vector_angle(a,b);beta=vector_angle(sub(u[fan],u[source]),sub(u[slit],u[source]));gamma=pi()-alpha-beta
    kappa=2*pi()-sum(face_angle(p,f,fan) for f in FACES if fan in f)
    z=phase(p,fan);norm=dot(z,z).sqrt();ca=dot(a,b)/(D*r)
    sa=(a[0]*b[1]-a[1]*b[0]);sa=(sa if sa.lo>0 else -sa)/(D*r)
    projection=r*(z[0]*ca-z[1]*sa)/norm
    return {'alpha':alpha,'beta':beta,'gamma':gamma,'kappa':kappa,'D':D,'radius':r,
            'q1_tangent_margin':D-r*ca,'q0_tangent_margin':D-projection}

def certify(row):
    exact=exact_points(row['points']);supports=support(exact);p=[[I.bounds(x) for x in v] for v in exact]
    k,fan,slit=row['patch'],row['fan_pole'],row['slit'];patch,selection=shortest(p,k);h=half_data(p,k,fan,slit,patch)
    gate=row['gate'];premises={}
    if gate=='large pole':premises['curvature_above_pi']=positive(h['kappa']-pi(),'Large-pole gate')
    elif gate=='obtuse ring corner':premises['corner_above_pi_over_two']=positive(h['gamma']-pi()/2,'Obtuse-corner gate')
    elif gate=='twice half angle':premises['gap_above_twice_half_angle']=positive(h['kappa']-2*h['alpha'],'Twice-half-angle gate')
    elif gate!='empty region':raise ValueError('Unknown replacement gate')
    if gate!='obtuse ring corner':
        premises['source_half_below_pi_over_two']=positive(pi()/2-h['beta'],'Acute source half')
        premises['gap_above_half_angle']=positive(h['kappa']-h['alpha'],'Triangle entirely in curvature gap')
        for key in('q0_tangent_margin','q1_tangent_margin'):premises[key]=positive(h[key],'Empty-region tangent bound')
    if row.get('require_acute_ring_corners'):
        premises['both_ring_corners_acute']=[positive(pi()/2-half_data(p,k,fan,u,patch)['gamma'],'Acute ring corner') for u in(k,(k+1)%5)]
    net=check_net(p,cut_at(11-fan,slit))
    return {'strict_support_minimum':str(min(x for _,vals in supports for x in vals)),**selection,
            'gate':gate,'fan_pole':fan,'slit':slit,'premises':premises,
            'angles':{key:h[key].export() for key in('alpha','beta','gamma','kappa')},
            'independent_net_check':net}

def certify_failure(row):
    exact=exact_points(row['points']);supports=support(exact);p=[[I.bounds(x) for x in v] for v in exact]
    _,selection=shortest(p,row['patch']);seen=set();failures=[]
    for choice in row['choices']:
        fan,slit=choice['fan_pole'],choice['slit'];seen.add((fan,slit));n=develop(p,cut_at(11-fan,slit))
        point=list(map(F,choice['witness']));pair=choice['faces']
        failures.append({'fan_pole':fan,'slit':slit,'faces':pair,'strict_inside_checks':[inside(n[i],point) for i in pair]})
    if seen!={(fan,slit) for fan in(5,6) for slit in(row['patch'],(row['patch']+1)%5)}:raise ValueError('All four endpoint trees are required')
    return {'strict_support_minimum':str(min(x for _,vals in supports for x in vals)),**selection,'four_overlaps':failures}

def replay_saved():
    data=json.loads((ROOT/'results/bipyramid-star-patch.json').read_text())
    for row in data['examples']:
        if json.loads(json.dumps(certify(row)))!=row['certificate']:raise ValueError('Replacement certificate mismatch: '+row['id'])
    for row in data['counterexamples']:
        if json.loads(json.dumps(certify_failure(row)))!=row['certificate']:raise ValueError('Four-tree failure certificate mismatch')
    return {'exact_successes':len(data['examples']),'four_tree_counterexamples':len(data['counterexamples']),
            'scope':'Specified rational instances and counterexamples; universal results have written proofs.'}
if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
