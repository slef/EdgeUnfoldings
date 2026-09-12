"""Exact applications of the receiver-chain three-petal separation lemmas.

Written universal geometry is separate from these specified coordinate checks.
"""
import json
from n7.bipyramid_morph import ROOT,FACES,I,exact_points,support,develop,cut_at,sub,dot,cross2,check_net
from n7.bipyramid_rule_checks import patch_pattern
from n7.angle_intervals import pi,face_angle,vector_angle

def positive(x,label):
    if x.lo<=0:raise ValueError(label+' is not certified strictly positive')
    return x.export()

def certify(row):
    exact=exact_points(row['points']);support_rows=support(exact)
    p=[[I.bounds(x) for x in v] for v in exact];pattern,_=patch_pattern(p)
    if pattern!='FCCBC':raise ValueError('Expected the normalized opposing-chain pattern')
    fan=row['fan_pole'];source=11-fan;fb=(fan-5)*5;sb=(source-5)*5
    angles={(f,v):face_angle(p,FACES[f],v) for f in range(10) for v in FACES[f]}
    k={v:2*pi()-sum(a for (f,u),a in angles.items() if u==v) for v in range(7)}
    n=develop(p,cut_at(source,0));extensions={}
    for i,symbol in((0,'F'),(3,'B')):
        O=n[fb+i][0];P=sub(n[sb+i][0],O)
        ray=sub(n[fb+i][2] if symbol=='F' else n[fb+i][1],O)
        extensions[i]=vector_angle(ray,P)
    chain=angles[fb+1,fan]+angles[fb+2,fan]-extensions[0]-extensions[3]
    positive(chain,'Chain selection margin')
    long=row['long_patch'];receiver=1 if long==0 else 2
    if long not in(0,3):raise ValueError('This example checker expects one long extension')
    excess=extensions[long]-angles[fb+receiver,fan];positive(excess,'Long extension')
    first=0 if long==0 else 1;middle=first+1;a,b=middle,middle+1
    lam,nu,rho=[angles[sb+i,source] for i in(first,middle,first+2)]
    alpha=angles[sb+middle,a]+k[a];beta=angles[sb+middle,b]+k[b]
    theta=alpha+beta;half=(pi()+theta)/2
    sigma=angles[fb+first,a]+angles[fb+middle,a]
    tau=angles[fb+middle,b]+angles[fb+first+2,b]
    fan_margin=sigma+tau-pi();positive(fan_margin,'Large-fan branch')
    outer_vertex=(first+4)%5;last=(first+3)%5
    A=angles[sb+last,outer_vertex]+angles[sb+outer_vertex,outer_vertex]
    B=angles[fb+last,outer_vertex]+angles[fb+outer_vertex,outer_vertex]
    H=k[source]-k[fan]+B-A
    if (pi()-theta).lo>0:
        A2=n[sb+middle][1];B2=n[sb+middle][2]
        P=n[sb+first][0];Q=n[sb+first+2][0]
        d=sub(P,A2);e=sub(Q,B2);offset=sub(B2,A2);det=cross2(d,e)
        t=cross2(offset,e)/det;u=cross2(offset,d)/det
        positive(t,'Left ray parameter');positive(u,'Right ray parameter')
        choices=[]
        for side,parameter,apex in(('left',t,lam),('right',u,rho)):
            if (parameter-1).lo>0 and (half-apex).lo>0:
                choices.append({'side':side,'short_cut_margin':(parameter-1).export(),
                                'wide_angle_margin':(half-apex).export()})
        if not choices:raise ValueError('No short cut with a sufficient apex-angle bound')
        branch={'name':'Case A','theta_below_pi':(pi()-theta).export(),
                'sufficient_sides':choices,'cap_correction_H':H.export(),
                'cap_correction_gate':H.lo>=0,
                'both_wide_angle_margins':[(half-x).export() for x in(lam,rho)]}
    elif (theta-pi()).lo>0:
        branch={'name':'base cones','theta_above_pi':(theta-pi()).export()}
    else:raise ValueError('This finite checker does not certify a threshold equality')
    auxiliary=None
    if row.get('auxiliary_pole_edge'):
        deleted=(first+4)%5;ends=(first,(first+3)%5)
        faces=tuple(f for f in FACES if deleted not in f)+((5,6,ends[0]),(5,6,ends[1]))
        active=[v for v in range(7) if v!=deleted];sp=support(exact,faces,active)
        auxiliary={'deleted_vertex':deleted,'strict_support_minimum':str(min(x for _,vs in sp for x in vs)),
                   'source_nets':{str(q):check_net(p,[(q,u) for u in active if u!=q],faces) for q in(5,6)}}
    net=check_net(p,cut_at(source,0))
    return {'strict_support_minimum':str(min(x for _,values in support_rows for x in values)),
            'pattern':pattern,'fan_pole':fan,'long_patch':long,
            'auxiliary_pole_edge':auxiliary,'chain_margin':chain.export(),'long_extension_margin':excess.export(),
            'large_fan_margin':fan_margin.export(),'branch':branch,
            'receiver_source_angle_above_pi_over_two':positive(nu-pi()/2,'Obtuse receiver apex'),
            'source_curvature_below_pi':positive(pi()-k[source],'Source curvature below pi'),
            'independent_net_check':{'fan_pairs':len(net['shared_vertex_pairs']),
                                      'strict_separators':net['strict_separators']}}

def replay_saved():
    rows=json.loads((ROOT/'results/bipyramid-receiver-pairs.json').read_text())['examples']
    for row in rows:
        if json.loads(json.dumps(certify(row)))!=row['certificate']:
            raise ValueError('Receiver-pair certificate mismatch: '+row['id'])
    return {'exact_examples':len(rows),'branches':[row['certificate']['branch']['name'] for row in rows],
            'scope':'Specified rational applications and independent complete-net checks; the general separation lemmas are written proofs.'}

if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
