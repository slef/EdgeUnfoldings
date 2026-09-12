"""Exact applications of the two radial long-receiver lemmas.

The general lemmas and complete pattern proofs are in BIPYRAMID_RADIAL.md.
"""
import json
from n7.bipyramid_morph import ROOT,FACES,I,exact_points,support,develop,cut_at,sub,dot,cross2,check_net
from n7.angle_intervals import pi,face_angle,vector_angle
from n7.bipyramid_rule_checks import patch_pattern
from n7.bipyramid_receiver_pairs import positive

def length(v):return dot(v,v).sqrt()
def certify_local(row):
    ex=exact_points(row['points']);sr=support(ex);p=[[I.bounds(x) for x in v] for v in ex]
    pattern,_=patch_pattern(p);fan=row['fan_pole'];q=11-fan;i=row['long_patch'];symbol=pattern[i]
    if symbol not in 'BF':raise ValueError('Expected an inward patch')
    a=i if symbol=='B' else(i+1)%5;j=(i+(-1 if symbol=='B' else 1))%5
    b=(i-1)%5 if symbol=='B' else(i+2)%5
    if pattern[j]!='C':raise ValueError('Expected a convex receiver')
    slit=next(k for k in range(5) if k!=a);n=develop(p,cut_at(q,slit));fb=(fan-5)*5;sb=(q-5)*5
    O=n[fb+i][0];A=n[fb+i][1 if symbol=='B' else 2];P=n[sb+i][0];M=n[sb+j][0]
    ext=vector_angle(sub(A,O),sub(P,O));omega=face_angle(p,FACES[fb+j],fan)
    positive(ext-omega,'Long receiver')
    e=sub(P,A);v=sub(O,A);dotve=dot(v,e);t=dotve/dot(e,e)
    if t.hi<0:delta2=dot(v,v);projection='first endpoint'
    elif(t-1).lo>0:delta2=dot(sub(O,P),sub(O,P));projection='second endpoint'
    elif t.lo>0 and(t-1).hi<0:delta2=dot(v,v)-dotve*dotve/dot(e,e);projection='interior'
    else:raise ValueError('This finite example checker does not decide a projection threshold')
    delta=delta2.sqrt();db=length(sub(p[fan],p[b]))+length(sub(p[q],p[b]))
    first=positive(delta-db,'Far vertex strictly inside shielding circle')
    other=develop(p,cut_at(fan,slit));O2=other[sb+i][0];X=other[fb+i][0];Z=other[fb+j][0];A2=other[sb+i][1 if symbol=='B' else 2]
    direction=sub(X,O2);edge=sub(Z,A2);off=sub(A2,O2);det=cross2(direction,edge)
    ray=cross2(off,edge)/det;edge_t=cross2(off,direction)/det
    positive(ray,'Forward cone ray');positive(edge_t,'Receiver edge parameter');positive(1-edge_t,'Receiver edge parameter below one')
    Y=[x+ray*d for x,d in zip(O2,direction)]
    radial=positive(dot(sub(Z,O2),sub(Z,O2))-dot(sub(Y,O2),sub(Y,O2)),'Clipping point within source-radius disk')
    return {'pattern':pattern,'fan':fan,'bad_patch':i,'receiver':j,'far_vertex':b,
        'strict_support_minimum':str(min(x for _,vs in sr for x in vs)),
        'long_extension_margin':(ext-omega).export(),
        'shield_projection':projection,'far_vertex_shield_margin':first,
        'other_fan_clipping_ray_parameter':ray.export(),'other_fan_clipping_edge_parameter':edge_t.export(),
        'other_fan_radial_square_margin':radial}

def replay_saved():
    rows=json.loads((ROOT/'results/bipyramid-radial.json').read_text())['local_examples']
    for row in rows:
        if json.loads(json.dumps(certify_local(row)))!=row['certificate']:raise ValueError('Radial replay mismatch: '+row['id'])
    rules=json.loads((ROOT/'results/bipyramid-radial.json').read_text())['rule_examples']
    for row in rules:
        if json.loads(json.dumps(certify_rule(row)))!=row['certificate']:raise ValueError('Radial rule replay mismatch: '+row['id'])
    return {'exact_rule_examples':len(rules),'exact_local_examples':len(rows),'projection_regimes':sorted({r['certificate']['shield_projection'] for r in rows}),
            'scope':'Exact applications of two written universal local lemmas; no search is a universal proof.'}

def certify_rule(row):
    ex=exact_points(row['points']);sr=support(ex);p=[[I.bounds(x) for x in v] for v in ex]
    pattern,_=patch_pattern(p)
    if pattern not in('FCCBC','FCFCC','FCCCB'):raise ValueError('Normalize to one of the three distinct-receiver patterns')
    angles={(f,v):face_angle(p,FACES[f],v) for f in range(10) for v in FACES[f]}
    k={s:2*pi()-sum(a for(f,v),a in angles.items() if v==s) for s in(5,6)}
    for s in(5,6):positive(pi()-k[s],'Both poles below pi')
    bad=[i for i,c in enumerate(pattern) if c!='C'];other_bad=bad[1];ell={};short={};span={}
    for fan in(5,6):
        fb=(fan-5)*5;sb=(6-fan)*5;n=develop(p,cut_at(11-fan,0));span[fan]=[]
        for i in range(5):
            w=angles[fb+i,fan];e=I.bounds(0)
            if i in bad:
                O=n[fb+i][0];A=n[fb+i][1 if pattern[i]=='B' else 2];P=n[sb+i][0]
                e=vector_angle(sub(A,O),sub(P,O));receiver=(i+(-1 if pattern[i]=='B' else 1))%5
                ell[fan,i]=e;short[fan,i]=angles[fb+receiver,fan]-e
            span[fan].append(positive((2*pi()-k[fan])/2-w-e,'Half-fan patch span'))
    choices=[s for s in(5,6) if all(short[s,i].lo>=0 for i in bad)]
    branch='both short';local=[];distance_order=[]
    if choices:fan=choices[0]
    else:
        fan=next((s for s in(5,6) if short[s,0].hi<0),None)
        if fan is None:raise ValueError('Interval uncertainty at a long threshold')
        q=11-fan
        if short[q,other_bad].hi>=0:raise ValueError('Opposing long preferences not certified')
        d=[sum(length(sub(p[s],p[i])) for s in(5,6)) for i in range(5)]
        if pattern=='FCCCB' and(d[3]-d[2]).lo>0:fan=q
        elif pattern=='FCCCB' and(d[2]-d[3]).lo<=0:raise ValueError('This finite checker leaves equal radii to the written proof')
        branch='radial separation with opposing preferences'
        for i in bad:
            # Use the actual long pole of each patch, independent of the selected fan.
            f=next(s for s in(5,6) if short[s,i].hi<0)
            local.append(certify_local({'points':row['points'],'fan_pole':f,'long_patch':i}))
        pairs=[(i,i+1) for i in range(4)] if pattern=='FCFCC' else [(0,1),(1,2),(0,4),(4,3)] if pattern=='FCCCB' else [(0,1),(1,2),(4,3),(3,2)]
        distance_order=[{'larger':a,'smaller':b,'margin':positive(d[a]-d[b],'Distance descent')} for a,b in pairs]
    n=check_net(p,cut_at(11-fan,0))
    return {'pattern':pattern,'fan':fan,'slit':0,'branch':branch,'half_fan_span_margins':span,
        'radial_lemmas':local,'distance_order':distance_order,
        'independent_net_check':{'shared_vertex_pairs':len(n['shared_vertex_pairs']),'strict_separators':n['strict_separators']}}

if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
