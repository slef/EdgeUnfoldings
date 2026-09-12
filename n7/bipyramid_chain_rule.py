"""Exact examples of the complete FCCBC rule; the universal proof is written separately."""
import json
from n7.bipyramid_morph import ROOT,FACES,I,exact_points,support,develop,cut_at,sub,cross2,check_net
from n7.bipyramid_rule_checks import patch_pattern
from n7.angle_intervals import pi,face_angle,vector_angle
from n7.bipyramid_receiver_pairs import positive

def certify(row):
    exact=exact_points(row['points']);sr=support(exact);p=[[I.bounds(x) for x in v] for v in exact]
    pattern,_=patch_pattern(p)
    if pattern!='FCCBC':raise ValueError('Normalize the pattern to FCCBC before applying this checker')
    ang={(f,v):face_angle(p,FACES[f],v) for f in range(10) for v in FACES[f]}
    k={v:2*pi()-sum(a for (f,u),a in ang.items() if u==v) for v in range(7)}
    nets={fan:develop(p,cut_at(11-fan,0)) for fan in(5,6)};ell={};width={}
    for fan,n in nets.items():
        fb=(fan-5)*5;sb=(6-fan)*5
        for i,symbol in((0,'F'),(3,'B')):
            O=n[fb+i][0];P=sub(n[sb+i][0],O)
            ray=sub(n[fb+i][2] if symbol=='F' else n[fb+i][1],O)
            ell[fan,i]=vector_angle(ray,P)
            width[fan,i]=ang[fb+(1 if i==0 else 2),fan]
    margins={fan:sum(width[fan,i]-ell[fan,i] for i in(0,3)) for fan in(5,6)}
    preferred=row.get('initial_fan',5)
    fan=preferred if margins[preferred].lo>0 else 11-preferred
    positive(margins[fan],'Selected combined-extension margin')
    source=11-fan
    short=lambda f,i:(width[f,i]-ell[f,i]).lo>=0
    long=[i for i in(0,3) if (ell[fan,i]-width[fan,i]).lo>0]
    selected=fan;branch='both short';details={};pockets=[]
    def pocket(f,i):
        q=11-f;a=1 if i==0 else 3;recv=1 if i==0 else 2;fb=(f-5)*5;sb=(q-5)*5
        return {'fan':f,'bad_patch':i,'receiver':recv,
                'long_extension':positive(ell[f,i]-width[f,i],'Long extension'),
                'other_extension_bound':positive(ell[q,i]-(pi()-k[a])/2,'Pocket lower bound'),
                'fan_receiver_acute':positive(pi()/2-ang[fb+recv,f],'Acute fan receiver'),
                'source_receiver_obtuse':positive(ang[sb+recv,q]-pi()/2,'Obtuse source receiver'),
                'bad_apex_bound':positive((pi()+k[a])/2-ang[sb+i,q],'Bad apex bound')}
    if all(short(fan,i) for i in(0,3)):pass
    else:
        if len(long)!=1:raise ValueError('Interval uncertainty at an extension threshold')
        bad=long[0];other=3-bad;pockets.append(pocket(fan,bad))
        if not short(source,bad):raise ValueError('The long patch must become short after switching poles')
        if all(short(source,i) for i in(0,3)):
            selected=source;branch='switch to both short'
        else:
            pockets.append(pocket(source,other));branch='opposing long extensions'
            sb=(source-5)*5;fb=(fan-5)*5;first=0 if bad==0 else 1;middle=first+1;a,b=middle,middle+1
            alpha=ang[sb+middle,a]+k[a];beta=ang[sb+middle,b]+k[b];theta=alpha+beta
            sigma=ang[fb+first,a]+ang[fb+middle,a];tau=ang[fb+middle,b]+ang[fb+first+2,b]
            details['large_fan_margin']=positive(sigma+tau-pi(),'Large fan')
            if (theta-pi()).lo>0:
                details['separator']='base cones';details['theta_above_pi']=positive(theta-pi(),'Large theta')
            elif (pi()-theta).lo>0:
                n=nets[fan];A=n[sb+middle][1];B=n[sb+middle][2];P=n[sb+first][0];R=n[sb+first+2][0]
                d=sub(P,A);e=sub(R,B);offset=sub(B,A);det=cross2(d,e)
                left=cross2(offset,e)/det;right=cross2(offset,d)/det
                half=(pi()+theta)/2
                details.update({'separator':'wider apex','theta_below_pi':positive(pi()-theta,'Small theta'),
                    'both_wide_angle_margins':[positive(half-ang[sb+i,source],'Wide apex') for i in(first,first+2)],
                    'short_cuts':[side for side,t in(('left',left),('right',right)) if (t-1).lo>0]})
                if not details['short_cuts']:raise ValueError('No strictly short copied cut certified')
            else:raise ValueError('This example checker leaves theta equality to the written proof')
    net=check_net(p,cut_at(11-selected,0))
    return {'strict_support_minimum':str(min(x for _,vs in sr for x in vs)),
            'pattern':pattern,'initial_fan':fan,'selected_fan':selected,'slit':0,
            'selection_margin':margins[fan].export(),'branch':branch,'long_receiver_bounds':pockets,
            'pair_separation':details,'independent_net_check':{'shared_vertex_pairs':len(net['shared_vertex_pairs']),
                'strict_separators':net['strict_separators']}}

def replay_saved():
    rows=json.loads((ROOT/'results/bipyramid-chain-rule.json').read_text())['examples']
    for row in rows:
        if json.loads(json.dumps(certify(row)))!=row['certificate']:raise ValueError('Replay mismatch: '+row['id'])
    return {'exact_examples':len(rows),'branches':sorted({r['certificate']['branch'] for r in rows}),
            'scope':'Exact coordinate applications; the whole FCCBC class is covered by a separate written proof.'}
if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
