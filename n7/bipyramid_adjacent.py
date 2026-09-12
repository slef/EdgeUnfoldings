"""Exact applications of the adjacent-two-bad unfolding rule.

Universal geometry and equality cases are proved in BIPYRAMID_ADJACENT.md.
"""
import json
from collections import Counter
from n7.bipyramid_morph import ROOT,FACES,I,exact_points,support,develop,cut_at,sub,dot,check_net
from n7.angle_intervals import pi,face_angle,vector_angle
from n7.bipyramid_receiver_pairs import positive
from n7.bipyramid_rule_checks import patch_pattern
from n7.bipyramid_radial import certify_local,length

def verify_identity():
    checked=[]
    for m in range(3,9):
        for i in range(m):
            j=(i+1)%m;a=j;v=(j+1)%m;z=Counter()
            def term(key,n):z[key]+=n
            # rho_i-rho_j-(two pole angles of patch j)+kappa_a
            for s in(0,1):
                term((s,i,a),1);term((s,j,v),-1);term((s,j,'pole'),-1)
                term((s,i,a),-1);term((s,j,a),-1)
            term('pi',2)
            # Add the two triangle sums of patch j, minus 2*pi.
            for s in(0,1):
                for u in('pole',j,v):term((s,j,u),1)
            term('pi',-2)
            if any(z.values()):raise ValueError('Nonzero coefficient in adjacent identity')
            checked.append([m,i])
    return {'exact_integer_coefficient_identities':len(checked),'rings_and_start_indices':checked}

def certify(row):
    ex=exact_points(row['points']);sr=support(ex);p=[[I.bounds(x) for x in v] for v in ex];pattern,_=patch_pattern(p)
    if pattern!='FFCCC':raise ValueError('Normalize to FFCCC')
    ang={(f,v):face_angle(p,FACES[f],v) for f in range(10) for v in FACES[f]};ell={};A={};B={};nets={}
    for fan in(5,6):
        fb=(fan-5)*5;sb=(6-fan)*5;n=develop(p,cut_at(11-fan,0));nets[fan]=n
        for i in(0,1):ell[fan,i]=vector_angle(sub(n[fb+i][2],n[fb+i][0]),sub(n[sb+i][0],n[fb+i][0]))
        A[fan]=ell[fan,0]-ang[fb+1,fan]-ell[fan,1];B[fan]=ell[fan,1]-ang[fb+2,fan]
    fan=next((s for s in(5,6) if B[s].hi<=0),None)
    if fan is None:raise ValueError('Interval uncertainty at the short threshold')
    initial=fan;other=11-fan;branch='ordered and short';details={}
    if A[fan].hi<=0:pass
    elif A[fan].lo>0:
        if B[other].hi<=0:fan=other;branch='switch to ordered and short';positive(-A[fan],'Other pole ordering')
        elif B[other].lo>0:
            branch='outer pocket and radial cover';fb=(fan-5)*5;sb=(other-5)*5;n=nets[fan]
            O=n[fb][0];a=n[fb][2];P=n[sb][0];M=n[sb+1][0];e=sub(P,a);v=sub(O,a);ve=dot(v,e);t=ve/dot(e,e)
            if t.hi<0:d2=dot(v,v)
            elif(t-1).lo>0:d2=dot(sub(O,P),sub(O,P))
            elif t.lo>0 and(t-1).hi<0:d2=dot(v,v)-ve*ve/dot(e,e)
            else:raise ValueError('Projection equality left to written proof')
            delta=d2.sqrt();D=length(sub(O,M));far=sum(length(sub(p[s],p[3])) for s in(5,6))
            details={'source_inside_shield':positive(delta-D,'Pocket source bound'),
                'first_extension_acute':positive(pi()/2-ell[fan,0],'First extension below pi/2'),
                'last_receiver_fan_obtuse':positive(ang[fb+2,fan]-pi()/2,'Last receiver above pi/2'),
                'far_vertex_inside_source_radius':positive(D-far,'Far radius below middle diagonal'),
                'other_pole_radial_lemmas':certify_local({'points':row['points'],'fan_pole':other,'long_patch':1})}
        else:raise ValueError('Interval uncertainty at the other long threshold')
    else:raise ValueError('Interval uncertainty at the cone ordering threshold')
    net=check_net(p,cut_at(11-fan,0))
    return {'pattern':pattern,'initial_fan':initial,'selected_fan':fan,'slit':0,'branch':branch,
        'strict_support_minimum':str(min(x for _,vs in sr for x in vs)),
        'ordering_A':{s:x.export() for s,x in A.items()},'last_extension_B':{s:x.export() for s,x in B.items()},
        'radial_branch':details,'independent_net_check':{'shared_vertex_pairs':len(net['shared_vertex_pairs']),'strict_separators':net['strict_separators']}}

def replay_saved():
    report=json.loads((ROOT/'results/bipyramid-adjacent.json').read_text())
    if verify_identity()!=report['identity']:raise ValueError('Identity replay mismatch')
    for row in report['examples']:
        if json.loads(json.dumps(certify(row)))!=row['certificate']:raise ValueError('Adjacent replay mismatch: '+row['id'])
    return {'exact_examples':len(report['examples']),'branches':[r['certificate']['branch'] for r in report['examples']],
        'scope':'Specified rational applications; the third decision branch is proved geometrically and is not claimed realized by these examples.'}
if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
