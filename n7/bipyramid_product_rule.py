"""Exact applications and exact limitations of the local diagonal-product test."""
import json
from n7.bipyramid_morph import ROOT,FACES,I,exact_points,support,develop,cut_at,sub,dot,check_net
from n7.bipyramid_rule_checks import patch_pattern
from n7.angle_intervals import pi,face_angle

def condition(row):
    ex=exact_points(row['points']);sr=support(ex);v=[[I.bounds(x) for x in a] for a in ex];pattern,_=patch_pattern(v)
    bad=[a for a in range(5) if pattern[a]=='B' or pattern[(a-1)%5]=='F']
    net=develop(v,cut_at(6,0));D=[dot(sub(net[i][0],net[i+5][0]),sub(net[i][0],net[i+5][0])).sqrt() for i in range(5)]
    H=[dot(sub(ex[5],a),sub(ex[5],a))-dot(sub(ex[6],a),sub(ex[6],a)) for a in ex[:5]]
    tests={q:{a:D[(a-1)%5]*D[a]-(H[a] if q==6 else -H[a]) for a in bad} for q in (5,6)}
    good=[q for q in (5,6) if all(x.lo>=0 for x in tests[q].values())]
    failed={q:[a for a,x in tests[q].items() if x.hi<0] for q in (5,6)}
    planes={q:[dot(sub(a,ex[q]),sub(ex[11-q],ex[q])) for a in ex[:5]] for q in (5,6)}
    out={'pattern':pattern,'bad_vertices':bad,'pole_diagonals':[x.export() for x in D],
        'signed_squared_distance_differences':list(map(str,H)),
        'product_test_margins':{q:{a:x.export() for a,x in tests[q].items()} for q in (5,6)},
        'good_sources':good,'strictly_failed_vertices':failed,
        'whole_ring_plane_passes':{q:min(planes[q])>=0 for q in (5,6)},
        'inward_corner_plane_passes':{q:all(planes[q][a]>=0 for a in bad) for q in (5,6)},
        'strict_support_minimum':str(min(x for _,vs in sr for x in vs))}
    return ex,v,out

def certify(row):
    ex,v,out=condition(row)
    if row.get('expect_both_tests_fail'):
        if not all(out['strictly_failed_vertices'][q] for q in (5,6)):raise ValueError('Both product tests must fail strictly')
        out['scope']='Exact failure of both sufficient product tests, not a proof of net overlap or nonexistence of an unfolding.'
        return out
    if not out['good_sources']:raise ValueError('No source certified by the sufficient product test')
    q=out['good_sources'][0];dist=[sum(dot(sub(v[s],v[a]),sub(v[s],v[a])).sqrt() for s in (5,6)) for a in range(5)]
    slit=max(range(5),key=lambda a:dist[a].mid());comparisons=[]
    for a in range(5):
        if a==slit:continue
        margin=dist[slit]-dist[a]
        if margin.lo<=0:raise ValueError('Strict slit maximum uncertain; ties belong to the written proof')
        comparisons.append({'vertex':a,'margin':margin.export()})
    n=check_net(v,cut_at(q,slit));out.update({'selected_source':q,'slit':slit,'slit_comparisons':comparisons,
        'independent_net_check':{'shared_vertex_pairs':len(n['shared_vertex_pairs']),'strict_separators':n['strict_separators']}})
    return out

def replay_saved():
    report=json.loads((ROOT/'results/bipyramid-product-rule.json').read_text())
    for row in report['examples']:
        if json.loads(json.dumps(certify(row)))!=row['certificate']:raise ValueError('Product rule replay mismatch: '+row['id'])
    return {'exact_examples':len(report['examples']),'applications':sum(not r.get('expect_both_tests_fail',False) for r in report['examples']),
        'two_pole_test_failures':sum(r.get('expect_both_tests_fail',False) for r in report['examples'])}
if __name__=='__main__':print(json.dumps(replay_saved(),indent=2))
