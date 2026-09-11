"""Finite position patterns covered by the new written geometric theorems.

Sharp means curvature >= pi. Gauss--Bonnet and positive curvature exclude
four or more sharp vertices. These are combinatorial position counts,
not fractions of shape space and not numerical geometric certification.
"""
from itertools import combinations
import json
from pathlib import Path
from n6.families import MINUS_FACES,PRISM_FACES
from n6.flat_octahedron import original_candidates
from n6.original_edge_rule import ring_for
from n6.trees import quadrilateral_path_stars


def route_data(faces):
    family,trees=original_candidates(faces);result=[]
    for route in quadrilateral_path_stars(faces):
        v,w,c=(route[k] for k in ('apex','antipode','slit_vertex'))
        ring=ring_for(family,v,w,c);q=set(faces[route['common_quadrilateral']])
        qi=next(i for i in (0,3) if {v,w,ring[i],ring[(i+1)%4]}==q)
        middle=1 if qi==0 else 2
        result.append(dict(source=v,fan=w,slit=c,cuts=route['cuts'],
                           middle_base=[ring[middle],ring[(middle+1)%4]]))
    return trees,result


def covered(kind,sharp):
    sharp=set(sharp);faces=MINUS_FACES if kind=='minus' else PRISM_FACES
    trees,routes=route_data(faces)
    if kind=='minus' and sharp & {0,1}:
        v=min(sharp & {0,1})
        return dict(reason='high_source_with_all_four_fifth_edges_original',source=v,
                    fan=1-v,choose='maximum-curvature equator vertex',
                    proof='OCTA_FLAT_HINGES.md')
    if kind=='minus' and sharp & {2,3}:
        return dict(reason='complementary_cofacial_sources_at_a_sharp_corner',
                    sharp_corner=min(sharp & {2,3}),sources=[0,1],
                    choose='Case B, or a source whose two outer angles obey the Case A no-wrap bound',
                    proof='MINUS_COMPLEMENTARY_SOURCES.md')
    if kind=='minus':
        return dict(reason='sharp_off_quad_threshold_or_forced_complementary_gates',
                    proof='MINUS_EDGE_PROOF.md')
    if kind=='prism' and {2,5}<=sharp:
        return dict(reason='two_sharp_ends',proof='PRISM_TWO_SHARP_ENDS.md')
    for t in trees:
        if t['source'] in sharp and (t['fan'] in sharp or t['slit'] in sharp):
            return dict(reason='high_source_and_automatic_weighted_threshold',
                        **t,proof='OCTA_FLAT_HINGES.md')
    for t in routes:
        if t['fan'] not in sharp and t['slit'] in sharp and sharp & set(t['middle_base']):
            return dict(reason='cofacial_sharp_route_and_Case_B',**t,
                        proof='COFACIAL_STAR_REDUCTION.md')
    return dict(reason="complete_seven_candidate_prism_theorem",proof="PRISM_EDGE_PROOF.md")


def report():
    result=dict(sharp_definition='curvature >= pi',
        domain='Maximum curvature > pi; the all-at-most-pi family is already proved.',
        at_most_three_sharp='Four curvatures >=pi would leave no positive curvature for the other two vertices.',
        scope='Finite position patterns, not percentages of shape space. Covered means a written universal argument, pending independent mathematical review. Open patterns can have proved subfamilies.')
    for kind in ('minus','prism'):
        groups=[]
        for n in (1,2,3):
            patterns=[]
            for sharp in combinations(range(6),n):
                witness=covered(kind,sharp)
                patterns.append(dict(sharp_vertices=list(sharp),status='proved' if witness else 'open',argument=witness))
            groups.append(dict(sharp_count=n,patterns_total=len(patterns),
                               patterns_proved=sum(p['status']=='proved' for p in patterns),patterns=patterns))
        result[kind]=groups
    return result


if __name__=='__main__':
    data=report();root=Path(__file__).parent/'results'
    (root/'sharp-vertex-patterns.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:[{x:g[x] for x in ('sharp_count','patterns_total','patterns_proved')} for g in data[k]] for k in ('minus','prism')},indent=2))
