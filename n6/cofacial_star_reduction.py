"""Exact hypotheses and residual pairs for COFACIAL_STAR_REDUCTION.md.

A published shortest-path star-unfolding theorem supplies nonoverlap of
all faces except one movable original quadrilateral. No curvature ranking
is needed; the remaining pairs are not silently declared nonoverlapping.
"""
from itertools import combinations
from n6.certify import edge,require,tree_path
from n6.polycert import Geometry
from n6.trees import quadrilateral_path_stars,incidence,tree_data

REFERENCE=dict(authors='Stephen Kiazyk and Anna Lubiw',year=2015,theorem=4,
    title='Star Unfolding from a Geodesic Curve',
    url='https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SOCG.2015.390',
    role='Nonoverlap of the shortest-path star, including a vertex source')


def verify(spec):
    g=Geometry(spec);cuts=sorted(edge(*e) for e in spec['cut_edges'])
    choices=[t for t in quadrilateral_path_stars(g.faces) if t['cuts']==cuts]
    require(len(choices)==1,'Expected one cofacial source-and-route interpretation')
    t=choices[0];v,w,q=(t[x] for x in ('apex','antipode','common_quadrilateral'))
    f=g.faces[q];require(len(f)==4 and {v,w}<=set(f),'Expected cofacial opposite corners')
    inc=incidence(g.faces);neighbors={b if a==v else a for a,b in inc if v in (a,b)}
    require(neighbors==set(range(6))-{v,w},'Source must see every other vertex by an original edge')
    require(edge(v,w) not in inc,'Reference diagonal must not be an original edge')
    j=f.index(v);ordered=f[j:]+f[:j]
    require(ordered[2]==w,'The source and nonneighbor must be opposite corners')
    require(len(g.adj[q])==1,'The movable quadrilateral is not a leaf')
    remaining=[i for i in range(len(g.faces)) if i!=q]
    subadj={i:[j for j in g.adj[i] if j!=q] for i in remaining}
    for i in remaining:tree_path(subadj,remaining[0],i)
    # Split only the comparison face. No strict-facet claim is made for these
    # coplanar reference triangles; Geometry already certified the original Q.
    reference_faces=[g.faces[i] for i in remaining]+[(v,ordered[1],w),(v,w,ordered[3])]
    reference_cuts={edge(v,x) for x in range(6) if x!=v}
    reference=tree_data(reference_faces,reference_cuts)
    require(all(sum(a==i or b==i for a,b in reference['hinges'])==1
                for i in (len(remaining),len(remaining)+1)),
            'The two reference triangles must be leaves')
    actual_hinges={frozenset((remaining.index(i),remaining.index(j)))
                  for i in remaining for j in subadj[i]}
    inherited={frozenset((a,b)) for a,b in reference['hinges'] if max(a,b)<len(remaining)}
    require(actual_hinges==inherited,'The remaining face developments do not agree')
    allpairs=list(combinations(range(len(g.faces)),2))
    shared={p for p in allpairs if set.intersection(*(set(g.faces[i]) for i in tree_path(g.adj,*p)))}
    star={p for p in allpairs if q not in p};safe=star|shared
    residual=[list(p) for p in allpairs if p not in safe]
    require(len(residual)==2,'Unexpected residual count for the stated n=6 types')
    return dict(result='verified_cofacial_star_pair_reduction',source=v,nonneighbor=w,
        via=t['slit_vertex'],movable_quadrilateral=q,cut_edges=[list(e) for e in cuts],
        pairs_total=len(allpairs),pairs_proved=len(safe),remaining_pairs=residual,
        inherited_star_pairs=len(star),additional_shared_vertex_pairs=len(shared-star),
        original_faces_remain_whole=True,curvature_ranking_required=False,
        whole_net_claimed=False,proof='COFACIAL_STAR_REDUCTION.md',
        theorem_dependencies=[REFERENCE],
        scope='All but the two listed pairs follow from the written reduction for this exact original-face domain. Those two pairs, and the existence of a successful candidate, are not asserted.')


def case_frame(spec):
    """Shared geometry for the one remaining opposite-petal triple."""
    from n6.flat_octahedron import original_candidates,curvature_bands
    from n6.original_edge_rule import ring_for
    partial=verify(spec);g=Geometry(spec);family,trees=original_candidates(g.faces)
    t=next(t for t in trees if t['cuts']==sorted(edge(*e) for e in spec['cut_edges']))
    v,w,c=(t[k] for k in ('source','fan','slit'));ring=ring_for(family,v,w,c)
    qset=set(g.faces[partial['movable_quadrilateral']])
    qi=next(i for i in (0,3) if {v,w,ring[i],ring[(i+1)%4]}==qset)
    middle=1 if qi==0 else 2;u,up=ring[middle],ring[(middle+1)%4]
    fi=next(i for i,f in enumerate(g.faces) if set(f)=={v,u,up})
    bands=curvature_bands(g)
    require(bands[w] in ('<','='),'Fan curvature <=pi is not certified')
    from n6.prism_paths import polygon_angle_product
    from n6.original_edge_rule import sum_pi
    totals={x:polygon_angle_product(g,x) for x in (c,w)}
    gate=sum_pi(totals,bands,[c,w])
    require(gate in ('>','='),'Route endpoint plus fan curvature >=pi is not certified')
    return g,v,w,c,ring,middle,fi,bands


def verify_case_B(spec):
    """A slit-plus-fan curvature gate, low fan, and the sole Case B suffice."""
    from n6.prism_paths import polygon_angle_product
    from n6.curvature import face_angle
    from n6.regimes import two_curvatures_angle
    g,v,w,c,ring,middle,fi,bands=case_frame(spec)
    u,up=ring[middle],ring[(middle+1)%4]
    if bands[u] in ('>','=') or bands[up] in ('>','='):case='>'
    else:
        case=two_curvatures_angle(polygon_angle_product(g,u),polygon_angle_product(g,up),
                                 face_angle(g.p,g.faces[fi],g.h[fi],v))
    require(case in ('>','='),'The sole remaining opposite-petal triple is not certified in Case B')
    return dict(result='verified_cofacial_curvature_gate_case_B',source=v,fan=w,slit=c,
        curvature_comparisons_with_pi=bands,route_hypothesis='fan<=pi and slit+fan>=pi',remaining_middle_base=[u,up],middle_face=fi,
        remaining_case_B_comparison=case,original_faces_remain_whole=True,
        whole_net_safe_by_written_theorem=True,proof='COFACIAL_STAR_REDUCTION.md',
        dependencies=['ORIGINAL_EDGE_RULE.md','OCTA_FLAT_HINGES.md',REFERENCE],
        full_type_proved=False,
        scope='These exact hypotheses supply the whole specified original-edge net by the written geometric reduction. The proof awaits independent review; numerical experiments are not premises.')


def verify_case_A(spec):
    """The actual-length Case A separator finishes the same original net."""
    from n6.prism_paths import polygon_angle_product
    from n6.curvature import face_angle,cmul,conjugate
    from n6.regimes import two_curvatures_angle
    from n6.intervals import sub,dot,cross,norm2
    from n6.case_a_one_sided import length_planar_tests
    g,v,w,c,ring,middle,fi,bands=case_frame(spec)
    u,up=ring[middle],ring[(middle+1)%4]
    totals={x:polygon_angle_product(g,x) for x in (u,up)}
    case=two_curvatures_angle(totals[u],totals[up],face_angle(g.p,g.faces[fi],g.h[fi],v))
    require(case=='<','The remaining triple is not certified in strict Case A')
    def outer(j):
        target={v,ring[j],ring[(j+1)%4]}
        candidates=[i for i,f in enumerate(g.faces) if target<=set(f)]
        require(len(candidates)==1,'Expected a unique original outer face')
        f=g.faces[candidates[0]];k=f.index(v)
        a=sub(g.p[f[k-1]],g.p[v]);b=sub(g.p[f[(k+1)%len(f)]],g.p[v])
        return candidates[0],(dot(a,b),norm2(cross(a,b)).sqrt())
    left,la=outer(middle-1);right,ra=outer((middle+1)%4)
    alpha=cmul(face_angle(g.p,g.faces[fi],g.h[fi],u),conjugate(totals[u]))
    beta=cmul(face_angle(g.p,g.faces[fi],g.h[fi],up),conjugate(totals[up]))
    tests=length_planar_tests(alpha,beta,la,ra,norm2(sub(g.p[v],g.p[u])).sqrt(),
                           norm2(sub(g.p[v],g.p[up])).sqrt(),norm2(sub(g.p[u],g.p[up])).sqrt())
    tests['middle_nonobtuse_condition']=face_angle(g.p,g.faces[fi],g.h[fi],v)[0].lo>=0
    require(tests['left_length_condition'] or tests['right_length_condition'],
            'Neither actual-length Case A separator is certified')
    return dict(result='verified_cofacial_curvature_gate_length_case_A',source=v,fan=w,slit=c,
        curvature_comparisons_with_pi=bands,route_hypothesis='fan<=pi and slit+fan>=pi',remaining_middle_base=[u,up],middle_face=fi,
        remaining_original_pair=[left,right],case_A_comparison=case,**tests,
        original_faces_remain_whole=True,whole_net_safe_by_written_theorem=True,
        proof='CASE_A_LENGTH_SEPARATORS.md',dependencies=['COFACIAL_STAR_REDUCTION.md','ORIGINAL_EDGE_RULE.md',REFERENCE],
        full_type_proved=False,scope='The specified original net satisfies the written actual-length Case A theorem. No universal low-fan Case A claim is made.')


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    ap.add_argument('--whole-net',choices=['case_A','case_B'])
    args=ap.parse_args();spec=json.loads(args.input.read_text());set_precision(spec.get('suggested_fractional_bits',240))
    fn=verify_case_A if args.whole_net=='case_A' else verify_case_B if args.whole_net=='case_B' else verify
    print(json.dumps(fn(spec),indent=2))
