"""Hypotheses and original-edge candidates for two low-curvature n=6 families.

NONSIMPLICIAL_LOW_CURVATURE.md proves existence among the returned candidates.
This checker does NOT declare the supplied cut tree nonoverlapping merely
because the hypotheses pass. All-pair verification of a specified net is
a separate polycert operation. The curvature bound is strictly below pi.
"""
from itertools import product
from n6.certify import edge,require
from n6.polycert import Geometry
from n6.prism_paths import polygon_angle_product
from n6.regimes import curvature_pi


def candidate_trees(faces):
    sizes=sorted(map(len,faces))
    require(sizes in ([3]*6+[4],[3]*4+[4]*2),'Expected one of the two nonsimplicial types')
    original={edge(a,b) for f in faces for a,b in zip(f,f[1:]+f[:1])}
    adj={v:{b if a==v else a for a,b in original if v in (a,b)} for v in range(6)}
    expected=[3,3,4,4,4,4] if len(faces)==7 else [3,3,3,3,4,4]
    require(sorted(map(len,adj.values()))==expected,'Unexpected vertex degrees')
    quads=[f for f in faces if len(f)==4]
    options=[(edge(f[0],f[2]),edge(f[1],f[3])) for f in quads]
    completions=[]
    for diagonals in product(*options):
        added=set(diagonals)
        if len(added)!=len(quads) or added&original:continue
        full=original|added
        if all(sum(v in e for e in full)==4 for v in range(6)):
            completions.append((added,full))
    require(len(completions)==1,'Expected the unique octahedral diagonal completion')
    added,full=completions[0]
    opposite={v:next(x for x in range(6) if x!=v and edge(x,v) not in full) for v in range(6)}
    eligible=[v for v in range(6) if len(adj[v])==4]
    if len(faces)==7:
        sources=[v for v in eligible if opposite[v] in eligible]
        require(len(sources)==2 and opposite[sources[0]]==sources[1],'Missing unaffected opposite pair')
        # Fix either member of this pair; four fifth-edge choices suffice.
        sources=sources[:1]
    else:
        sources=eligible
        require(len(sources)==2 and edge(*sources) in original,'Expected adjacent degree-four sources')
        forbidden=[]
        for v in sources:
            w=opposite[v]
            targets=[x for x in range(6) if edge(w,x) in added]
            require(len(targets)==1,'Expected one forbidden fifth edge')
            forbidden.append(targets[0])
        # Each bad maximum must be compared against the other bad maximum.
        require(forbidden[0]!=forbidden[1],'Forbidden choices must differ')
        for v in sources:
            equator=set(range(6))-{v,opposite[v]}
            require(set(forbidden)<=equator,'Missing the cross-ranking argument')
    trees=[]
    for v in sources:
        w=opposite[v]
        for c in sorted(adj[w]):
            cuts={edge(v,x) for x in adj[v]}|{edge(w,c)}
            require(len(cuts)==5 and cuts<=original and not cuts&added,'Artificial diagonal in candidate cuts')
            trees.append(dict(source=v,fan=w,slit=c,cuts=[list(e) for e in sorted(cuts)]))
    return dict(type='octahedron_minus_edge' if len(faces)==7 else 'prism_with_one_diagonal',
                original_edges=[list(e) for e in sorted(original)],
                artificial_diagonals=[list(e) for e in sorted(added)],
                candidate_trees=trees)


def verify(spec):
    g=Geometry(spec);family=candidate_trees(g.faces)
    bands={x:curvature_pi(polygon_angle_product(g,x)) for x in range(6)}
    require(all(b=='<' for b in bands.values()),'Not every original vertex curvature is certified strictly below pi')
    cuts=sorted(edge(*e) for e in spec['cut_edges'])
    return dict(result='verified_low_curvature_original_edge_existence_hypotheses',
                **family,curvature_comparisons_with_pi=bands,
                parameter_dimension=len(g.box),
                at_least_one_candidate_unfolds_by_written_theorem=True,
                input_tree_in_candidate_family=any(cuts==[tuple(e) for e in t['cuts']] for t in family['candidate_trees']),
                input_tree_nonoverlap_checked=False,
                maximum_curvature_equal_to_pi_included=False,
                full_n6_proved=False,proof='NONSIMPLICIAL_LOW_CURVATURE.md',
                scope='All original vertex curvatures in this explicit domain are strictly below pi. The written refinement-and-limit proof gives existence among the original-edge candidates. This is not formal verification of that proof or a nonoverlap check of the input tree.')


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('certificate',type=Path)
    args=ap.parse_args();spec=json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits',240))
    print(json.dumps(verify(spec),indent=2))
