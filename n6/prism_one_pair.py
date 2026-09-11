"""Check the combinatorial star comparison in PRISM_ONE_PAIR.md."""
from itertools import combinations
from n6.certify import require,edge,tree_path
from n6.families import PRISM_FACES,PRISM_CUTS
from n6.polycert import Geometry
from n6.trees import tree_data
from n6.cofacial_star_reduction import REFERENCE


def verify(spec):
    g=Geometry(spec)
    require(tuple(g.faces)==PRISM_FACES,'Expected the stated original prism faces')
    require(sorted(edge(*e) for e in spec['cut_edges'])==list(PRISM_CUTS),'Expected the original two-pair cut tree')
    ref_faces=[g.faces[i] for i in (0,2,4,5)]+[(2,0,3),(2,3,5),(2,1,4),(2,4,5)]
    ref=tree_data(ref_faces,{edge(2,v) for v in (0,1,3,4,5)})
    require(all(sum(a==i or b==i for a,b in ref['hinges'])==1 for i in range(4,8)),
            'All four comparison triangles must be leaves')
    remaining=[0,2,4,5]
    inherited={frozenset((remaining[a],remaining[b])) for a,b in ref['hinges'] if max(a,b)<4}
    actual={frozenset((a,b)) for a in remaining for b in g.adj[a] if b in remaining}
    require(inherited==actual=={frozenset(e) for e in ((0,2),(2,4),(4,5))},'The triangular chain must agree')
    pairs=list(combinations(range(6),2))
    shared={p for p in pairs if set.intersection(*(set(g.faces[i]) for i in tree_path(g.adj,*p)))}
    star=set(combinations(remaining,2));safe=shared|star;residual=[list(p) for p in pairs if p not in safe]
    require(len(shared)==13 and len(safe)==14 and residual==[[1,3]],'Unexpected residual pair')
    return dict(result='verified_prism_one_pair_reduction',pairs_total=15,pairs_proved=14,
                remaining_pairs=residual,triangular_caps_safe=True,curvature_hypothesis_required=False,
                cut_edges=[list(e) for e in PRISM_CUTS],whole_net_claimed=False,
                proof='PRISM_ONE_PAIR.md',theorem_dependencies=[REFERENCE])
