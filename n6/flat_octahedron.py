"""Original-face hypotheses for OCTA_FLAT_HINGES.md, including pi boundaries."""
from fractions import Fraction as F
from n6.certify import edge,require
from n6.low_curvature_types import candidate_trees
from n6.polycert import Geometry
from n6.prism_paths import polygon_angle_product
from n6.regimes import curvature_pi
from n6.slit_threshold import weighted_slit_pi


def exact_polygon_angle_sum_pi(g,vertex):
    """Recognize a finite set of rational multiples of pi at exact points.

    Returns the exact sum divided by pi, or None. This is deliberately a
    sufficient recognizer, not a general symbolic trigonometric solver.
    """
    if any(q.lo!=q.hi for p in g.p for q in p):return None
    p=[[q.lo for q in row] for row in g.p];total=F(0)
    acute={F(0):F(1,2),F(1,4):F(1,3),F(1,2):F(1,4),F(3,4):F(1,6)}
    for face in g.faces:
        if vertex not in face:continue
        i=face.index(vertex)
        a=[x-y for x,y in zip(p[face[i-1]],p[vertex])]
        b=[x-y for x,y in zip(p[face[(i+1)%len(face)]],p[vertex])]
        d=sum(x*y for x,y in zip(a,b));q=d*d/(sum(x*x for x in a)*sum(x*x for x in b))
        if q not in acute:return None
        angle=acute[q];total+=angle if d>=0 else 1-angle
    return total


def curvature_bands(g):
    bands={}
    for x in range(6):
        band=curvature_pi(polygon_angle_product(g,x))
        if band is None:
            total=exact_polygon_angle_sum_pi(g,x)
            if total is not None:band='<' if total>1 else '>' if total<1 else '='
        bands[x]=band
    return bands


def original_candidates(faces):
    family=candidate_trees(faces);original=set(map(tuple,family['original_edges']))
    full=original|set(map(tuple,family['artificial_diagonals']))
    adj={v:{x for x in range(6) if edge(v,x) in original} for v in range(6)}
    trees=[]
    for v in range(6):
        if len(adj[v])!=4:continue
        w=next(x for x in range(6) if x!=v and edge(v,x) not in full)
        for c in sorted(adj[w]):
            trees.append(dict(source=v,fan=w,slit=c,
                              cuts=sorted({edge(v,x) for x in adj[v]}|{edge(w,c)})))
    return family,trees


def verify_low_existence(spec):
    g=Geometry(spec);family=candidate_trees(g.faces);bands=curvature_bands(g)
    require(all(b in ('<','=') for b in bands.values()),'All original curvatures <=pi must be certified')
    return dict(result='verified_closed_low_curvature_original_edge_existence',
                **family,curvature_comparisons_with_pi=bands,
                maximum_curvature_equal_to_pi_included=True,
                at_least_one_original_candidate_unfolds=True,input_tree_nonoverlap_checked=False,
                full_n6_proved=False,proof='OCTA_FLAT_HINGES.md',
                scope='The written flat-hinge theorem gives existence for this original-face domain, including exact pi boundaries. This is not a nonoverlap check of the supplied tree or a formal verification of the geometric proof.')


def verify_fixed_tree(spec):
    g=Geometry(spec);family,trees=original_candidates(g.faces);cuts=sorted(edge(*e) for e in spec['cut_edges'])
    choices=[t for t in trees if t['cuts']==cuts]
    require(bool(choices),'Expected an original degree-four star plus an original fifth edge')
    bands=curvature_bands(g);totals={x:polygon_angle_product(g,x) for x in range(6)}
    low=all(b in ('<','=') for b in bands.values())
    for t in choices:
        v,w,c=(t[k] for k in ('source','fan','slit'))
        if not (low or bands[v] in ('>','=')):continue
        threshold='>' if bands[c] in ('>','=') or bands[w] in ('>','=') else weighted_slit_pi(totals[c],totals[w])
        if threshold not in ('>','='):continue
        return dict(result='verified_original_edge_fixed_tree_threshold',type=family['type'],
                    **t,curvature_comparisons_with_pi=bands,all_curvatures_at_most_pi=low,
                    source_curvature_at_least_pi=bands[v] in ('>','='),
                    weighted_threshold_comparison=threshold,artificial_diagonals_uncut=True,
                    input_tree_nonoverlapping_by_written_theorem=True,full_n6_proved=False,
                    proof='OCTA_FLAT_HINGES.md',
                    scope='This original-edge tree satisfies the source and weighted slit conditions on the original polygonal domain. The written flat-hinge theorem proves it safe; formal mathematical verification is not claimed.')
    raise ValueError('No source/threshold interpretation of this original tree is certified')
