"""Exact hypotheses for the two new prism switching branches, on tree T."""
from n6.certify import require
from n6.families import PRISM_FACES
from n6.polycert import Geometry
from n6.prism_one_pair import verify as one_pair
from n6.prism_paths import polygon_angle_product
from n6.flat_octahedron import curvature_bands
from n6.original_edge_rule import sum_pi
from n6.curvature import cmul,conjugate,cdet
from n6.regimes import two_curvatures_angle
from n6.intervals import sub,dot,cross,norm2
from n6.case_a_one_sided import comparison


def angle(g,f,v):
    face=g.faces[f];i=face.index(v)
    a=sub(g.p[face[i-1]],g.p[v]);b=sub(g.p[face[(i+1)%len(face)]],g.p[v])
    return dot(a,b),norm2(cross(a,b)).sqrt()


def wide_comparison(a,theta):
    if a[0].lo>=0:return '>'
    if a[0].hi<0:
        square=cmul(a,a)
        return comparison(cdet((-square[0],-square[1]),theta))
    return None


def verify_sharp_fan_fallback(spec):
    reduction=one_pair(spec);g=Geometry(spec);bands=curvature_bands(g)
    require(bands[2] in ('>','=') and bands[5] in ('<','='),'Expected sharp 2 and low fan 5')
    t={v:polygon_angle_product(g,v) for v in range(6)}
    case=two_curvatures_angle(t[3],t[4],angle(g,4,1));require(case=='<','Expected strict Case A in the near-star')
    require(angle(g,4,1)[0].hi<0,'Expected the obtuse middle angle E1')
    theta=cmul(cmul(angle(g,4,3),conjugate(t[3])),cmul(angle(g,4,4),conjugate(t[4])))
    c=wide_comparison(angle(g,2,1),theta);d=wide_comparison(angle(g,3,1),theta)
    require(d=='<','The D1 wider-angle failure is not certified')
    upper=two_curvatures_angle(t[3],t[4],angle(g,5,5))
    if upper=='<':
        theta5=cmul(cmul(angle(g,5,3),conjugate(t[3])),cmul(angle(g,5,4),conjugate(t[4])))
        upper_bounds={name:wide_comparison(angle(g,i,5),theta5) for i,name in [(1,'B5'),(3,'D5')]}
        require(all(v in ('>','=') for v in upper_bounds.values()),'The predicted upper wider bounds are not resolved')
    elif upper in ('>','='):upper_bounds={'reason':'Case B; both wider thresholds are at least pi'}
    else:raise ValueError('Upper pair comparison unresolved')
    return dict(result='verified_prism_sharp_fan_fallback',curvature_comparisons_with_pi=bands,
                near_star_middle_obtuse=True,near_star_case_A=case,
                C1_wider_comparison=c,D1_wider_comparison=d,upper_view_case_comparison=upper,
                upper_wider_bounds=upper_bounds,one_pair_reduction=reduction,
                input_tree_nonoverlapping_by_written_theorem=True,proof='PRISM_SHARP_FAN_SWITCH.md')


def verify_gate_fallback(spec):
    reduction=one_pair(spec);g=Geometry(spec);bands=curvature_bands(g)
    t={v:polygon_angle_product(g,v) for v in range(6)}
    require(bands[2] in ('<','='),'Low fan 2 is not certified')
    gates={name:sum_pi(t,bands,vertices) for name,vertices in [('route',[0,2]),('lower_base',[0,1])]}
    require(all(x in ('>','=') for x in gates.values()),'Both curvature gates must be certified')
    require(angle(g,5,3)[0].hi<0,'Expected the obtuse F3 switch')
    require(angle(g,5,5)[0].lo>0,'The predicted acute fallback middle F5 is unresolved')
    return dict(result='verified_prism_gate_fallback',curvature_comparisons_with_pi=bands,
                gate_comparisons=gates,first_middle_obtuse=True,fallback_middle_acute=True,
                one_pair_reduction=reduction,input_tree_nonoverlapping_by_written_theorem=True,
                proof='PRISM_GATE_SWITCH.md')
