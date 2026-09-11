"""Build notes/status.html from the template and status_figs.json."""
import json, datetime
from fractions import Fraction
from pathlib import Path
from progress_data import load_progress
notes = Path(__file__).resolve().parent / 'notes'
research = notes.parent.parent / 'n6'
figs = json.loads((notes / 'status_figs.json').read_text())
figs['thickness'] = json.loads((notes / 'thickness.json').read_text())
far_pair_svg = (research / 'figures/lemma-F-two-pairs.svg').read_text()
figs['far_pair_targets'] = far_pair_svg[far_pair_svg.index('<svg'):].replace('<svg ', '<svg class="net" ', 1)
projection_svg = (research / 'figures/lemma-F-pole-angle.svg').read_text()
figs['far_projection'] = projection_svg[projection_svg.index('<svg'):].replace('<svg ', '<svg class="net" ', 1)
chord_svg = (research / 'figures/lemma-F-equal-lengths.svg').read_text()
figs['far_chord'] = chord_svg[chord_svg.index('<svg'):].replace('<svg ', '<svg class="net" ', 1)
local_overlap_svg = (research / 'figures/low-local-failure.svg').read_text()
figs['low_local_overlap'] = local_overlap_svg[local_overlap_svg.index('<svg'):].replace('<svg ', '<svg class="net" ', 1)
original_rule_svg = (research / 'figures/original-rule-families.svg').read_text()
figs['original_rule_families'] = original_rule_svg[original_rule_svg.index('<svg'):].replace('<svg ', '<svg class="net" ', 1)
two_sharp_svg = (research / 'figures/prism-two-sharp-ends.svg').read_text()
figs['prism_two_sharp'] = two_sharp_svg[two_sharp_svg.index('<svg'):].replace('<svg ', '<svg class="net" ', 1)
cofacial_svg = (research / 'figures/cofacial-star-comparison.svg').read_text()
figs['cofacial_star'] = cofacial_svg[cofacial_svg.index('<svg'):].replace('<svg ', '<svg class="net" ', 1)
true_scale_svg = (research / 'figures/octa-three-same-true-scale.svg').read_text()
figs['three_same_true_scale'] = true_scale_svg[true_scale_svg.index('<svg'):].replace('<svg ', '<svg class="net" ', 1)
for key, filename in [('local_small_sum','local-small-sum.svg'),('thesis_df','thesis-DF.svg'),('prism_failure','prism-two-pair.svg'),('local_radial','local-radial-failure.svg'),('apex_entry','caseB-apex-entry.svg'),('minus_pair','minus-pair-switch.svg'),('octa_patches','octa-convex-patches.svg'),('octa_patch_net','octa-one-patch-net.svg'),('hinge_boundary','hinge-boundary-counterexample.svg'),('half_fan','octa-half-fan.svg'),('one_patch','octa-one-patch-two-poles.svg'),('patch_budget','octa-patch-budget.svg'),('three_same','octa-three-same.svg'),('chain_switch','octa-three-chain.svg')]:
    svg = (research / 'figures' / filename).read_text()
    figs[key] = svg[svg.index('<svg'):].replace('<svg ', '<svg class="net" ', 1)
# Keep each 3D picture, its labels, and its cuts tied to the exact witness.
def witness_model(filename, names=None, face_names=None, highlight_faces=None, **display):
    witness = json.loads((research / 'results' / filename).read_text())
    if witness['parameter_box']:
        raise ValueError('Counterexample illustrations require fixed-point witnesses')
    points = []
    for point in witness['coordinate_polynomials']:
        row = []
        for polynomial in point:
            if any(any(powers) for _, powers in polynomial):
                raise ValueError('Counterexample illustrations require constant coordinates')
            value = sum((Fraction(c) for c, _ in polynomial), Fraction(0))
            if value.denominator != 1:
                raise ValueError('Counterexample coordinate tables expect integer coordinates')
            row.append(int(value))
        points.append(row)
    pair = witness['overlap_witness']['faces'] if highlight_faces is None else highlight_faces
    names = witness['thesis_vertex_labels'] if names is None else names
    face_names = witness['face_names'] if face_names is None else face_names
    return {
        'P': points, 'faces': witness['faces'], 'cut': witness['cut_edges'],
        'names': dict(enumerate(names)),
        'faceNames': {i: face_names[i] for i in pair},
        'faceColors': {i: '#2878b5' if pair and i == pair[0] else '#d26b32' if len(pair)>1 and i == pair[1] else '#dce3e9'
                       for i in range(len(witness['faces']))},
        'radialLabels': True, **display,
    }

figs['models']['selected_boundary'] = witness_model(
    'selected-octahedron-curvature-equality.certificate.json',
    names=['v','w','u₀','u₁','u₂','u₃'],
    face_names=['V0','V3','V1','V2','W0','W3','W1','W2'],
    highlight_faces=[0,4],
    faceColors={i:'#8fc1dd' if 1 in f else '#e6af78' for i,f in enumerate(json.loads((research/'results/selected-octahedron-curvature-equality.certificate.json').read_text())['faces'])},
    view={'yaw':-0.7,'pitch':0.3},
    title='Exact octahedron at source curvature 180 degrees',
    caption='The maximum curvature at v is exactly 180 degrees. Red edges are the selected cuts. Drag to rotate.',
)

for label, names in [('minus',['A','B','C','D','P','Q']),('prism',['0','1','2','3','4','5'])]:
    filename='low-curvature-'+label+'.certificate.json'
    spec=json.loads((research/'results'/filename).read_text())
    quads=[i for i,f in enumerate(spec['faces']) if len(f)==4]
    figs['models']['low_'+label] = witness_model(
        filename, names=names,
        face_names=['Q' if len(f)==4 else 'T' for f in spec['faces']],
        highlight_faces=quads,
        faceColors={i:'#83bbd5' if len(f)==4 else '#ead2b3' for i,f in enumerate(spec['faces'])},
        view={'yaw':-0.7,'pitch':0.3},
        title='Exact low-curvature '+label+' example with original-edge cuts',
        caption='Original quadrilaterals are blue and stay whole. Red edges are the independently certified cuts. Drag to rotate.',
    )

for kind,names in [('minus',['v=A','w=B','c=C','D','P','Q']),('prism',['0','1','w=2','v=3','4','c=5'])]:
    filename='original-rule-'+kind+'.certificate.json'
    spec=json.loads((research/'results'/filename).read_text())
    figs['models']['original_rule_'+kind] = witness_model(
        filename,names=names,face_names=['Q' if len(f)==4 else 'T'+str(i) for i,f in enumerate(spec['faces'])],
        highlight_faces=[i for i,f in enumerate(spec['faces']) if len(f)==4],
        faceColors={i:'#83bbd5' if len(f)==4 else '#ead2b3' for i,f in enumerate(spec['faces'])},
        view={'yaw':-0.7,'pitch':0.3},title='A sharp fifth-cut endpoint gives an original-edge net',
        caption='The source v is below 180 degrees; c is above it. Blue quadrilaterals remain whole. Red edges are certified cuts.',
    )

for kind,names in [('minus',['v=A','w=B','C','D','P','Q']),('prism',['0','v=1','2','3','4','w=5'])]:
    filename='cofacial-case-B-'+kind+'.certificate.json'
    spec=json.loads((research/'results'/filename).read_text())
    figs['models']['cofacial_case_B_'+kind] = witness_model(
        filename,names=names,face_names=['Q' if len(f)==4 else 'T'+str(i) for i,f in enumerate(spec['faces'])],
        highlight_faces=[i for i,f in enumerate(spec['faces']) if len(f)==4],
        faceColors={i:'#83bbd5' if len(f)==4 else '#ead2b3' for i,f in enumerate(spec['faces'])},
        view={'yaw':-0.7,'pitch':0.3},title='A newly proved two-sharp-vertex family',
        caption=('C and D are sharp.' if kind=='minus' else 'Vertices 2 and 4 are sharp.')+
                ' Red edges give the new proved net. Original blue quadrilaterals remain whole. Drag to rotate.',
    )

figs['models']['prism_two_sharp'] = witness_model(
    'prism-two-sharp-point.certificate.json', names=['0','1','2','3','4','5'],
    face_names=list('ABCDEF'), highlight_faces=[1,3],
    faceColors={i:'#9bc7dd' if i in (1,3) else '#edc189' if i in (0,5) else '#e2e8e8' for i in range(6)},
    view={'yaw':-0.7,'pitch':0.3}, title='The prism branch with both end vertices sharp',
    caption='Vertices 2 and 5 have curvature above 180 degrees. Cut their five incident edges, shown in red. Drag to rotate.',
)

for suffix, title in [('failure','A nonmaximum slit with two certified local overlaps'),
                      ('repair','The same solid with a certified successful slit')]:
    figs['models']['low_local_'+suffix] = witness_model(
        'low-local-'+suffix+'.certificate.json',
        names=['0','1','2','w=3','4','v=5'],face_names=['F'+str(i) for i in range(8)],
        highlight_faces=[3,4,7],
        faceColors={i:'#8fc1dd' if i in (0,1,4,5) else '#e6af78' for i in range(8)},
        view={'yaw':1.6224793791,'pitch':1.5440872643},title=title,
        caption='Original integer coordinates, seen from the broad side. Red edges are cut. Drag to rotate.',
    )

for kind,names in [('minus',['A','B','C','D','P','Q']),('prism',['0','1','2','3','4','5'])]:
    filename='flat-hinges-'+kind+'-boundary.certificate.json'
    spec=json.loads((research/'results'/filename).read_text())
    figs['models']['flat_'+kind+'_boundary'] = witness_model(
        filename,names=names,face_names=['Q' if len(f)==4 else 'T' for f in spec['faces']],
        highlight_faces=[i for i,f in enumerate(spec['faces']) if len(f)==4],
        faceColors={i:'#83bbd5' if len(f)==4 else '#ead2b3' for i,f in enumerate(spec['faces'])},
        view={'yaw':-0.7,'pitch':0.3},title='An exact 180-degree boundary example',
        caption='The blue quadrilaterals stay whole. Red edges form an independently certified original-edge net.',
    )

figs['models']['thesis_df'] = witness_model(
    'thesis-chart-DF.certificate.json',
    view={'yaw': -0.5041, 'pitch': -0.06204},
    title='DiBiase counterexample: convex octahedron with thesis vertex labels',
    caption='The same convex octahedron. D is blue and F is orange; red edges are cut. '
            'Vertices use DiBiase’s labels 1–6. Drag or use arrow keys to rotate; Home resets the view.',
)
figs['models']['prism_failure'] = witness_model(
    'prism-two-pair-failure.certificate.json',
    names=['a', 'b', 'c', 'a′', 'b′', 'c′'],
    face_names=['base', 'Q1', 'T2', 'Q3', 'T4', 'top'],
    view={'yaw': 0.25, 'pitch': -0.35},
    title='Prism with one diagonal: exact counterexample to the fixed two-pair tree',
    caption='The same thin convex polyhedron. Q1 is blue and Q3 is orange; red edges are the '
            'failing cut tree. Both quadrilaterals remain whole. Drag or use arrow keys to rotate; Home resets the view.',
)
apex_certificate = json.loads((research / 'results/caseB-apex-entry.certificate.json').read_text())
apex_face_names = []
for f in apex_certificate['faces']:
    pole = 'V' if 0 in f else 'W'
    equator = set(f) - {0, 1}
    index = next(i for i in range(4) if equator == {2+i, 2+(i+1)%4})
    apex_face_names.append(pole + str(index))
left, right = apex_face_names.index('V0'), apex_face_names.index('V2')
figs['models']['apex_entry'] = witness_model(
    'caseB-apex-entry.certificate.json', names=['v','w','u₀','u₁','u₂','u₃'],
    face_names=apex_face_names, highlight_faces=[left,right],
    faceColors={i: '#e4a15e' if i==left else '#ac8bca' if i==right else '#cdddea' for i in range(8)},
    view={'yaw': -2.65, 'pitch': -0.25},
    title='Exact convex octahedron refuting the individual-apex exclusion',
    caption='The same convex polyhedron. The two tested petals are orange and purple; red edges are cut. Drag or use arrow keys to rotate.',
)
for apex,fan in [('P',{0,1,6}),('Q',{0,3,4})]:
    figs['models']['minus_pair_'+apex] = witness_model(
        'minus-pair-'+apex+'.certificate.json', names=['A','B','C','D','P','Q'],
        face_names=['ACBD','ACP','APQ','ADQ','BDQ','BPQ','BCP'],highlight_faces=[0,2],
        faceColors={i:'#8fc1dd' if i in fan else '#e6af78' for i in range(7)},
        view={'yaw':-0.8,'pitch':0.45},
        title='Minus-edge two-choice example: cuts at '+apex,
        caption='The same exact polyhedron, with the cuts for T_'+apex+'. Drag or use arrow keys to rotate.',
    )
t = (notes / 'status_template.html').read_text()
figs['models']['octa_patches'] = witness_model(
    'octa-patches-one.certificate.json', names=['v','w','u₀','u₁','u₂','u₃'],
    face_names=['W'+str(i) for i in range(4)]+['V'+str(i) for i in range(4)],
    highlight_faces=[1,5], view={'yaw': -0.7, 'pitch': 0.3},
    title='Exact octahedron with one nonconvex flattened patch',
    caption='The same convex octahedron. The two colored faces form Q₁ when flattened. Red edges give the certified successful opening at u₃. Drag to rotate.',
)
figs['models']['hinge_boundary'] = witness_model(
    'hinge-boundary-counterexample.certificate.json', names=['v','w','u₀','u₁','u₂','u₃'],
    face_names=['W'+str(i) for i in range(4)]+['V'+str(i) for i in range(4)],
    highlight_faces=[0,6], faceColors={i:'#61a9d3' if i==0 else '#e89a52' if i==6 else '#dce5eb' for i in range(8)},
    view={'yaw': -0.7, 'pitch': 0.3},
    title='Exact counterexample to the conditional far-fan reduction',
    caption='The actual thin convex octahedron. Blue W₀ and orange V₂ overlap only in the specified net. Red edges are cut. The four-cut source v is not sharpest. Drag to rotate.',
)
figs['models']['half_fan'] = witness_model(
    'half-fan-bf.certificate.json', names=['v','w','u₀','u₁','u₂','u₃'],
    face_names=['W'+str(i) for i in range(4)]+['V'+str(i) for i in range(4)],
    highlight_faces=[2,6], faceColors={i:'#8fc1dd' if i<4 else '#e6af78' for i in range(8)},
    view={'yaw': -0.7, 'pitch': 0.3},
    title='Two adjacent bad patches: theorem-selected cuts',
    caption='The same exact convex octahedron. The blue faces form the fan at w; red edges are the four cuts at v and w–u₁. Drag to rotate.',
)
for letter, fan in [('A',1),('B',0)]:
    figs['models']['one_patch_'+letter] = witness_model(
        'one-patch-'+letter+'.certificate.json', names=['v','w','u₀','u₁','u₂','u₃'],
        face_names=['W'+str(i) for i in range(4)]+['V'+str(i) for i in range(4)],
        highlight_faces=[1,5],
        faceColors={i:'#8fc1dd' if (i<4)==(fan==1) else '#e6af78' for i in range(8)},
        view={'yaw': -0.7, 'pitch': 0.3},
        title='One bad patch: cut choice '+letter,
        caption='The same exact solid, with original vertex labels. Red edges are cut; blue triangles form the remaining fan. Drag to rotate.',
    )
for key, filename in [('patch_budget','patch-budget-adjacent-below-pi.certificate.json'),
                      ('three_same','patch-budget-three-same.certificate.json')]:
    figs['models'][key] = witness_model(
        filename, names=['v','w','u₀','u₁','u₂','u₃'],
        face_names=['W'+str(i) for i in range(4)]+['V'+str(i) for i in range(4)],
        highlight_faces=[2,6], faceColors={i:'#8fc1dd' if i<4 else '#e6af78' for i in range(8)},
        view={'yaw': -0.7, 'pitch': 0.3},
        title='Exact '+('two-adjacent-patch example below the half-turn threshold' if key=='patch_budget' else 'three-patch example with a common lean direction'),
        caption='The same exact convex solid. Red edges give an independently certified successful net on this example; blue faces meet at w. Drag to rotate.',
    )
for key, filename, title in [
    ('chain_switch', 'three-chain-switch.certificate.json', 'A three-patch shape covered by the stronger switch theorem'),
    ('chain_uncovered', 'three-chain-uncovered.certificate.json', 'An exact shape outside the new middle-patch conditions'),
]:
    figs['models'][key] = witness_model(
        filename, names=['v','w','u₀','u₁','u₂','u₃'],
        face_names=['W'+str(i) for i in range(4)]+['V'+str(i) for i in range(4)],
        highlight_faces=[1,5], faceColors={i:'#8fc1dd' if i<4 else '#e6af78' for i in range(8)},
        view={'yaw': -0.7, 'pitch': 0.3}, title=title,
        caption='The exact convex solid. The two highlighted faces form the middle patch; red edges give a separately certified successful net. Drag to rotate.',
    )
# View perpendicular to each example's broadest plane, avoiding the old
# almost end-on view. These are camera rotations, never changes to points.
figs['models']['three_same']['view'] = {'yaw': -2.5206086676, 'pitch': 0.7051927251}
figs['models']['chain_uncovered']['view'] = {'yaw': 0.1086721582, 'pitch': 0.0078613013}
figs['models']['local_gate_chain'] = witness_model(
    'local-gate-three-chain.certificate.json', names=['v','w','u₀','u₁','u₂','u₃'],
    face_names=['W'+str(i) for i in range(4)]+['V'+str(i) for i in range(4)],
    highlight_faces=[2,3,6,7], faceColors={i:'#8fc1dd' if i<4 else '#e6af78' for i in range(8)},
    view={'yaw': -0.7, 'pitch': 0.3},
    title='Lemma L at the maximum-curvature equator slit',
    caption='Same solid as the earlier uncovered middle-patch example, with a different fifth cut: w–u₃. The highlighted faces are the two flank patches. This selected net has an independent all-pairs certificate. Drag to rotate.',
)
figs['models']['far_projection_low'] = witness_model(
    'far-projection-low-curvature.certificate.json', names=['u₀','u₂','v','u₁','u₃','w'],
    face_names=['V0','V3','W0','W3','V1','V2','W1','W2'],
    highlight_faces=[0,1,2,3,4,5,6,7],
    faceColors={i:'#8fc1dd' if i in (2,3,6,7) else '#e6af78' for i in range(8)},
    view={'yaw': -0.7, 'pitch': 0.3}, title='A low-curvature octahedron covered by the pole-angle theorem',
    caption='Exact integer coordinates. Red edges form the selected original-edge net, proved safe by the pole-angle theorem. Drag to rotate.',
)
t = t.replace('__PROGRESS_CSS__', (notes / 'progress_dashboard.css').read_text())
t = t.replace('__PROGRESS_DASHBOARD_JS__', (notes / 'progress_dashboard.js').read_text())
t = t.replace('__SCORE_JSON__', json.dumps(load_progress(notes, research)))
# Preserve earlier progress entries; append a new dated snapshot when results change.
t = t.replace('__PROGRESS_JSON__', json.dumps(json.loads((notes / 'progress_history.json').read_text())))
t = t.replace('__FIGS_JSON__', json.dumps(figs)).replace('__GLOSS_JS__', (notes / 'glossary.js').read_text()).replace('__WIDGET_JS__', (notes / 'widget.js').read_text()).replace('__UPDATED__', datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z'))
(notes / 'status.html').write_text(t)
print(len(t), "bytes")
