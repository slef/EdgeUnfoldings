"""Build notes/status.html from the template and status_figs.json."""
import json, datetime
from fractions import Fraction
from pathlib import Path
from progress_data import load_progress
notes = Path(__file__).resolve().parent / 'notes'
research = notes.parent.parent / 'n6'
figs = json.loads((notes / 'status_figs.json').read_text())
figs['thickness'] = json.loads((notes / 'thickness.json').read_text())
for key, filename in [('thesis_df','thesis-DF.svg'),('prism_failure','prism-two-pair.svg'),('local_radial','local-radial-failure.svg'),('apex_entry','caseB-apex-entry.svg'),('minus_pair','minus-pair-switch.svg'),('octa_patches','octa-convex-patches.svg'),('octa_patch_net','octa-one-patch-net.svg'),('hinge_boundary','hinge-boundary-counterexample.svg'),('half_fan','octa-half-fan.svg'),('one_patch','octa-one-patch-two-poles.svg'),('patch_budget','octa-patch-budget.svg'),('three_same','octa-three-same.svg')]:
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
        'faceColors': {i: '#2878b5' if i == pair[0] else '#d26b32' if i == pair[1] else '#dce3e9'
                       for i in range(len(witness['faces']))},
        'radialLabels': True, **display,
    }

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
t = t.replace('__PROGRESS_CSS__', (notes / 'progress_dashboard.css').read_text())
t = t.replace('__PROGRESS_DASHBOARD_JS__', (notes / 'progress_dashboard.js').read_text())
t = t.replace('__SCORE_JSON__', json.dumps(load_progress(notes, research)))
# Preserve earlier progress entries; append a new dated snapshot when results change.
t = t.replace('__PROGRESS_JSON__', json.dumps(json.loads((notes / 'progress_history.json').read_text())))
t = t.replace('__FIGS_JSON__', json.dumps(figs)).replace('__GLOSS_JS__', (notes / 'glossary.js').read_text()).replace('__WIDGET_JS__', (notes / 'widget.js').read_text()).replace('__UPDATED__', datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z'))
(notes / 'status.html').write_text(t)
print(len(t), "bytes")
