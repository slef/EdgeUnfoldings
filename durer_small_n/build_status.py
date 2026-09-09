"""Build notes/status.html from the template and status_figs.json."""
import json, datetime
from fractions import Fraction
from pathlib import Path
notes = Path(__file__).resolve().parent / 'notes'
research = notes.parent.parent / 'n6'
figs = json.loads((notes / 'status_figs.json').read_text())
figs['thickness'] = json.loads((notes / 'thickness.json').read_text())
for key, filename in [('thesis_df','thesis-DF.svg'),('prism_failure','prism-two-pair.svg'),('local_radial','local-radial-failure.svg'),('apex_entry','caseB-apex-entry.svg')]:
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
t = (notes / 'status_template.html').read_text()
# Preserve earlier progress entries; append a new dated snapshot when results change.
t = t.replace('__PROGRESS_JSON__', json.dumps(json.loads((notes / 'progress_history.json').read_text())))
t = t.replace('__FIGS_JSON__', json.dumps(figs)).replace('__GLOSS_JS__', (notes / 'glossary.js').read_text()).replace('__WIDGET_JS__', (notes / 'widget.js').read_text()).replace('__UPDATED__', datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z'))
(notes / 'status.html').write_text(t)
print(len(t), "bytes")
