"""Build notes/status.html from the template and status_figs.json."""
import json, datetime
from fractions import Fraction
from pathlib import Path
notes = Path(__file__).resolve().parent / 'notes'
research = notes.parent.parent / 'n6'
figs = json.loads((notes / 'status_figs.json').read_text())
figs['thickness'] = json.loads((notes / 'thickness.json').read_text())
for key, filename in [('thesis_df','thesis-DF.svg'),('prism_failure','prism-two-pair.svg')]:
    svg = (research / 'figures' / filename).read_text()
    figs[key] = svg[svg.index('<svg'):].replace('<svg ', '<svg class="net" ', 1)
# Keep the 3D picture, vertex numbering, and cuts tied to the exact witness.
witness = json.loads((research / 'results/thesis-chart-DF.certificate.json').read_text())
if witness['parameter_box']:
    raise ValueError('The thesis illustration requires a fixed-point witness')
points = []
for point in witness['coordinate_polynomials']:
    row = []
    for polynomial in point:
        if any(any(powers) for _, powers in polynomial):
            raise ValueError('The thesis illustration requires constant coordinates')
        value = sum((Fraction(c) for c, _ in polynomial), Fraction(0))
        if value.denominator != 1:
            raise ValueError('The thesis coordinate table expects integer coordinates')
        row.append(int(value))
    points.append(row)
pair = witness['overlap_witness']['faces']
figs['models']['thesis_df'] = {
    'P': points, 'faces': witness['faces'], 'cut': witness['cut_edges'],
    'names': dict(enumerate(witness['thesis_vertex_labels'])),
    'faceNames': {i: witness['face_names'][i] for i in pair},
    'faceColors': {i: '#2878b5' if i == pair[0] else '#d26b32' if i == pair[1] else '#dce3e9'
                   for i in range(len(witness['faces']))},
    'view': {'yaw': -0.5041, 'pitch': -0.06204},
    'radialLabels': True,
    'title': 'DiBiase counterexample: convex octahedron with thesis vertex labels',
    'caption': 'The same convex octahedron. D is blue and F is orange; red edges are cut. '
               'Vertices use DiBiase’s labels 1–6. Drag or use arrow keys to rotate; Home resets the view.',
}
t = (notes / 'status_template.html').read_text()
t = t.replace('__FIGS_JSON__', json.dumps(figs)).replace('__GLOSS_JS__', (notes / 'glossary.js').read_text()).replace('__WIDGET_JS__', (notes / 'widget.js').read_text()).replace('__UPDATED__', datetime.date.today().isoformat())
(notes / 'status.html').write_text(t)
print(len(t), "bytes")
