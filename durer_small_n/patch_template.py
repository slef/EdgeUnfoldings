s=open('notes/status_template.html').read()
assert '__FIGS_JSON__' in s
s = s.replace("svg.net .w { fill: var(--ink); }", """svg.net .w { fill: var(--ink); }
svg.net .outline { fill: none; stroke-width: 2.2; } svg.net .outline.o1 { stroke: var(--hit); } svg.net .outline.o2 { stroke: var(--M); } svg.net .outline.o3 { stroke: var(--fan); stroke-dasharray: 5 3; }
svg.net .flat { fill: none; stroke: var(--petal); stroke-width: 1.2; stroke-dasharray: 3 3; }
svg.net .hl { stroke-width: 2; stroke: var(--hit); }
.axis { max-width: 620px; margin: 14px 0 20px; } .axis svg { width: 100%; height: auto; display: block; }
.axis text { font-family: var(--mono); font-size: 11px; fill: var(--ink); } .axis .bar { fill: var(--open-bg); } .axis .ok { fill: var(--proved-bg); } .axis line { stroke: var(--ink-2); stroke-width: 1; } .axis .tick { stroke: var(--ink); }
.widget { display: grid; grid-template-columns: 300px 1fr; gap: 18px; margin: 16px 0 24px; max-width: 980px; }
.widget .controls { display: grid; gap: 8px; align-content: start; }
.widget .row { display: grid; grid-template-columns: 78px 1fr 46px; align-items: center; gap: 8px; font-size: 12.5px; }
.widget .row label { font-family: var(--mono); font-size: 11.5px; color: var(--ink-2); }
.widget .row output { font-family: var(--mono); font-size: 11.5px; text-align: right; font-variant-numeric: tabular-nums; }
.widget input[type=range] { width: 100%; accent-color: var(--fan); }
.widget .group { font-family: var(--mono); font-size: 11px; letter-spacing: 0.06em; text-transform: uppercase; color: var(--ink-3); margin-top: 6px; }
.widget select, .widget button { font: inherit; font-size: 13px; padding: 4px 8px; border: 1px solid var(--rule); border-radius: 4px; background: var(--panel); color: var(--ink); }
.widget .stage svg.net { width: 100%; height: auto; background: var(--panel); border: 1px solid var(--rule); border-radius: 4px; }
.widget .readout { display: flex; flex-wrap: wrap; gap: 6px 14px; font-family: var(--mono); font-size: 12px; margin: 8px 0; align-items: center; }
.widget .readout .k { color: var(--ink-3); }
.widget .warn { color: var(--open); font-weight: 600; }
.grid24 { display: grid; grid-template-columns: 70px repeat(4, 34px); gap: 3px; font-family: var(--mono); font-size: 11px; margin-top: 10px; align-items: center; }
.grid24 .cell { height: 26px; border-radius: 3px; border: 1px solid var(--rule); cursor: pointer; display: flex; align-items: center; justify-content: center; font-size: 10px; }
.grid24 .cell.ok { background: var(--proved-bg); } .grid24 .cell.bad { background: var(--open-bg); } .grid24 .cell.rule { outline: 2px solid var(--ink); }
.grid24 .h { color: var(--ink-3); text-align: center; }
@media (max-width: 820px) { .widget { grid-template-columns: 1fr; } }""")
s = s.replace("function figure(key, caption) { if (!FIGS[key]) return ''; return `<figure>${FIGS[key]}<figcaption>${caption}</figcaption></figure>`; }",
"""function figure(key, caption) { if (!FIGS[key]) return ''; return `<figure>${FIGS[key]}<figcaption>${caption}</figcaption></figure>`; }
const NODEFIG = {
  root: ['net_typical', 'The kind of object the whole page is about: a net of an octahedron, the hard case. Fan faces blue, petals orange.'],
  lemmaA: ['lemmaA', 'Lemma A on a pentagonal pyramid: the five edges at the apex v are cut, the base stays whole and the triangles open like petals.'],
  n4: ['n4', 'A tetrahedron cut at one vertex v.'],
  n5: ['n5_pyr', 'The square pyramid cut at its apex.'], n5b: ['n5_bipyr', 'The triangular bipyramid cut at an equatorial vertex v of degree 4.'],
  t_pyr5: ['t_pyr5', 'Pentagonal pyramid, Lemma A at the apex.'],
  t_simp55: ['t_simp55', 'Simplicial type 5·5·4·4·3·3 cut at a degree-5 vertex v: the opposite face stays in the middle.'],
  t_54: ['t_54', 'The type with one quadrilateral (blue) cut at its degree-5 vertex.'],
  t_prism: ['t_prism', 'The prism unfolded as a strip of three quadrilaterals with the two triangles on the middle one.'],
  t_prismd: ['t_prismd', 'A prism with one diagonal, unfolded with a cut tree containing the star of a degree-4 vertex.'],
  t_octa_minus: ['t_octa_minus', 'Octahedron minus an edge: the quadrilateral (blue) is the merged pair V₀ ∪ W₀; the tree is the octahedron tree, star(v) plus one edge at w.'],
  octa_shared: ['octa_shared', 'The four faces outlined in red all contain the same copy of u₂ and occupy disjoint wedges there.'],
  lemmaL: ['lemmaL', 'The local pairs at the slit: the two petals outlined in red and the two fan faces dashed, either side of the gap at w.'],
  lemmaF: ['lemmaF', 'The far pairs: the two opposite-petal pairs (red and purple outlines) and the four petal-versus-far-fan pairs (dashed fan faces).'],
  F_hinge: ['F_hinge', 'An interior hinge w u₂ and its two fan faces (dashed): no petal can cross it, since every petal shares a vertex with one of them.'],
  F_triple: ['F_triple', 'A triple: outer petals in red, middle petal in purple. The Triple Lemma says the two red petals are disjoint.'],
  F_nocross: ['overlap_above', 'Even in this overlapping example the two dashed cut edges do not cross each other; their lines only meet beyond the endpoints, at p*.'],
  F_rot: ['F_rot', 'Dashed outlines: the outer petals in the flat development around v (no gaps). Filled: their net positions, rotated about u and u′ by the gaps. The composition is the rotation about c*.'],
  F_angular: ['F_rot', 'Angles are measured around c*; the rotation adds κ to every angle, moving points across M from u′’s side to u’s side.'],
  F_notboth: ['F_rot', 'Both outer petals would have to wrap past the ray of M beyond v, which needs the three face angles at v to exceed 2π.'],
  F_side: ['overlap_above', 'How the open step fails without (H): here ν_i + ν_j > π and the petal V_i crosses M through its wedge at v (mechanism 1).'],
  octa_false: ['octa_false', 'A fixed labelled tree fails: this net uses the same polytope as the typical net with a different apex, and overlaps (red).'],
  evidence: ['evidence', 'Closest approach found by adversarial search under (H) with non-degeneracy guards (separation 0.4% of the diameter, no overlap).'],
  n7: ['n7', 'Seven vertices: a hexagonal pyramid, settled by Lemma A; the simplicial types need Lemma F and Lemma L.'],
};""")
s = s.replace("  if (n.figure) h += figure(n.figure, CAPTIONS[n.figure](FIGS[n.figure + '_meta']));",
"""  if (n.figure) h += figure(n.figure, CAPTIONS[n.figure](FIGS[n.figure + '_meta']));
  else if (NODEFIG[n.id]) h += figure(NODEFIG[n.id][0], NODEFIG[n.id][1]);
  if (n.id === 'n5') h += figure(NODEFIG.n5b[0], NODEFIG.n5b[1]);
  if (n.id === 'F_sharp') h += sharpAxis();
  if (n.id === 'play') h += widgetShell();""")
engine = open('notes/widget.js').read()
s = s.replace("let showAll = false;", engine + "\nlet showAll = false;")
s = s.replace("  document.querySelectorAll('nav button.node').forEach(b => b.setAttribute('aria-current', b.dataset.id === n.id ? 'true' : 'false'));",
"""  document.querySelectorAll('nav button.node').forEach(b => b.setAttribute('aria-current', b.dataset.id === n.id ? 'true' : 'false'));
  if (document.getElementById('wg')) initWidget();""")
s = s.replace("{ id: 'octa_false', parent: 't_octa',", """{ id: 'play', parent: 't_octa', title: 'Play: shape an octahedron and watch the net', status: 'info', summary: 'Move the six vertices, see the curvatures, the chosen apex and slit, and every net Z_k with its overlaps.',
  body: `<p>The six vertices are given in cylindrical coordinates about the axis through <i>v</i> and <i>w</i>. The rule picks the sharpest vertex as apex and the sharpest neighbour of its antipode as the slit; you can override both. The grid shows all 24 nets (six apexes × four slits): green is simple, red overlaps, the outlined cell is the rule's choice. Presets include the real polytopes behind the figures on this page, including two that overlap when the hypothesis fails.</p>` },
{ id: 'octa_false', parent: 't_octa',""")
open('notes/status_template.html','w').write(s)
print("patched", len(s))
