import re
s = open('notes/status_template.html').read()
# ---- CSS
s = s.replace(".types { display: grid;", """a.term { color: inherit; text-decoration: underline dotted; text-decoration-color: var(--fan); text-decoration-thickness: 1.5px; text-underline-offset: 3px; cursor: help; }
a.term:hover { text-decoration-style: solid; }
#tip { position: absolute; z-index: 50; background: var(--panel); color: var(--ink); border: 1px solid var(--rule); box-shadow: 0 8px 28px rgba(0,0,0,0.14); border-radius: 6px; padding: 10px 12px; font-size: 13px; line-height: 1.45; display: none; }
#tip .tl { font-weight: 600; margin-bottom: 4px; } #tip .td { color: var(--ink-2); } #tip a { display: inline-block; margin-top: 7px; font-size: 12.5px; }
.statement { border: 1px solid var(--rule); border-left: 4px solid var(--fan); background: var(--panel); padding: 10px 14px; margin: 0 0 16px; border-radius: 0 6px 6px 0; max-width: 66ch; }
.statement .statement-title { font-family: var(--mono); font-size: 11.5px; letter-spacing: 0.06em; text-transform: uppercase; color: var(--fan); display: block; margin-bottom: 4px; }
dl.defs { max-width: 66ch; } dl.defs dt { font-weight: 600; margin-top: 14px; scroll-margin-top: 12px; } dl.defs dd { margin: 4px 0 0; }
.types { display: grid;""")
s = s.replace(".widget { display: grid; grid-template-columns: 300px 1fr;", ".widget { display: grid; grid-template-columns: 300px minmax(0, 1fr);")
# ---- glossary script placeholder before widget js
s = s.replace("__WIDGET_JS__", "__GLOSS_JS__\n__WIDGET_JS__")
# ---- statements
ST = {
 'lemmaA': "Let <i>P</i> be a convex polytope and <i>v</i> a vertex adjacent to every other vertex. Cutting exactly the edges at <i>v</i> gives a net.",
 't_prismd': "Reduction. If every realization of the simplicial type 5·5·4·4·3·3 has a net whose cut tree contains the star of a degree-4 vertex, then every prism with one diagonal has a net.",
 't_octa_minus': "Reduction. If every octahedron has a net of the form <i>Z<sub>k</sub></i> (the star of an apex plus one edge at the antipode), then every octahedron minus an edge has a net.",
 't_octa': "To prove. Every octahedron-type polytope has a net; the candidate is <i>Z<sub>k</sub></i> with <i>v</i> the sharpest vertex and <i>k</i> the sharpest neighbour of <i>w</i>. This follows from the shared-vertex lemma, Lemma F and Lemma L.",
 'octa_shared': "Lemma (shared vertex). In any net, two faces that contain the same copy of a vertex lie in disjoint angular wedges at it and do not overlap.",
 'lemmaL': "Lemma L (conjectured). Let <i>v</i> be the sharpest vertex, <i>w</i> its antipode and <i>u<sub>k</sub></i> the sharpest neighbour of <i>w</i>. In <i>Z<sub>k</sub></i> the pairs <i>V<sub>k</sub></i>–<i>V<sub>k−1</sub></i>′, <i>V<sub>k</sub></i>–<i>W<sub>k−1</sub></i>′ and <i>V<sub>k−1</sub></i>′–<i>W<sub>k</sub></i> do not overlap.",
 'lemmaF': "Lemma F (conjectured). Assume (H). Then in every net <i>Z<sub>k</sub></i>, <i>k</i> = 0, …, 3, none of the six far pairs overlaps.",
 'F_hinge': "Lemma. In <i>Z<sub>k</sub></i> no petal meets the relative interior of a hinge segment <i>w u<sub>j</sub></i>, <i>j</i> ≠ <i>k</i>. Consequently, if a petal <i>V<sub>i</sub></i> overlaps a fan face <i>W<sub>j</sub></i> with <i>j</i> ∉ {<i>i</i>−1, <i>i</i>, <i>i</i>+1}, then <i>V<sub>i</sub></i> overlaps <i>V<sub>j</sub></i>.",
 'F_triple': "Triple Lemma (conjectured). Let <i>W<sub>i</sub></i>, <i>W<sub>j</sub></i>, <i>W<sub>j+1</sub></i> (<i>j</i> = <i>i</i>+1) be consecutive fan faces of a net and <i>V<sub>i</sub></i>, <i>V<sub>j</sub></i>, <i>V<sub>j+1</sub></i> their petals. Under (H), <i>V<sub>i</sub></i> and <i>V<sub>j+1</sub></i> do not overlap.",
 'F_D': "Lemma (D). Let <i>L</i>, <i>L</i>′ be the lines through the cut edges <i>u v<sub>i</sub></i> and <i>u</i>′<i>v<sub>j+1</sub></i>. Then <i>V<sub>i</sub></i> lies in the closed half-plane of <i>L</i> not containing <i>V<sub>j</sub></i>, <i>V<sub>j+1</sub></i> in the closed half-plane of <i>L</i>′ not containing <i>V<sub>j</sub></i>, so <i>V<sub>i</sub></i> ∩ <i>V<sub>j+1</sub></i> ⊂ D, the wedge at <i>L</i> ∩ <i>L</i>′ opposite the base. D lies on <i>v</i>’s side of the base iff κ<sub>u</sub> + κ<sub>u′</sub> &lt; ν<sub>j</sub>, on <i>w</i>’s side iff &gt;, and is empty if equal.",
 'F_nocross': "Lemma. The cut edges <i>u v<sub>i</sub></i> and <i>u</i>′<i>v<sub>j+1</sub></i> are disjoint segments.",
 'F_above': "Case A: κ<sub>u</sub> + κ<sub>u′</sub> &lt; ν<sub>j</sub>. To show under (H): <i>V<sub>i</sub></i> ∩ <i>V<sub>j+1</sub></i> = ∅.",
 'F_rot': "Lemma. Let <i>V<sub>i</sub></i><sup>flat</sup>, <i>V<sub>j+1</sub></i><sup>flat</sup> be the positions in the flat development around <i>v</i>, ρ<sub>u</sub> the rotation about <i>u</i> by κ<sub>u</sub> away from <i>V<sub>j</sub></i>, and ρ<sub>u′</sub> the rotation about <i>u</i>′ by κ<sub>u′</sub> in the same sense. Then <i>V<sub>i</sub></i> = ρ<sub>u</sub>(<i>V<sub>i</sub></i><sup>flat</sup>), <i>V<sub>j+1</sub></i> = ρ<sub>u′</sub><sup>−1</sup>(<i>V<sub>j+1</sub></i><sup>flat</sup>), and <i>R</i> = ρ<sub>u′</sub> ∘ ρ<sub>u</sub> is the rotation by κ = κ<sub>u</sub> + κ<sub>u′</sub> about <i>c</i>*. Hence <i>V<sub>i</sub></i> ∩ <i>V<sub>j+1</sub></i> ≠ ∅ iff <i>R</i>(<i>V<sub>i</sub></i><sup>flat</sup>) ∩ <i>V<sub>j+1</sub></i><sup>flat</sup> ≠ ∅.",
 'F_angular': "Lemma. Let ε<sub>i</sub>, ε<sub>j+1</sub> ≥ 0 be the largest angles, seen from <i>c</i>*, by which the above-base parts of <i>V<sub>i</sub></i><sup>flat</sup> and <i>V<sub>j+1</sub></i><sup>flat</sup> cross <i>M</i> towards the other petal. If κ &lt; ν<sub>j</sub> and ε<sub>i</sub> + ε<sub>j+1</sub> &lt; κ, then <i>V<sub>i</sub></i> ∩ <i>V<sub>j+1</sub></i> = ∅.",
 'F_notboth': "Lemma. Under (H) it is impossible that the wedges at <i>v</i> of both <i>V<sub>i</sub></i><sup>flat</sup> and <i>V<sub>j+1</sub></i><sup>flat</sup> reach the ray of <i>M</i> beyond <i>v</i>.",
 'F_sharp': "Lemma. Under (H), κ<sub>u</sub> + κ<sub>u′</sub> &lt; ν<sub>j</sub> implies κ<sub>v</sub> &gt; 6π/7; hence Σν &lt; 8π/7 and every face angle at <i>v</i> is below 4π/7.",
 'F_side': "Claim (open). Under (H) and κ &lt; ν<sub>j</sub>, the above-base part of <i>V<sub>i</sub></i><sup>flat</sup> lies on <i>u</i>’s side of <i>M</i> and that of <i>V<sub>j+1</sub></i><sup>flat</sup> on <i>u</i>′’s side, i.e. ε<sub>i</sub> = ε<sub>j+1</sub> = 0. With the lemmas above this closes Case A.",
 'F_below': "Claim (open). Case B: under (H) and κ<sub>u</sub> + κ<sub>u′</sub> ≥ ν<sub>j</sub>, <i>V<sub>i</sub></i> ∩ <i>V<sub>j+1</sub></i> = ∅.",
}
for k, v in ST.items():
    key = "{ id: '%s', parent:" % k
    assert key in s, k
    s = s.replace(key, "{ id: '%s', statement: `%s`, parent:" % (k, v), 1)
# ---- definitions node (second top-level node)
DEFS = r"""{ id: 'defs', parent: 'root', title: 'Definitions and notation', status: 'info', summary: 'Everything the other pages assume. Underlined terms anywhere on the site show these definitions on hover and link here.',
  body: `<dl class="defs">
  <dt id="defs-net">Net, cut tree, hinge, overlap</dt><dd>An <b>edge unfolding</b> cuts a polytope along a set of edges forming a spanning tree of its vertices (the <b>cut tree</b>) and flattens the surface; the uncut edges (<b>hinges</b>) form a spanning tree of the dual graph. Each cut edge has two copies in the unfolding, of equal length. Two faces <b>overlap</b> if their interiors meet; touching along edges or at vertices is allowed. A <b>net</b> is an unfolding without overlap. Every statement here is about simple nets in this sense, as in DiBiase.</dd>
  <dt id="defs-kappa">Curvature κ and gaps</dt><dd>κ<sub>x</sub> = 2π − (sum of the face angles at the vertex <i>x</i>), the angle deficit. For a convex polytope 0 &lt; κ<sub>x</sub> &lt; 2π at every vertex and Σ<sub>x</sub> κ<sub>x</sub> = 4π (six vertices: average 2π/3). In an unfolding, the faces around a copy of <i>x</i> are laid out consecutively and the remaining angular <b>gap</b> equals κ<sub>x</sub>; the two copies of a cut edge at <i>x</i> bound that gap. "Sharpest vertex" means largest curvature.</dd>
  <dt id="defs-cone">Cone inequality</dt><dd>At a vertex of a convex polytope each face angle is at most the sum of the other face angles at that vertex (the triangle inequality for the spherical polygon cut out by the tangent cone). Consequence used throughout: a face angle at <i>v</i> is at most half of their sum, ν<sub>j</sub> ≤ (2π − κ<sub>v</sub>)/2.</dd>
  <dt id="defs-octa">Octahedron notation</dt><dd><i>v</i>, <i>w</i>: a pair of non-adjacent (antipodal) vertices. <i>u</i><sub>0</sub>, …, <i>u</i><sub>3</sub>: the equator, the four neighbours of <i>w</i> in cyclic order (indices mod 4). Faces <i>W<sub>i</sub></i> = <i>w u<sub>i</sub> u<sub>i+1</sub></i> (fan faces, blue) and <i>V<sub>i</sub></i> = <i>v u<sub>i</sub> u<sub>i+1</sub></i> (petals, orange); <i>Q<sub>i</sub></i> = <i>W<sub>i</sub></i> ∪ <i>V<sub>i</sub></i>. Angles: ω<sub>i</sub> of <i>W<sub>i</sub></i> at <i>w</i>, ν<sub>i</sub> of <i>V<sub>i</sub></i> at <i>v</i>. Lengths: <i>r<sub>i</sub></i> = |<i>w u<sub>i</sub></i>|, <i>s<sub>i</sub></i> = |<i>v u<sub>i</sub></i>|, ℓ<sub>i</sub> = |<i>u<sub>i</sub> u<sub>i+1</sub></i>|. The net <i>Z<sub>k</sub></i> has cut tree star(<i>v</i>) ∪ {<i>w u<sub>k</sub></i>}: the four fan faces form a fan around <i>w</i> opened along the <b>slit</b> <i>w u<sub>k</sub></i> with gap κ<sub>w</sub> (the two copies of <i>u<sub>k</sub></i> are written <i>u<sub>k</sub></i> and <i>u<sub>k</sub></i>′), and each petal hangs from its fan face along the equator edge. Faces of <i>Z<sub>k</sub></i> are named relative to the slit: <i>W<sub>k</sub></i>, <i>W<sub>k+1</sub></i>, <i>W<sub>k+2</sub></i>, <i>W<sub>k−1</sub></i>′ and their petals. <b>Local pairs</b>: the three pairs across the gap at <i>w</i> sharing no net vertex. <b>Far pairs</b>: the two opposite-petal pairs (<i>V<sub>k</sub></i>, <i>V<sub>k+2</sub></i>), (<i>V<sub>k+1</sub></i>, <i>V<sub>k−1</sub></i>′) and the four petal-versus-far-fan pairs.</dd>
  <dt>Triple notation</dt><dd>For three consecutive fan faces <i>W<sub>i</sub></i>, <i>W<sub>j</sub></i>, <i>W<sub>j+1</sub></i> (<i>j</i> = <i>i</i>+1): the middle petal <i>V<sub>j</sub></i> has base <i>u</i> = <i>u<sub>j</sub></i>, <i>u</i>′ = <i>u<sub>j+1</sub></i>, base angles φ at <i>u</i>, ψ at <i>u</i>′, apex angle ν<sub>j</sub>; κ = κ<sub>u</sub> + κ<sub>u′</sub>. <i>v<sub>i</sub></i>, <i>v<sub>j</sub></i>, <i>v<sub>j+1</sub></i> are the copies of <i>v</i> in the three petals; <i>u v<sub>i</sub></i> and <i>u</i>′<i>v<sub>j+1</sub></i> are the cut edges of the outer petals. "Above the base" means on <i>v<sub>j</sub></i>’s side of the line <i>u u</i>′.</dd>
  <dt id="defs-H">Hypothesis (H)</dt><dd><i>v</i> is the sharpest of all six vertices: κ<sub>v</sub> ≥ κ<sub>x</sub> for every vertex <i>x</i>. Consequences: κ<sub>v</sub> ≥ 2π/3; Σ<sub>i</sub> ν<sub>i</sub> = 2π − κ<sub>v</sub> ≤ 4π/3; each ν<sub>j</sub> ≤ π − κ<sub>v</sub>/2 ≤ 2π/3 (cone inequality); every gap κ<sub>u</sub> ≤ κ<sub>v</sub>. The weaker hypothesis "κ<sub>v</sub> ≥ κ<sub>u</sub> for the four equator vertices only" is numerically also overlap-free but does not support the rotation argument; the bound κ<sub>w</sub> ≤ κ<sub>v</sub> is used.</dd>
  <dt id="defs-rule">The rule</dt><dd>Apex <i>v</i> = the vertex of largest curvature; <i>w</i> = its antipode; slit <i>k</i> = the neighbour of <i>w</i> of largest curvature. The rule makes (H) hold for the chosen apex. Two other slit choices also work numerically: the neighbour farthest from <i>v</i>, and the longest edge at <i>w</i>.</dd>
  <dt id="defs-thickness">Thickness</dt><dd>Smallest extent of the polytope divided by its diameter, computed as the ratio of the smallest to the largest singular value of the centred vertex matrix. A doubly covered polygon has thickness 0. Used only to describe examples; no lemma depends on it.</dd>
  <dt>Degeneracy guards</dt><dd>Adversarial searches restrict to polytopes with every edge at least 5% of the diameter and every curvature at least 0.05, because without guards the searches converge to a collapsed edge or a flat vertex, where faces touch legitimately.</dd>
  </dl>` },
"""
s = s.replace("{ id: 'lemmaA', parent: 'root',", DEFS + "{ id: 'lemmaA', parent: 'root',", 1)
# ---- render statement box; link terms; anchor routing
s = s.replace("  let h = `<article id=\"a-${n.id}\"><div class=\"crumbs\">${crumbs(n)}</div><div class=\"head\"><h2>${n.title}</h2><span class=\"chip ${n.status}\">${S[n.status]}</span></div><p class=\"summary\">${n.summary}</p>`;",
"  let h = `<article id=\"a-${n.id}\"><div class=\"crumbs\">${crumbs(n)}</div><div class=\"head\"><h2>${n.title}</h2><span class=\"chip ${n.status}\">${S[n.status]}</span></div><p class=\"summary\">${n.summary}</p>`;\n  if (n.statement) h += `<div class=\"statement\"><span class=\"statement-title\">Statement</span>${n.statement}</div>`;")
s = s.replace("  const id = (location.hash || '#root').slice(1); const n = byId[id] || byId.root;",
"  let id = (location.hash || '#root').slice(1); let anchor = null; if (!byId[id] && id.startsWith('defs-')) { anchor = id; id = 'defs'; } const n = byId[id] || byId.root;")
s = s.replace("  mountViewers();\n  if (document.getElementById('wg')) initWidget();",
"  linkTerms(d);\n  mountViewers();\n  if (document.getElementById('wg')) initWidget();\n  if (anchor) { const el = document.getElementById(anchor); if (el) el.scrollIntoView(); }")
open('notes/status_template.html', 'w').write(s)

# ---- widget.js: viewer reads the model on every draw; 3D panel moves into the controls column
w = open('notes/widget.js').read()
a = w.index("function viewer3d(el, model, opts) {"); b = w.index("function mountViewers(root)")
w = w[:a] + r"""function viewer3d(el, model, opts) {
  opts = opts || {}; const W = opts.size || 300, H = W;
  const st = { yaw: opts.yaw ?? 0.7, pitch: opts.pitch ?? -0.55 };
  function draw() {
    const P = model.P, names = model.names || {};
    const c0 = [0, 1, 2].map(k => P.reduce((s, p) => s + p[k], 0) / P.length);
    const faces = model.faces.map(f => { const a = P[f[0]], b = P[f[1]], d = P[f[2]]; const n = cross(sub(b, a), sub(d, a)); return dot(n, sub(c0, a)) > 0 ? [...f].reverse() : [...f]; });
    const cutSet = new Set((model.cut || []).map(e => e[0] < e[1] ? e[0] + '-' + e[1] : e[1] + '-' + e[0]));
    const R = Math.max(...P.map(p => Math.hypot(p[0] - c0[0], p[1] - c0[1], p[2] - c0[2]))) || 1;
    const edges = {}; faces.forEach((f, fi) => f.forEach((a, t) => { const b = f[(t + 1) % f.length]; const key = a < b ? a + '-' + b : b + '-' + a; (edges[key] = edges[key] || { a, b, faces: [] }).faces.push(fi); }));
    const rot = p => { const x = (p[0] - c0[0]) / R, y = (p[1] - c0[1]) / R, z = (p[2] - c0[2]) / R;
      const cy = Math.cos(st.yaw), sy = Math.sin(st.yaw); const x1 = cy * x - sy * y, y1 = sy * x + cy * y;
      const cp = Math.cos(st.pitch), sp = Math.sin(st.pitch); const y2 = cp * y1 - sp * z, z2 = sp * y1 + cp * z; return [x1, y2, z2]; };
    const Q = P.map(rot); const s = W * 0.38; const X = q => [W / 2 + q[0] * s, H / 2 - q[2] * s];
    const front = faces.map(f => { const a = Q[f[0]], b = Q[f[1]], d = Q[f[2]]; const n = [(b[1]-a[1])*(d[2]-a[2])-(b[2]-a[2])*(d[1]-a[1]), (b[2]-a[2])*(d[0]-a[0])-(b[0]-a[0])*(d[2]-a[2]), (b[0]-a[0])*(d[1]-a[1])-(b[1]-a[1])*(d[0]-a[0])]; return n[1] < 0; });
    let svg = `<svg viewBox="0 0 ${W} ${H}" xmlns="http://www.w3.org/2000/svg" class="v3d">`;
    const ed = Object.values(edges); const ck = e => cutSet.has(e.a < e.b ? e.a + '-' + e.b : e.b + '-' + e.a) ? 'cut' : '';
    for (const e of ed) { if (e.faces.some(fi => front[fi])) continue; const [x1, y1] = X(Q[e.a]), [x2, y2] = X(Q[e.b]); svg += `<line class="hid ${ck(e)}" x1="${x1.toFixed(1)}" y1="${y1.toFixed(1)}" x2="${x2.toFixed(1)}" y2="${y2.toFixed(1)}"/>`; }
    faces.forEach((f, fi) => { if (!front[fi]) return; svg += `<polygon class="${f.length === 3 ? 'tri' : 'quad'}" points="${f.map(i => X(Q[i]).map(v => v.toFixed(1)).join(',')).join(' ')}"/>`; });
    for (const e of ed) { if (!e.faces.some(fi => front[fi])) continue; const [x1, y1] = X(Q[e.a]), [x2, y2] = X(Q[e.b]); svg += `<line class="vis ${ck(e)}" x1="${x1.toFixed(1)}" y1="${y1.toFixed(1)}" x2="${x2.toFixed(1)}" y2="${y2.toFixed(1)}"/>`; }
    P.forEach((p, i) => { const [x, y] = X(Q[i]); const onFront = faces.some((f, fi) => front[fi] && f.includes(i)); svg += `<circle class="${onFront ? 'vtx' : 'vtx hid'}" cx="${x.toFixed(1)}" cy="${y.toFixed(1)}" r="2.6"/><text class="${onFront ? '' : 'hid'}" x="${(x + 4).toFixed(1)}" y="${(y - 4).toFixed(1)}">${names[i] ?? i}</text>`; });
    el.innerHTML = svg + `</svg>`;
  }
  let drag = null;
  el.addEventListener('pointerdown', e => { drag = [e.clientX, e.clientY, st.yaw, st.pitch]; el.setPointerCapture(e.pointerId); });
  el.addEventListener('pointermove', e => { if (!drag) return; st.yaw = drag[2] + (e.clientX - drag[0]) * 0.012; st.pitch = Math.max(-1.55, Math.min(1.55, drag[3] + (e.clientY - drag[1]) * 0.012)); draw(); });
  el.addEventListener('pointerup', () => { drag = null; }); el.addEventListener('pointercancel', () => { drag = null; });
  el.style.touchAction = 'none'; el.style.cursor = 'grab';
  draw(); return { draw, set(m) { model = m; draw(); } };
}
""" + w[b:]
w = w.replace("""</div><div class="stage"><div class="figrow"><div id="wg-svg"></div><div><div class="viewer" id="wg-3d"></div><div class="vcap">Drag to rotate. Red: the cut tree, star(v) plus one edge at w.</div></div></div><div class="readout" id="wg-read"></div>""",
"""<div class="viewer" id="wg-3d"></div><div class="vcap">Drag to rotate. Red: the cut tree, star(v) plus one edge at w.</div>
    </div><div class="stage"><div id="wg-svg"></div><div class="readout" id="wg-read"></div>""")
assert 'id="wg-3d"' in w
open('notes/widget.js', 'w').write(w)
b2 = open('build_status.py').read()
b2 = b2.replace(".replace('__WIDGET_JS__', open('notes/widget.js').read())", ".replace('__GLOSS_JS__', open('notes/glossary.js').read()).replace('__WIDGET_JS__', open('notes/widget.js').read())")
open('build_status.py', 'w').write(b2)
print('ok')
