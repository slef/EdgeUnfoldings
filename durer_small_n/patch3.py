import re
s = open('notes/status_template.html').read()
# fonts + CSS
s = s.replace("family=IBM+Plex+Mono:wght@400;500&display=swap", "family=IBM+Plex+Mono:wght@400;500&family=STIX+Two+Text:ital,wght@0,400;0,600;1,400&display=swap")
s = s.replace(".statement { border: 1px solid var(--rule); border-left: 4px solid var(--fan); background: var(--panel); padding: 10px 14px; margin: 0 0 16px; border-radius: 0 6px 6px 0; max-width: 66ch; }\n.statement .statement-title { font-family: var(--mono); font-size: 11.5px; letter-spacing: 0.06em; text-transform: uppercase; color: var(--fan); display: block; margin-bottom: 4px; }",
""".thm { font-family: "STIX Two Text", "Times New Roman", Times, serif; font-size: 16.5px; line-height: 1.5; margin: 0 0 18px; max-width: 68ch; padding: 10px 14px 10px 16px; border-left: 3px solid var(--fan); background: var(--bg-2); border-radius: 0 4px 4px 0; }
.thm .thm-head { font-weight: 600; font-style: normal; }
.thm .thm-body { font-style: italic; } .thm .thm-body i { font-style: normal; } .thm.def .thm-body { font-style: normal; } .thm.def .thm-body i { font-style: italic; }
.thm .thm-body sup, .thm .thm-body sub { font-style: normal; }
.thm.def { border-left-color: var(--petal); background: transparent; padding-left: 14px; margin-bottom: 14px; }
.thm.def .thm-head { color: var(--ink); }
.thm.open { border-left-color: var(--open); } .thm.conj { border-left-color: var(--numeric); }""")
# --- statements: strip old prefixes, add kind/name
KIND = {
 'lemmaA': ('lemma', 'A', None), 'octa_shared': ('lemma', None, 'shared vertex'), 'F_hinge': ('lemma', None, 'hinges'), 'F_D': ('lemma', None, 'the wedge D'),
 'F_nocross': ('lemma', None, 'cut edges do not cross'), 'F_rot': ('lemma', None, 'rotation picture'), 'F_angular': ('lemma', None, 'angular criterion'),
 'F_notboth': ('lemma', None, 'at most one crossing'), 'F_sharp': ('lemma', None, 'sharpness of v'),
 'lemmaF': ('conj', None, 'Lemma F'), 'lemmaL': ('conj', None, 'Lemma L'), 'F_triple': ('conj', None, 'Triple Lemma'),
 'F_side': ('open', None, 'side conditions'), 'F_below': ('open', None, 'below the base'),
 't_prismd': ('red', None, 'prism with one diagonal'), 't_octa_minus': ('red', None, 'octahedron minus an edge'), 't_octa': ('thm', None, 'octahedron'), 'F_above': ('case', None, 'A'),
}
prefixes = ["Lemma (shared vertex). ", "Lemma L (conjectured). ", "Lemma F (conjectured). ", "Triple Lemma (conjectured). ", "Lemma (D). ", "Lemma. ", "Claim (open). ", "Reduction. ", "To prove. "]
for k, (kind, name, title) in KIND.items():
    m = re.search(r"\{ id: '%s', statement: `(.*?)`, parent:" % k, s, re.S); assert m, k
    body = m.group(1)
    for p in prefixes:
        if body.startswith(p): body = body[len(p):]
    if k == 'F_above': body = body.replace("Case A: ", "")
    s = s.replace(m.group(0), "{ id: '%s', kind: '%s', kname: %s, ktitle: %s, statement: `%s`, parent:" % (k, kind, repr(name) if name else 'null', repr(title) if title else 'null', body))
# --- definitions page as numbered definitions
a = s.index("{ id: 'defs', parent: 'root',"); b = s.index("{ id: 'lemmaA',")
DEFS_JS = r"""{ id: 'defs', parent: 'root', title: 'Definitions and notation', status: 'info', summary: 'Everything the other pages assume. Underlined terms anywhere on the site show these definitions on hover and link here.', defs: true, body: `` },
"""
s = s[:a] + DEFS_JS + s[b:]
DEFS_DATA = r"""
const DEFS = [
  ['defs-net', 'Net', `An <b>edge unfolding</b> cuts a polytope along a set of edges forming a spanning tree of its vertices (the <b>cut tree</b>) and flattens the surface; the uncut edges (<b>hinges</b>) form a spanning tree of the dual graph. Each cut edge has two copies in the unfolding, of equal length. Two faces <b>overlap</b> if their interiors meet; touching along edges or at vertices is allowed. A <b>net</b> is an unfolding without overlap.`],
  ['defs-kappa', 'Curvature and gaps', `κ<sub>x</sub> = 2π − (sum of the face angles at the vertex <i>x</i>), the angle deficit. For a convex polytope 0 &lt; κ<sub>x</sub> &lt; 2π at every vertex and Σ<sub>x</sub> κ<sub>x</sub> = 4π (six vertices: average 2π/3). In an unfolding the faces around a copy of <i>x</i> are laid out consecutively and the remaining angular <b>gap</b> equals κ<sub>x</sub>; the two copies of a cut edge at <i>x</i> bound that gap. The <b>sharpest</b> vertex is the one of largest curvature.`],
  ['defs-cone', 'Cone inequality', `At a vertex of a convex polytope each face angle is at most the sum of the other face angles at that vertex (the triangle inequality for the spherical polygon cut out by the tangent cone). Consequence: a face angle ν<sub>j</sub> at <i>v</i> satisfies ν<sub>j</sub> ≤ (2π − κ<sub>v</sub>)/2.`],
  ['defs-octa', 'Octahedron notation', `<i>v</i>, <i>w</i> is a pair of non-adjacent (antipodal) vertices and <i>u</i><sub>0</sub>, …, <i>u</i><sub>3</sub> the equator, the four neighbours of <i>w</i> in cyclic order (indices mod 4). Faces: <i>W<sub>i</sub></i> = <i>w u<sub>i</sub> u<sub>i+1</sub></i> (fan faces, blue) and <i>V<sub>i</sub></i> = <i>v u<sub>i</sub> u<sub>i+1</sub></i> (petals, orange); <i>Q<sub>i</sub></i> = <i>W<sub>i</sub></i> ∪ <i>V<sub>i</sub></i>. Angles: ω<sub>i</sub> of <i>W<sub>i</sub></i> at <i>w</i>, ν<sub>i</sub> of <i>V<sub>i</sub></i> at <i>v</i>. Lengths: <i>r<sub>i</sub></i> = |<i>w u<sub>i</sub></i>|, <i>s<sub>i</sub></i> = |<i>v u<sub>i</sub></i>|, ℓ<sub>i</sub> = |<i>u<sub>i</sub> u<sub>i+1</sub></i>|.`],
  ['defs-Zk', 'The net Z<sub>k</sub>', `The unfolding with cut tree star(<i>v</i>) ∪ {<i>w u<sub>k</sub></i>}: the four fan faces form a fan around <i>w</i> opened along the <b>slit</b> <i>w u<sub>k</sub></i> with gap κ<sub>w</sub> (the two copies of <i>u<sub>k</sub></i> are written <i>u<sub>k</sub></i> and <i>u<sub>k</sub></i>′), and each petal hangs from its fan face along the equator edge. Faces are named relative to the slit: <i>W<sub>k</sub></i>, <i>W<sub>k+1</sub></i>, <i>W<sub>k+2</sub></i>, <i>W<sub>k−1</sub></i>′ and their petals. The <b>local pairs</b> are the three pairs across the gap at <i>w</i> that share no net vertex; the <b>far pairs</b> are the two opposite-petal pairs (<i>V<sub>k</sub></i>, <i>V<sub>k+2</sub></i>), (<i>V<sub>k+1</sub></i>, <i>V<sub>k−1</sub></i>′) and the four petal-versus-far-fan pairs.`],
  ['defs-triple', 'Triple notation', `For three consecutive fan faces <i>W<sub>i</sub></i>, <i>W<sub>j</sub></i>, <i>W<sub>j+1</sub></i> (<i>j</i> = <i>i</i>+1) the middle petal <i>V<sub>j</sub></i> has base <i>u</i> = <i>u<sub>j</sub></i>, <i>u</i>′ = <i>u<sub>j+1</sub></i>, base angles φ at <i>u</i>, ψ at <i>u</i>′, apex angle ν<sub>j</sub>, and κ = κ<sub>u</sub> + κ<sub>u′</sub>. <i>v<sub>i</sub></i>, <i>v<sub>j</sub></i>, <i>v<sub>j+1</sub></i> are the copies of <i>v</i> in the three petals; <i>u v<sub>i</sub></i> and <i>u</i>′<i>v<sub>j+1</sub></i> are the cut edges of the outer petals. “Above the base” means on <i>v<sub>j</sub></i>’s side of the line <i>u u</i>′.`],
  ['defs-H', 'Hypothesis (H)', `<i>v</i> is the sharpest of all six vertices: κ<sub>v</sub> ≥ κ<sub>x</sub> for every vertex <i>x</i>. Consequences: κ<sub>v</sub> ≥ 2π/3; Σ<sub>i</sub> ν<sub>i</sub> = 2π − κ<sub>v</sub> ≤ 4π/3; each ν<sub>j</sub> ≤ π − κ<sub>v</sub>/2 ≤ 2π/3 by the cone inequality; every gap κ<sub>u</sub> ≤ κ<sub>v</sub>. The weaker hypothesis “κ<sub>v</sub> ≥ κ<sub>u</sub> for the four equator vertices only” is numerically also overlap-free but does not support the rotation argument, which uses κ<sub>w</sub> ≤ κ<sub>v</sub>.`],
  ['defs-rule', 'The rule', `Apex <i>v</i> = the vertex of largest curvature; <i>w</i> = its antipode; slit <i>k</i> = the neighbour of <i>w</i> of largest curvature. The rule makes (H) hold for the chosen apex. Two other slit choices also work numerically: the neighbour farthest from <i>v</i>, and the longest edge at <i>w</i>.`],
  ['defs-thickness', 'Thickness', `Smallest extent of the polytope divided by its diameter, computed as the ratio of the smallest to the largest singular value of the centred vertex matrix. A doubly covered polygon has thickness 0. Used only to describe examples; no lemma depends on it.`],
  ['defs-guards', 'Degeneracy guards', `Adversarial searches restrict to polytopes with every edge at least 5% of the diameter and every curvature at least 0.05, because without guards the searches converge to a collapsed edge or a flat vertex, where faces touch legitimately.`],
];
const KINDS = { lemma: ['Lemma', ''], conj: ['Conjecture', 'conj'], open: ['Open problem', 'open'], red: ['Reduction', ''], thm: ['Theorem to prove', ''], case: ['Case', ''] };
const NUM = {}; NODES.forEach(n => { if (n.kind && !n.kname && n.kind !== 'case' && n.kind !== 'thm') { NUM[n.id] = (NUM['_' + n.kind] = (NUM['_' + n.kind] || 0) + 1); } });
function thmHead(n) { const [word, cls] = KINDS[n.kind]; const num = n.kname ? ' ' + n.kname : (NUM[n.id] ? ' ' + NUM[n.id] : ''); const title = n.kind === 'case' ? ' ' + n.ktitle : (n.ktitle && !n.kname ? ' (' + n.ktitle + ')' : ''); return [`${word}${num}${title}.`, cls]; }
function thmBox(n) { const [head, cls] = thmHead(n); return `<div class="thm ${cls}"><span class="thm-head">${head}</span> <span class="thm-body">${n.statement}</span></div>`; }
function defsBlock() { return DEFS.map(([id, name, text], i) => `<div class="thm def" id="${id}"><span class="thm-head">Definition ${i + 1} (${name}).</span> <span class="thm-body">${text}</span></div>`).join(''); }
"""
s = s.replace("const byId = Object.fromEntries(NODES.map(n => [n.id, n]));", DEFS_DATA + "\nconst byId = Object.fromEntries(NODES.map(n => [n.id, n]));")
s = s.replace("  if (n.statement) h += `<div class=\"statement\"><span class=\"statement-title\">Statement</span>${n.statement}</div>`;", "  if (n.statement) h += thmBox(n);\n  if (n.defs) h += defsBlock();")
# --- no self-links: pass the node id to linkTerms
s = s.replace("  linkTerms(d);", "  linkTerms(d, showAll ? null : n.id);")
open('notes/status_template.html', 'w').write(s)
g = open('notes/glossary.js').read()
g = g.replace("function linkTerms(root) {\n  const counts = {}; const keys = Object.keys(GLOSS);",
"""function linkTerms(root, selfId) {
  const counts = {}; const keys = Object.keys(GLOSS).filter(k => { const l = GLOSS[k].link; if (!selfId) return true; if (l === '#' + selfId) return false; if (selfId === 'defs' && l.startsWith('#defs-')) return false; return true; });""")
g = g.replace("if (SKIP.has(p.tagName) || (p.classList && (p.classList.contains('term') || p.classList.contains('chip') || p.classList.contains('crumbs') || p.classList.contains('statement-title')))) return NodeFilter.FILTER_REJECT;",
"if (SKIP.has(p.tagName) || (p.classList && (p.classList.contains('term') || p.classList.contains('chip') || p.classList.contains('crumbs') || p.classList.contains('thm-head')))) return NodeFilter.FILTER_REJECT;")
# in one-page mode: skip self-links per article by checking the enclosing article id
g = g.replace("  for (const node of nodes) {\n    const text = node.nodeValue; const hits = [];\n    for (const key of keys) { const g = GLOSS[key];",
"""  for (const node of nodes) {
    const text = node.nodeValue; const hits = []; const art = node.parentNode && node.parentNode.closest ? node.parentNode.closest('article') : null; const artId = art ? art.id.slice(2) : null;
    for (const key of keys) { const g = GLOSS[key]; if (artId && (g.link === '#' + artId || (artId === 'defs' && g.link.startsWith('#defs-')))) continue;""")
# glossary links for the octahedron/Zk terms now point to the definition entries
g = g.replace("link: '#defs-octa', short: 'The unfolding whose cut tree", "link: '#defs-Zk', short: 'The unfolding whose cut tree").replace("slit: { label: 'Slit', re: /\\bslit\\b/g, link: '#defs-octa'", "slit: { label: 'Slit', re: /\\bslit\\b/g, link: '#defs-Zk'").replace("nearness: { label: 'Far and local pairs', re: /\\bfar pairs?\\b|\\blocal pairs?\\b/g, link: '#t_octa'", "nearness: { label: 'Far and local pairs', re: /\\bfar pairs?\\b|\\blocal pairs?\\b/g, link: '#defs-Zk'")
open('notes/glossary.js', 'w').write(g)
print('ok')
