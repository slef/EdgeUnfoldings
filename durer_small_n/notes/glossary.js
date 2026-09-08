// ---------- glossary: hover bubbles and jump links --------------------------------------------------------------
// Each entry: label, regex matched in running text, short definition (HTML), target hash, and how many occurrences
// per case to link (Infinity = all).
const GLOSS = {
  H: { label: 'Hypothesis (H)', re: /hypothesis \(H\)|\(H\)/g, all: true, link: '#defs-H',
    short: '<i>v</i> is the sharpest of all six vertices: κ<sub>v</sub> ≥ κ<sub>x</sub> for every vertex <i>x</i>. Consequences: κ<sub>v</sub> ≥ 2π/3, Σν ≤ 4π/3, and every face angle ν<sub>j</sub> at <i>v</i> is at most π − κ<sub>v</sub>/2.' },
  net: { label: 'Net', re: /\bnets?\b/g, link: '#defs-net', short: 'An edge unfolding of the polytope (cut along a spanning tree of edges, flatten) whose faces do not overlap. Touching along edges or at vertices counts as non-overlapping.' },
  curvature: { label: 'Curvature κ', re: /\bcurvatures?\b|\bκ\b/g, link: '#defs-kappa', short: 'κ<sub>x</sub> = 2π minus the sum of the face angles at the vertex <i>x</i> (the angle deficit). Positive at every vertex of a convex polytope; Σκ = 4π. In a net, the angular gap at a copy of <i>x</i> equals κ<sub>x</sub>.' },
  petal: { label: 'Petal V<sub>i</sub>', re: /\bpetals?\b/g, link: '#defs-octa', short: 'The face <i>V<sub>i</sub></i> = <i>v u<sub>i</sub> u<sub>i+1</sub></i> at the apex, drawn orange; in the net <i>Z<sub>k</sub></i> it hangs from its fan face <i>W<sub>i</sub></i> along the equator edge <i>u<sub>i</sub>u<sub>i+1</sub></i>.' },
  fan: { label: 'Fan face W<sub>i</sub>', re: /\bfan faces?\b|\bthe fan\b/g, link: '#defs-octa', short: 'The face <i>W<sub>i</sub></i> = <i>w u<sub>i</sub> u<sub>i+1</sub></i> at the antipode, drawn blue. The four fan faces form the fan around <i>w</i>, opened along the slit with an angular gap κ<sub>w</sub>.' },
  Zk: { label: 'The net Z<sub>k</sub>', re: /\bZ<sub>k<\/sub>|\bnets? Z/g, link: '#defs-Zk', short: 'The unfolding whose cut tree is the star of <i>v</i> (its four edges) plus the single edge <i>w u<sub>k</sub></i>. Hinges: the four equator edges and the other three edges at <i>w</i>.' },
  slit: { label: 'Slit', re: /\bslit\b/g, link: '#defs-Zk', short: 'The cut edge <i>w u<sub>k</sub></i> at the antipode; the fan opens there and <i>u<sub>k</sub></i> gets two copies, <i>u<sub>k</sub></i> and <i>u<sub>k</sub></i>′.' },
  cuttree: { label: 'Cut tree', re: /\bcut trees?\b/g, link: '#defs-net', short: 'The set of edges cut to unfold: a spanning tree of the vertex graph whose complement (the hinges) is a spanning tree of the dual graph. Each cut edge has two copies in the net, of equal length.' },
  rule: { label: 'The rule', re: /\bthe rule\b/g, link: '#defs-rule', short: 'Apex <i>v</i> = the vertex of largest curvature; <i>w</i> = its antipode (the unique non-neighbour); slit <i>k</i> = the neighbour of <i>w</i> of largest curvature.' },
  D: { label: 'Wedge D', re: /\bwedge D\b|\bD-lemma\b/g, link: '#F_D', short: 'For a triple with middle petal <i>V<sub>j</sub></i>: the intersection of the two closed half-planes bounded by the cut-edge lines through <i>u<sub>j</sub>v<sub>i</sub></i> and <i>u<sub>j+1</sub>v<sub>j+1</sub></i> on the sides away from <i>V<sub>j</sub></i>. Every common point of the outer petals lies in D.' },
  cstar: { label: 'The point c*', re: /\bc\*\b|<i>c<\/i>\*/g, link: '#F_above', short: 'Centre of the rotation by κ = κ<sub>u</sub> + κ<sub>u′</sub> that composes the two gap rotations: the point on <i>w</i>’s side of the base <i>u u</i>′ with ∠<i>c</i>*<i>u u</i>′ = κ<sub>u</sub>/2 and ∠<i>u u</i>′<i>c</i>* = κ<sub>u′</sub>/2.' },
  M: { label: 'The line M', re: /\bline M\b|\bthe line <i>M<\/i>|\b<i>M<\/i>\b/g, link: '#F_above', short: 'The line through <i>c</i>* and <i>v</i>. Measured around <i>c</i>*, the composed rotation moves points from <i>u</i>′’s side of M to <i>u</i>’s side.' },
  triple: { label: 'Triple Lemma', re: /\bTriple Lemma\b/g, all: true, link: '#F_triple', short: 'For three consecutive fan faces <i>W<sub>i</sub></i>, <i>W<sub>j</sub></i>, <i>W<sub>j+1</sub></i> (in any net where they are contiguous) with petals <i>V<sub>i</sub></i>, <i>V<sub>j</sub></i>, <i>V<sub>j+1</sub></i>: under (H) the outer petals <i>V<sub>i</sub></i> and <i>V<sub>j+1</sub></i> are disjoint. Numerically verified; proof open in two places.' },
  lemmaA: { label: 'Lemma A', re: /\bLemma A\b/g, all: true, link: '#lemmaA', short: 'If a vertex <i>v</i> is adjacent to every other vertex, cutting exactly the edges at <i>v</i> gives a net (the limit of the Aronov–O’Rourke star unfolding with source at <i>v</i>). Proved.' },
  lemmaF: { label: 'Lemma F', re: /\bLemma F\b/g, all: true, link: '#lemmaF', short: 'Under (H), in every net <i>Z<sub>k</sub></i> none of the six far pairs overlaps: the two opposite-petal pairs and the four petal-versus-far-fan pairs. Numerically verified; reduces to the Triple Lemma.' },
  lemmaL: { label: 'Lemma L', re: /\bLemma L\b/g, all: true, link: '#lemmaL', short: 'With <i>v</i> the sharpest vertex and the slit at the sharpest neighbour of <i>w</i>, the three local pairs at the slit (<i>V<sub>k</sub></i>–<i>V<sub>k−1</sub></i>′, <i>V<sub>k</sub></i>–<i>W<sub>k−1</sub></i>′, <i>V<sub>k−1</sub></i>′–<i>W<sub>k</sub></i>) never overlap. Numerically verified; proof open.' },
  shared: { label: 'Shared-vertex lemma', re: /\bshared-vertex lemma\b/g, all: true, link: '#octa_shared', short: 'Two faces of a net that contain the same copy of a vertex occupy disjoint angular wedges there (the face angles at a convex vertex sum to less than 2π), so they never overlap. Proved.' },
  cone: { label: 'Cone inequality', re: /\bcone inequality\b/g, link: '#defs-cone', short: 'At a vertex of a convex polytope each face angle is at most the sum of the other face angles at that vertex (the polygon inequality on the unit sphere).' },
  thickness: { label: 'Thickness', re: /\bthickness\b/g, link: '#defs-thickness', short: 'Smallest extent of the polytope divided by its diameter (ratio of the smallest to the largest singular value of the centred vertex matrix). Zero for a doubly covered polygon.' },
  flat: { label: 'Flat development around v', re: /\bflat development\b|\bflat petals?\b|\bglued flat\b/g, link: '#F_rot', short: 'The three petals of a triple glued around <i>v</i> with no gaps, as on the polytope; possible because their angles at <i>v</i> sum to less than 2π, and there they occupy disjoint wedges at <i>v</i>. The net is this picture with the outer petals rotated about <i>u</i> and <i>u</i>′ by the gaps κ<sub>u</sub>, κ<sub>u′</sub>.' },
  hinge: { label: 'Hinge', re: /\bhinges?\b/g, link: '#defs-net', short: 'An uncut edge: the two faces sharing it stay attached in the net. The hinges form a spanning tree of the dual graph.' },
  nearness: { label: 'Far and local pairs', re: /\bfar pairs?\b|\blocal pairs?\b/g, link: '#defs-Zk', short: 'Of the 28 face pairs of <i>Z<sub>k</sub></i>, nine share no net vertex: three local pairs at the slit (across the gap at <i>w</i>) and six far pairs (the two opposite-petal pairs and the four petal-versus-far-fan pairs).' },
};
const SKIP = new Set(['A', 'H2', 'H3', 'FIGURE', 'SVG', 'FIGCAPTION', 'BUTTON', 'SELECT', 'OUTPUT', 'LABEL', 'TABLE', 'STYLE', 'SCRIPT']);
function linkTerms(root, selfId) {
  const counts = {}; const keys = Object.keys(GLOSS).filter(k => { const l = GLOSS[k].link; if (!selfId) return true; if (l === '#' + selfId) return false; if (selfId === 'defs' && l.startsWith('#defs-')) return false; return true; });
  const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT, { acceptNode(n) { let p = n.parentNode; while (p && p !== root) { if (SKIP.has(p.tagName) || (p.classList && (p.classList.contains('term') || p.classList.contains('chip') || p.classList.contains('crumbs') || p.classList.contains('thm-head')))) return NodeFilter.FILTER_REJECT; p = p.parentNode; } return NodeFilter.FILTER_ACCEPT; } });
  const nodes = []; let n; while ((n = walker.nextNode())) nodes.push(n);
  for (const node of nodes) {
    const text = node.nodeValue; const hits = []; const art = node.parentNode && node.parentNode.closest ? node.parentNode.closest('article') : null; const artId = art ? art.id.slice(2) : null;
    for (const key of keys) { const g = GLOSS[key]; if (artId && (g.link === '#' + artId || (artId === 'defs' && g.link.startsWith('#defs-')))) continue; g.re.lastIndex = 0; let m; while ((m = g.re.exec(text))) { if (!g.all && (counts[key] || 0) >= 1) break; hits.push([m.index, m.index + m[0].length, key]); counts[key] = (counts[key] || 0) + 1; if (!g.all) break; } }
    if (!hits.length) continue;
    hits.sort((a, b) => a[0] - b[0]); const frag = document.createDocumentFragment(); let pos = 0;
    for (const [s, e, key] of hits) { if (s < pos) continue; frag.appendChild(document.createTextNode(text.slice(pos, s))); const a = document.createElement('a'); a.className = 'term'; a.href = GLOSS[key].link; a.dataset.term = key; a.tabIndex = 0; a.textContent = text.slice(s, e); frag.appendChild(a); pos = e; }
    frag.appendChild(document.createTextNode(text.slice(pos))); node.parentNode.replaceChild(frag, node);
  }
  // terms written as HTML (e.g. <i>c</i>*) are handled by explicit markup: <a class="term" data-term="cstar">
}
let tipEl = null, tipTimer = null;
function showTip(a) {
  const g = GLOSS[a.dataset.term]; if (!g) return;
  if (!tipEl) { tipEl = document.createElement('div'); tipEl.id = 'tip'; document.body.appendChild(tipEl); tipEl.addEventListener('mouseenter', () => clearTimeout(tipTimer)); tipEl.addEventListener('mouseleave', hideTip); }
  tipEl.innerHTML = `<div class="tl">${g.label}</div><div class="td">${g.short}</div><a href="${g.link}">Go to definition →</a>`;
  tipEl.style.display = 'block';
  const r = a.getBoundingClientRect(); const tw = Math.min(360, window.innerWidth - 24);
  tipEl.style.width = tw + 'px'; let left = Math.max(12, Math.min(r.left, window.innerWidth - tw - 12)); let top = r.bottom + 8 + window.scrollY;
  if (r.bottom + 180 > window.innerHeight) top = r.top + window.scrollY - tipEl.offsetHeight - 8;
  tipEl.style.left = left + 'px'; tipEl.style.top = top + 'px';
}
function hideTip() { tipTimer = setTimeout(() => { if (tipEl) tipEl.style.display = 'none'; }, 180); }
document.addEventListener('mouseover', e => { const a = e.target.closest && e.target.closest('a.term'); if (a) { clearTimeout(tipTimer); showTip(a); } });
document.addEventListener('mouseout', e => { const a = e.target.closest && e.target.closest('a.term'); if (a) hideTip(); });
document.addEventListener('focusin', e => { const a = e.target.closest && e.target.closest('a.term'); if (a) showTip(a); });
document.addEventListener('focusout', e => { const a = e.target.closest && e.target.closest('a.term'); if (a) hideTip(); });
document.addEventListener('click', e => { const a = e.target.closest && e.target.closest('a.term'); if (a && matchMedia('(hover: none)').matches && !a.dataset.tapped) { e.preventDefault(); a.dataset.tapped = '1'; showTip(a); setTimeout(() => delete a.dataset.tapped, 1500); } });
