// ---------- F_sharp axis diagram ------------------------------------------------------------------------------
function sharpAxis() {
  const W = 620, x0 = 40, x1 = 590, lo = 2.0, hi = 2 * Math.PI, X = v => x0 + (v - lo) / (hi - lo) * (x1 - x0);
  const marks = [[2 * Math.PI / 3, '2π/3'], [6 * Math.PI / 7, '6π/7'], [Math.PI, 'π'], [2 * Math.PI, '2π']];
  return `<div class="axis"><svg viewBox="0 0 ${W} 110" xmlns="http://www.w3.org/2000/svg">
  <rect class="bar" x="${X(2*Math.PI/3)}" y="38" width="${X(6*Math.PI/7)-X(2*Math.PI/3)}" height="18"/>
  <rect class="ok" x="${X(6*Math.PI/7)}" y="38" width="${X(2*Math.PI)-X(6*Math.PI/7)}" height="18"/>
  <line x1="${x0}" y1="56" x2="${x1}" y2="56"/>
  ${marks.map(([v, l]) => `<line class="tick" x1="${X(v)}" y1="52" x2="${X(v)}" y2="62"/><text x="${X(v)}" y="78" text-anchor="middle">${l}</text>`).join('')}
  <text x="${X(2*Math.PI/3)}" y="28">(H) alone: κ<tspan font-size="8">v</tspan> ≥ 2π/3</text>
  <text x="${(X(6*Math.PI/7)+X(2*Math.PI))/2}" y="100" text-anchor="middle">above-base case possible only here: κ<tspan font-size="8">v</tspan> &gt; 6π/7, so Σν &lt; 8π/7 and every ν &lt; 4π/7</text>
  <text x="${(X(2*Math.PI/3)+X(6*Math.PI/7))/2}" y="100" text-anchor="middle">excluded</text>
  </svg></div>`;
}

// ---------- interactive octahedron -----------------------------------------------------------------------------
function widgetShell() {
  return `<div class="widget" id="wg"><div class="controls">
    <div class="row"><label>preset</label><select id="wg-preset"></select><span></span></div>
    <div class="row"><label>apex v</label><select id="wg-apex"><option value="rule">rule: sharpest</option><option value="0">v</option><option value="1">w</option><option value="2">u₀</option><option value="3">u₁</option><option value="4">u₂</option><option value="5">u₃</option></select><span></span></div>
    <div class="row"><label>slit k</label><select id="wg-slit"><option value="rule">rule: sharpest neighbour</option><option value="0">0</option><option value="1">1</option><option value="2">2</option><option value="3">3</option></select><span></span></div>
    <div id="wg-sliders"></div>
    <div class="row"><label></label><button type="button" id="wg-random">Random shape</button><span></span></div>
  </div><div class="stage"><div id="wg-svg"></div><div class="readout" id="wg-read"></div><div class="grid24" id="wg-grid"></div></div></div>`;
}

const WG = { params: null };
const SL = [['zv', 'height of v', 0.05, 3, 0.01], ['zw', 'height of w', 0.05, 3, 0.01]];
for (let i = 0; i < 4; i++) SL.push([`r${i}`, `u${'₀₁₂₃'[i]} radius`, 0.005, 1.5, 0.005], [`phi${i}`, `u${'₀₁₂₃'[i]} angle°`, 0, 360, 0.5], [`z${i}`, `u${'₀₁₂₃'[i]} height`, -4, 4, 0.01]);

function fromPreset(p) { const q = { zv: p.zv, zw: p.zw }; p.u.forEach((d, i) => { q[`r${i}`] = d.r; q[`phi${i}`] = d.phi; q[`z${i}`] = d.z; }); return q; }
function points(q) {
  const P = [[0, 0, q.zv], [0, 0, -q.zw]];
  const us = [0, 1, 2, 3].map(i => ({ i, phi: q[`phi${i}`], p: [q[`r${i}`] * Math.cos(q[`phi${i}`] * Math.PI / 180), q[`r${i}`] * Math.sin(q[`phi${i}`] * Math.PI / 180), q[`z${i}`]] }));
  us.sort((a, b) => a.phi - b.phi); us.forEach(u => P.push(u.p)); return { P, order: us.map(u => u.i) };
}
const sub = (a, b) => [a[0]-b[0], a[1]-b[1], a[2]-b[2]], dot = (a, b) => a[0]*b[0]+a[1]*b[1]+a[2]*b[2], cross = (a, b) => [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]];
const norm = a => Math.sqrt(dot(a, a)), dist = (a, b) => norm(sub(a, b));
const angleAt = (b, a, c) => { const x = sub(a, b), y = sub(c, b); return Math.acos(Math.max(-1, Math.min(1, dot(x, y) / (norm(x) * norm(y))))); };
// combinatorics: vertices 0=v, 1=w, 2..5 = ring (sorted by angle). faces (0,e_i,e_{i+1}), (1,e_i,e_{i+1}).
const FACES = []; for (let i = 0; i < 4; i++) { FACES.push([0, 2 + i, 2 + (i + 1) % 4]); FACES.push([1, 2 + i, 2 + (i + 1) % 4]); }
const NBR = { 0: [2, 3, 4, 5], 1: [2, 3, 4, 5], 2: [0, 3, 1, 5], 3: [0, 4, 1, 2], 4: [0, 5, 1, 3], 5: [0, 2, 1, 4] };  // cyclic
const ANTI = { 0: 1, 1: 0, 2: 4, 3: 5, 4: 2, 5: 3 };
function convex(P) {
  const c = [0, 1, 2].map(k => P.reduce((s, p) => s + p[k], 0) / 6);
  for (const f of FACES) { const n = cross(sub(P[f[1]], P[f[0]]), sub(P[f[2]], P[f[0]])); const sc = dot(n, sub(c, P[f[0]]));
    for (let x = 0; x < 6; x++) { if (f.includes(x)) continue; const sx = dot(n, sub(P[x], P[f[0]])); if (sx * sc <= 1e-9 * norm(n) * norm(sub(P[x], P[f[0]]))) return false; } }
  return true;
}
function curvatures(P) {
  const k = new Array(6).fill(2 * Math.PI);
  for (const f of FACES) for (let t = 0; t < 3; t++) k[f[t]] -= angleAt(P[f[t]], P[f[(t + 1) % 3]], P[f[(t + 2) % 3]]);
  return k;
}
function third(A, B, la, lb) { const dx = B[0]-A[0], dy = B[1]-A[1], L = Math.hypot(dx, dy), ex = dx / L, ey = dy / L; const x = (la*la - lb*lb + L*L) / (2*L), h = Math.sqrt(Math.max(la*la - x*x, 0)); return [A[0] + x*ex + h*ey, A[1] + x*ey - h*ex]; }  // right of A->B
function net(P, v, k) {
  const w = ANTI[v]; const ring = NBR[w];
  // orient ring so that faces exist: any cyclic order of NBR[w] gives faces (w, r_j, r_{j+1}) in FACES? NBR lists neighbours in face-cyclic order, so yes.
  const n = 4, r = ring.map(u => dist(P[w], P[u])), s = ring.map(u => dist(P[v], P[u])), l = ring.map((u, j) => dist(P[u], P[ring[(j + 1) % n]]));
  const om = ring.map((u, j) => angleAt(P[w], P[u], P[ring[(j + 1) % n]]));
  const faces = {}; let th = 0;
  for (let t = 0; t < 4; t++) { const j = (k + t) % 4; const c = Math.cos(th), sn = Math.sin(th); const R = q => [c*q[0] - sn*q[1], sn*q[0] + c*q[1]];
    const wq = [0, 0], ui = [r[j], 0], un = [r[(j + 1) % 4] * Math.cos(om[j]), r[(j + 1) % 4] * Math.sin(om[j])]; const vq = third(ui, un, s[j], s[(j + 1) % 4]);
    faces['W' + t] = [R(wq), R(ui), R(un)]; faces['V' + t] = [R(vq), R(un), R(ui)]; th += om[j]; }
  return { faces, ring, kw: 2 * Math.PI - om.reduce((a, b) => a + b, 0) };
}
function sat(T1, T2) { let best = Infinity; for (const T of [T1, T2]) for (let i = 0; i < 3; i++) { const e = [T[(i+1)%3][0]-T[i][0], T[(i+1)%3][1]-T[i][1]]; const L = Math.hypot(e[0], e[1]) || 1e-300; const nx = -e[1]/L, ny = e[0]/L;
  const p1 = T1.map(q => q[0]*nx + q[1]*ny), p2 = T2.map(q => q[0]*nx + q[1]*ny); best = Math.min(best, Math.min(Math.max(...p1), Math.max(...p2)) - Math.max(Math.min(...p1), Math.min(...p2))); } return Math.max(0, best); }
const PAIRS = { 'V₀–V₃′': ['V0', 'V3'], 'V₀–W₃′': ['V0', 'W3'], 'V₃′–W₀': ['V3', 'W0'], 'V₀–V₂': ['V0', 'V2'], 'V₁–V₃′': ['V1', 'V3'], 'V₀–W₂': ['V0', 'W2'], 'V₂–W₀': ['V2', 'W0'], 'V₁–W₃′': ['V1', 'W3'], 'V₃′–W₁': ['V3', 'W1'] };
function overlaps(N, scale) { const out = []; for (const [nm, [a, b]] of Object.entries(PAIRS)) if (sat(N.faces[a], N.faces[b]) > 1e-9 * scale) out.push(nm); return out; }
function svgOf(N, hits, W = 520, H = 400, pad = 22) {
  const pts = Object.values(N.faces).flat(); const xs = pts.map(p => p[0]), ys = pts.map(p => p[1]);
  const lo = [Math.min(...xs), Math.min(...ys)], hi = [Math.max(...xs), Math.max(...ys)];
  const sc = Math.min((W - 2 * pad) / (hi[0] - lo[0] + 1e-12), (H - 2 * pad) / (hi[1] - lo[1] + 1e-12)), cx = (lo[0] + hi[0]) / 2, cy = (lo[1] + hi[1]) / 2;
  const X = q => [W / 2 + (q[0] - cx) * sc, H / 2 - (q[1] - cy) * sc], fmt = q => X(q).map(v => v.toFixed(1)).join(',');
  let s = `<svg viewBox="0 0 ${W} ${H}" xmlns="http://www.w3.org/2000/svg" class="net">`;
  const bad = new Set(hits.flatMap(nm => PAIRS[nm]));
  for (const [key, T] of Object.entries(N.faces)) { const cls = (key[0] === 'W' ? 'fan' : 'petal') + (bad.has(key) ? ' hl' : ''); s += `<polygon class="${cls}" points="${T.map(fmt).join(' ')}"/>`; }
  for (const [key, T] of Object.entries(N.faces)) { const c = [(T[0][0]+T[1][0]+T[2][0])/3, (T[0][1]+T[1][1]+T[2][1])/3]; const [x, y] = X(c); s += `<text class="face" x="${x.toFixed(1)}" y="${y.toFixed(1)}" text-anchor="middle" dominant-baseline="middle">${key[0]}<tspan class="sub">${key[1]}${key[1] === '3' ? '′' : ''}</tspan></text>`; }
  for (let t = 0; t < 4; t++) { const [x, y] = X(N.faces['W' + t][1]); s += `<text class="lbl vtx" x="${(x+3).toFixed(1)}" y="${(y-3).toFixed(1)}">u<tspan class="sub">${t}</tspan></text>`; const [vx, vy] = X(N.faces['V' + t][0]); s += `<text class="lbl apex" x="${(vx+3).toFixed(1)}" y="${(vy-3).toFixed(1)}">v</text>`; }
  const [wx, wy] = X([0, 0]); s += `<circle class="w" cx="${wx.toFixed(1)}" cy="${wy.toFixed(1)}" r="3"/><text class="lbl" x="${(wx+5).toFixed(1)}" y="${(wy+12).toFixed(1)}">w</text></svg>`;
  return s;
}
const VNAME = ['v', 'w', 'u₀', 'u₁', 'u₂', 'u₃'];
function initWidget() {
  const box = document.getElementById('wg-sliders'); if (!box || box.dataset.ready) return; box.dataset.ready = '1';
  const presets = FIGS.presets; const sel = document.getElementById('wg-preset');
  sel.innerHTML = Object.keys(presets).map(k => `<option>${k}</option>`).join('');
  WG.params = fromPreset(presets[Object.keys(presets)[0]]);
  let html = ''; let lastGroup = '';
  for (const [key, label, lo, hi, step] of SL) { const g = key.match(/\d/) ? 'u' + key.match(/\d/)[0] : 'poles'; if (g !== lastGroup) { html += `<div class="group">${g === 'poles' ? 'v and w' : 'equator vertex ' + VNAME[2 + Number(g[1])]}</div>`; lastGroup = g; }
    html += `<div class="row"><label for="wg-${key}">${label}</label><input type="range" id="wg-${key}" min="${lo}" max="${hi}" step="${step}"><output id="wgo-${key}"></output></div>`; }
  box.innerHTML = html;
  const setSliders = () => SL.forEach(([key]) => { document.getElementById('wg-' + key).value = WG.params[key]; document.getElementById('wgo-' + key).value = Number(WG.params[key]).toFixed(key.startsWith('phi') ? 0 : 2); });
  SL.forEach(([key]) => document.getElementById('wg-' + key).addEventListener('input', e => { WG.params[key] = Number(e.target.value); document.getElementById('wgo-' + key).value = Number(e.target.value).toFixed(key.startsWith('phi') ? 0 : 2); update(); }));
  sel.addEventListener('change', () => { WG.params = fromPreset(presets[sel.value]); setSliders(); update(); });
  document.getElementById('wg-apex').addEventListener('change', update); document.getElementById('wg-slit').addEventListener('change', update);
  document.getElementById('wg-random').addEventListener('click', () => { for (let tries = 0; tries < 200; tries++) { const q = { zv: 0.3 + 2 * Math.random(), zw: 0.3 + 2 * Math.random() }; for (let i = 0; i < 4; i++) { q[`r${i}`] = 0.2 + 1.2 * Math.random(); q[`phi${i}`] = i * 90 + (Math.random() - 0.5) * 100; q[`z${i}`] = (Math.random() - 0.5) * 2; } if (convex(points(q).P)) { WG.params = q; break; } } setSliders(); update(); });
  setSliders(); update();
}
function update() {
  const { P } = points(WG.params); const read = document.getElementById('wg-read'), svg = document.getElementById('wg-svg'), grid = document.getElementById('wg-grid');
  if (!convex(P)) { svg.innerHTML = ''; grid.innerHTML = ''; read.innerHTML = `<span class="warn">Not a convex octahedron with this combinatorics: a face plane has another vertex on the wrong side. Move a slider back.</span>`; return; }
  const kap = curvatures(P); const scale = Math.max(...P.flatMap(a => P.map(b => dist(a, b))));
  const sharpest = kap.indexOf(Math.max(...kap));
  const apexSel = document.getElementById('wg-apex').value, slitSel = document.getElementById('wg-slit').value;
  const v = apexSel === 'rule' ? sharpest : Number(apexSel); const w = ANTI[v]; const ring = NBR[w];
  let k; if (slitSel === 'rule') { let best = -1; ring.forEach((u, j) => { if (kap[u] > best) { best = kap[u]; k = j; } }); } else k = Number(slitSel);
  const N = net(P, v, k); const hits = overlaps(N, scale);
  svg.innerHTML = svgOf(N, hits);
  const H = kap.every(x => x <= kap[v] + 1e-12);
  read.innerHTML = `<span><span class="k">apex</span> ${VNAME[v]}${v === sharpest ? ' (sharpest)' : ''}</span><span><span class="k">antipode</span> ${VNAME[w]}</span><span><span class="k">slit</span> ${VNAME[w]}–${VNAME[ring[k]]}</span>` +
    kap.map((x, i) => `<span><span class="k">κ(${VNAME[i]})</span> ${x.toFixed(3)}</span>`).join('') + `<span><span class="k">Σκ</span> ${kap.reduce((a, b) => a + b, 0).toFixed(3)}</span>` +
    `<span><span class="k">(H) for this apex</span> ${H ? 'yes' : 'no'}</span>` + (hits.length ? `<span class="warn">overlap: ${hits.join(', ')}</span>` : `<span style="color:var(--proved);font-weight:600">simple net</span>`);
  // 24-net grid
  let g = `<div class="h"></div>` + [0, 1, 2, 3].map(j => `<div class="h">k=${j}</div>`).join('');
  for (let a = 0; a < 6; a++) { g += `<div>${VNAME[a]}${a === sharpest ? ' ★' : ''}</div>`; const wa = ANTI[a]; let kr = 0, best = -1; NBR[wa].forEach((u, j) => { if (kap[u] > best) { best = kap[u]; kr = j; } });
    for (let j = 0; j < 4; j++) { const h = overlaps(net(P, a, j), scale).length; g += `<div class="cell ${h ? 'bad' : 'ok'}${a === sharpest && j === kr ? ' rule' : ''}" data-a="${a}" data-k="${j}" title="apex ${VNAME[a]}, slit ${j}${h ? ': overlap' : ': simple'}">${h ? '×' : '✓'}</div>`; } }
  grid.innerHTML = g;
  grid.querySelectorAll('.cell').forEach(c => c.addEventListener('click', () => { document.getElementById('wg-apex').value = c.dataset.a; document.getElementById('wg-slit').value = c.dataset.k; update(); }));
}
