// Counts describe named proof obligations or named parameter domains.
// They are never converted into an estimated percentage of research completed.
function progressNumber(q) {
  const parts=String(q).split('/').map(Number); return parts[0]/(parts[1] || 1);
}
function coveragePercent(q) {
  const [numerator,denominator=1n]=String(q).split('/').map(BigInt);
  if (denominator<=0n || numerator<0n || numerator>denominator) throw Error('Invalid coverage fraction');
  if (numerator===denominator) return '100%';
  if (numerator===0n) return '0%';
  const digits=(100n*numerator<denominator || 100n*numerator>99n*denominator) ? 4 : 2;
  const scale=10n**BigInt(digits),rounded=(100n*numerator*scale+denominator/2n)/denominator;
  if (rounded===0n) return '&lt;0.0001%';
  if (rounded===100n*scale) return '&gt;99.9999%';
  return `${rounded/scale}.${String(rounded%scale).padStart(digits,'0')}%`;
}
function proofTally(items) { return `${items.filter(x=>x.status==='proved').length} / ${items.length}`; }
function proofSteps(items) {
  return `<ol class="proof-steps">${items.map(item=>`<li><span class="progress-state ${item.status}">${item.status==='proved'?'Proved':'Open'}</span><div><a href="#${item.link}">${item.label}</a>${item.condition?`<small>${item.condition}</small>`:''}</div></li>`).join('')}</ol>`;
}
function pairAccounting() {
  const groups=SCORE.octahedron.pair_groups;
  return `<div class="pair-accounting" role="img" aria-label="${groups.map(g=>`${g.count} ${g.label}: ${g.status}`).join('; ')}">${groups.map(g=>`<span class="${g.status}" style="flex:${g.count}">${g.count}</span>`).join('')}</div><ul class="pair-key">${groups.map(g=>`<li><span class="progress-state ${g.status}">${g.count}</span><a href="#${g.link}">${g.label}</a> — ${g.status==='conditional'?'conditional reduction':g.status}</li>`).join('')}</ul>`;
}
function boxScope(data,label) {
  return `<details class="progress-domain"><summary>Define ${label}: center, bounds, and certificate</summary><p>The parameters, in order, are (${data.parameter_names.join(', ')}).</p><p>Center: (${data.center.join(', ')}).<br>Independent half-widths: (${data.half_widths.join(', ')}).</p><p>${data.report ? `<a href="../../n6/results/${data.report}">Saved exact verification</a>` : `<a href="../../n6/results/${data.certificate}">Saved partial search (verification pending)</a>`}. Coverage measures volume in these coordinates. It is not a percentage of all shapes of this type.</p></details>`;
}
function coverageGaps() {
  return `<p><b>Two steps are still missing for a complete computational proof:</b></p><ol class="coverage-gaps">${SCORE.coverage_obligations.map(s=>`<li>${s}</li>`).join('')}</ol><p>A geometric theorem could replace this route. Neither missing step has a measured fraction complete.</p>`;
}
function caseProgress(id,compact=false) {
  const octa=SCORE.octahedron;
  const pairTotal=octa.pair_groups.reduce((n,g)=>n+g.count,0);
  const directlyProved=octa.pair_groups.filter(g=>g.status==='proved').reduce((n,g)=>n+g.count,0);
  const localTotal=octa.pair_groups.filter(g=>g.link==='lemmaL').reduce((n,g)=>n+g.count,0);
  const localProved=octa.pair_groups.filter(g=>g.link==='lemmaL' && g.status==='proved').reduce((n,g)=>n+g.count,0);
  let title,body;
  if (id==='t_octa') {
    title='Octahedron · two main proof obligations remain';
    body=`<div class="progress-key"><strong>${octa.remaining.length}</strong><span>remaining universal proof obligations</span></div><p><b>${proofTally(octa.angle_branches)} angle branches proved</b> for opposite petals. These branches partition the possibilities; they need not be equally difficult.</p>${proofSteps(octa.angle_branches)}`;
    if (compact) body+=`<p><b>${directlyProved} / ${pairTotal} face pairs directly settled.</b> The local slit obligations are ${localProved} / ${localTotal} proved; four other pairs depend on the open results.</p>`;
    if (!compact) body+=`<h4>Where the 28 face pairs stand</h4>${pairAccounting()}<p>The four conditional pairs follow once Lemma L and opposite-petal separation are proved. They are not four additional independent proof tasks, and are not counted as already solved.</p><h4>What must close next</h4><ol>${octa.remaining.map(g=>`<li><a href="#${g.link}">${g.label}</a>.</li>`).join('')}</ol><p><b>Lemma L: ${localProved} / ${localTotal} local pair obligations proved for all selected shapes.</b> Individual examples and neighborhoods have certificates, but these three general statements remain open.</p>`;
    body+=`<p class="progress-change">Latest research hour: <b>no remaining universal gap closed</b>. The new apex-entry family rules out a stronger shortcut; joint-petal separation is still needed.</p>`;
  } else if (id==='t_octa_minus') {
    const d=SCORE.minus, first=progressNumber(d.history[0].half_width),last=progressNumber(d.history.at(-1).half_width);
    title='Octahedron minus an edge · local extent is measurable';
    body=`<div class="progress-key"><strong>±${last}</strong><span>certified variation in each of 10 coordinates</span></div><p><b>${last/first}× the earlier half-width in every coordinate.</b> The whole current box is certified, including its boundaries.</p><div class="extent-history" aria-label="Verified half-width milestones">${d.history.map((h,i)=>`<span><b>±${progressNumber(h.half_width)}</b><small>${i===0?'Earlier':'Verified'}</small></span>`).join('')}</div><p>${d.leaves} certificate cells · ${d.distinct_cut_trees} cut trees · ${Object.values(d.checked_face_pairs).reduce((a,b)=>a+b,0).toLocaleString()} face-pair checks.</p><p class="global-unknown"><b>Fraction of the whole type covered: unknown.</b> The remaining shapes have not been reduced to a finite list of domains.</p>`;
    if (!compact) body+=`${boxScope(d,'the current minus-edge box')}<details class="progress-domain"><summary>History of the certified extent</summary><div class="progress-table-wrap"><table class="progress-table"><thead><tr><th>Half-width</th><th>Verified cells</th><th>Trees</th><th>Record</th></tr></thead><tbody>${d.history.map(h=>`<tr><td>±${progressNumber(h.half_width)}</td><td>${h.leaves}</td><td>${h.trees}</td><td><a href="../../n6/results/${h.report}">Verification</a></td></tr>`).join('')}</tbody></table></div><p>More cells can simply mean finer subdivision. The comparable progress measure here is how far the same ten-coordinate box extends.</p></details>${coverageGaps()}`;
    body+=`<p class="progress-change">Earlier advance: ±0.01 → ±0.05. <b>Latest research hour: unchanged at ±0.05.</b></p>`;
  } else if (id==='t_prismd') {
    const d=SCORE.prism,p=SCORE.prism_partial;
    title='Prism with one diagonal · two named search boxes';
    body=`<div class="box-progress"><div><div class="progress-key"><strong>100%</strong><span>of box A certified</span></div><p>${d.leaves} cells · ${d.distinct_cut_trees} trees · no unresolved cells.</p></div><div><div class="progress-key"><strong>${coveragePercent(p.candidate_parameter_fraction)}</strong><span>of box B provisionally covered</span></div><p>${p.unresolved_cells} unresolved cells occupy ${coveragePercent(p.unresolved_parameter_fraction)} of box B.</p></div></div><p class="progress-pending"><b>Box B: verification pending.</b> Its percentage measures the cells marked successful by the search. Only box A has a completed independent replay.</p><p><b>Boxes A and B have different centers and bounds.</b> These percentages are separate measurements. They must not be added or interpreted as coverage of the whole type.</p><p class="global-unknown"><b>Fraction of the whole type covered: unknown.</b></p>`;
    if (!compact) body+=`${boxScope(d,'box A')}${boxScope(p,'box B')}<p><b>Why count volume?</b> Box B has ${p.candidate_cells.toLocaleString()} candidate-covered cells and ${p.unresolved_cells} unresolved cells, but the candidate-covered cells are tiny. Counting cells equally would suggest ${(100*p.candidate_cells/(p.candidate_cells+p.unresolved_cells)).toFixed(1)}% coverage; their actual parameter volume is only ${coveragePercent(p.candidate_parameter_fraction)}. This fraction is exact bookkeeping of the saved subdivision; the geometric certificates for all these cells have not yet completed independent replay.</p><p><b>What does “${p.unresolved_cells} remaining” mean?</b> It is today's subdivision queue for box B. A difficult cell may split into more cells, so this count can increase even while covered volume grows. It is not a count of all remaining mathematical cases.</p>${coverageGaps()}<p><b>Alternative geometric route:</b> prove that at least one of the two quadrilateral routes at the sharper degree-four apex always works. This is still a conjecture; 60,000 numerical samples do not close it.</p>`;
    body+=`<p class="progress-change">Latest research hour: <b>box A unchanged</b>; two proposed route rules ruled out exactly. Box B’s saved subdivision is measured here, with geometric replay still pending.</p>`;
  } else return '';
  return `<section class="case-progress ${compact?'compact':''}" aria-label="${title}"><h3>${compact?`<a href="#${id}">${title}</a>`:title}</h3>${body}${compact?`<a class="progress-more" href="#${id}">See the obligations and precise scope →</a>`:''}</section>`;
}
function progressComparison() {
  const rows=SCORE.snapshots;
  return `<details class="progress-domain progress-comparison"><summary>Before and after the latest research hour</summary><div class="progress-table-wrap"><table class="progress-table"><thead><tr><th>Measure</th>${rows.map(r=>`<th>${r.label}</th>`).join('')}</tr></thead><tbody><tr><td>Fully proved six-vertex types</td>${rows.map(r=>`<td>${r.proved_types} / 7</td>`).join('')}</tr><tr><td>Octahedron: angle branches proved</td>${rows.map(r=>`<td>${r.octahedron_angle_branches} / 3</td>`).join('')}</tr><tr><td>Octahedron: local pair obligations proved</td>${rows.map(r=>`<td>${r.octahedron_local_pairs} / 3</td>`).join('')}</tr><tr><td>Minus-edge: certified half-width</td>${rows.map(r=>`<td>±${progressNumber(r.minus_half_width)}</td>`).join('')}</tr><tr><td>Prism: certified fraction of box A</td>${rows.map(r=>`<td>${coveragePercent(r.prism_box_A_fraction)}</td>`).join('')}</tr></tbody></table></div><p>That hour added exact counterexamples to proposed shortcuts, an octahedron neighborhood certificate, and a global metric-closure obstruction. It did not finish another type or one of the remaining universal proof obligations. <a href="../../n6/CONTINUATION.md">Retained research log</a>.</p></details>`;
}
function progressDashboard(compact=true) {
  const types=children('n6'),done=types.filter(n=>n.status==='proved').length;
  return `<section class="progress-dashboard"><div class="progress-heading"><h2>How far along is the proof?</h2><p><strong>${done} / ${types.length}</strong> six-vertex types proved here · ${types.length-done} remain open</p></div><p class="progress-disclaimer">The indicators below count specific obligations or coverage of a specified box. They do not estimate the percentage of effort or time remaining.</p><div class="type-tally">${types.map(n=>`<a class="${n.status}" href="#${n.id}" title="${n.title}: ${n.status}"><span>${n.status==='proved'?'✓':'○'}</span>${n.title}</a>`).join('')}</div><div class="progress-cards ${compact?'':'expanded'}">${['t_octa','t_octa_minus','t_prismd'].map(id=>caseProgress(id,compact)).join('')}</div>${progressComparison()}${compact?'<p><a href="#progress">Open the full progress dashboard</a></p>':''}</section>`;
}
