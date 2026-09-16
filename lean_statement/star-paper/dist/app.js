'use strict';
const D = window.PAPER_DATA;
const $ = s => document.querySelector(s);
const escapeHTML = s => String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const labels = {proved:'Proved · stated inputs',restricted:'Proved · restricted scope',defined:'Definition present',missing:'Statement / bridge missing',outside:'Outside point-star scope'};
const byId = Object.fromEntries(D.annotations.map(a => [a.id,a]));
let lastTrigger = null;
function badge(a){return `<span class="badge ${a.status}">${labels[a.status]}</span>`;}
function declaration(ref){
  const d=D.declarations[ref.join(':')];
  const href=`sources/${d.module}.html#L${d.line}`;
  return `<details class="declaration"><summary><span class="decl-kind">${d.kind==='theorem'?'THEOREM':'DEFINITION'}</span><code>${escapeHTML(d.name)}</code></summary><div class="decl-content"><p class="code-path">${escapeHTML(d.namespace)}</p>${d.context?`<details class="context"><summary>Surrounding Lean context & hypotheses</summary><pre><code>${escapeHTML(d.context)}</code></pre></details>`:''}<pre class="signature"><code>${escapeHTML(d.signature)}</code></pre><p class="source-links"><a href="${href}" target="_blank" rel="noopener">Full source & proof ↗</a> <a href="sources/${d.module}.lean" download>Download Lean</a></p><p class="fine">${d.kind==='theorem'?'Proof body omitted here; original statement retained. Read section context for inherited hypotheses.':'Original source definition; supporting declarations are in the full file.'}</p></div></details>`;
}
function select(id,trigger,scroll=false){
  const a=byId[id];if(!a)return;
  lastTrigger=trigger?.closest(".passage") ? trigger : document.querySelector(`#${a.blocks[0]} .annotation-button`);
  document.body.classList.remove('reading-only');$('#annotations-toggle').checked=true;
  document.querySelectorAll('[data-annotation]').forEach(el=>{
    const active=el.dataset.annotation===id;el.classList.toggle('active',active);
    if(el.tagName==='BUTTON')el.setAttribute('aria-pressed',String(active));
  });
  $('#annotation-content').innerHTML=`<div class="inspector-eyebrow">LEAN ANNOTATION ${String(D.annotations.indexOf(a)+1).padStart(2,'0')} / ${D.annotations.length}</div><h2 id="inspector-heading" tabindex="-1">${escapeHTML(a.title)}</h2>${badge(a)}<dl class="status-grid"><dt>Statement</dt><dd>${escapeHTML(a.statement)}</dd><dt>Proof</dt><dd>${escapeHTML(a.proof)}</dd></dl><div class="scope"><strong>Exact scope</strong><p>${escapeHTML(a.scope)}</p></div><p>${escapeHTML(a.note)}</p>${a.steps.length?`<h3>How the proof is split</h3><ol class="steps">${a.steps.map(s=>`<li>${escapeHTML(s)}</li>`).join('')}</ol>`:''}${a.gap?`<div class="gap"><strong>Still needed</strong><p>${escapeHTML(a.gap)}</p></div>`:''}${a.refs.length?`<h3>Read the Lean</h3><p class="fine">Exact excerpts, linked to their full source. A checked conditional theorem does not construct its inputs.</p>${a.refs.map(declaration).join('')}`:'<p class="no-declaration">No matching Lean declaration to display.</p>'}<a class="back-to-text" href="#${a.blocks[0]}">↖ Corresponding paper passage</a>`;
  $('#annotation-content').scrollTop=0;
  if(scroll && matchMedia('(max-width: 1050px)').matches){$('#inspector').scrollIntoView({behavior:'smooth',block:'start'});$('#inspector-heading').focus({preventScroll:true});}
  $('#selection-live').textContent=`Selected: ${a.title}. ${labels[a.status]}.`;
}
document.addEventListener('click',e=>{
  const trigger=e.target.closest('button[data-annotation]');
  if(trigger)select(trigger.dataset.annotation,trigger,true);
  if(e.target.closest('#return-to-passage') && lastTrigger){lastTrigger.scrollIntoView({behavior:'smooth',block:'center'});lastTrigger.focus({preventScroll:true});}
});
$('#annotations-toggle').addEventListener('change',e=>document.body.classList.toggle('reading-only',!e.target.checked));
$('#proof-map').innerHTML=D.annotations.filter(a=>a.id!=='curve').map((a,i)=>`<li><a href="#${a.blocks[0]}">${escapeHTML(a.title)}</a><button data-annotation="${a.id}" aria-pressed="false" aria-label="Inspect ${escapeHTML(a.title)}">${badge(a)}</button></li>`).join('');
select('main');
