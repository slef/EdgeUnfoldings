"use strict";
const toggle = document.getElementById("annotations-toggle");
const popup = document.getElementById("lean-hover");
const body = document.getElementById("lean-hover-body");
const symbols = window.LEAN_HOVERS.symbols;
const declarations = [...document.querySelectorAll(".declaration[data-source-path]")];
const hoverDelay = 450;
let active = null, pinned = false, showTimer = null, hideTimer = null;
const esc = value => String(value).replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
function markdown(text) {
  // Lean documentation is data, never executable HTML.
  return text.split(/(```[\s\S]*?```|\n\*\*\*\n)/g).map(part => {
    if (part.startsWith("```")) return `<pre><code>${esc(part.replace(/^```[^\n]*\n/, "").replace(/```$/, ""))}</code></pre>`;
    if (part.trim() === "***") return '<hr>';
    return esc(part).split(/\n\s*\n/).filter(Boolean).map(p => `<p>${p.trim().replace(/^\*import ([^*]+)\*$/, '<em>import $1</em>').replace(/`([^`]+)`/g,"<code>$1</code>").replace(/\n/g,"<br>")}</p>`).join("");
  }).join("");
}
function place() {
  if (!active || !popup.classList.contains("visible")) return;
  const r = active.getBoundingClientRect();
  const w = Math.min(570, window.innerWidth - 24);
  popup.style.width = `${w}px`;
  const h = popup.getBoundingClientRect().height;
  const roomBelow = window.innerHeight - r.bottom - 16;
  const top = roomBelow >= Math.min(h, 210) ? r.bottom + 8 : Math.max(12, r.top - h - 8);
  popup.style.left = `${Math.max(12, Math.min(r.left, window.innerWidth - w - 12))}px`;
  popup.style.top = `${Math.max(12, Math.min(top, Math.max(12, window.innerHeight - h - 12)))}px`;
}
function close() {
  clearTimeout(showTimer); clearTimeout(hideTimer);
  if (active) active.setAttribute("aria-expanded", "false");
  popup.classList.remove("visible"); popup.hidden = true;
  active = null; pinned = false;
}
function definitionLink(d) {
  if (!d.location) return "";
  const location = d.location;
  const candidates = d.origin === "This project" ? declarations.filter(el =>
    el.dataset.sourcePath === location.path &&
    Number(el.dataset.sourceStart) <= location.line && location.line <= Number(el.dataset.sourceEnd)
  ) : [];
  const nearby = active.closest(".lean-note");
  const target = candidates.find(el => nearby && nearby.contains(el)) || candidates[0];
  const path = `${esc(location.path)}:${location.line}`;
  const other = (window.LEAN_DECLARATION_LINKS || []).find(entry =>
    d.origin === "This project" && entry.path === location.path && entry.start <= location.line && location.line <= entry.end);
  return target
    ? `<p class="hover-location"><a class="definition-jump" href="#${esc(target.id)}">View definition on this page →</a><br><span>${path}</span></p>`
    : other ? `<p class="hover-location"><a href="${esc(other.href)}">View definition in the interactive paper →</a><br><span>${path}</span></p>`
    : `<p class="hover-location"><a href="${esc(location.href)}" target="_blank" rel="noopener">${path} ↗</a></p>`;
}
function revealDefinition(id, updateHistory = false) {
  const target = document.getElementById(id);
  if (!target || !target.matches(".declaration")) return;
  close();
  toggle.checked = true; document.body.classList.remove("reading-only");
  for (let details = target; details; details = details.parentElement?.closest("details")) details.open = true;
  if (updateHistory && location.hash !== `#${id}`) history.pushState(null, "", `#${id}`);
  target.querySelector(":scope > summary").focus({preventScroll:true});
  target.scrollIntoView({block:"start", behavior:window.matchMedia("(prefers-reduced-motion: reduce)").matches ? "instant" : "smooth"});
}
function show(button, pin = false) {
  clearTimeout(showTimer); clearTimeout(hideTimer);
  if (active === button) { pinned ||= pin; return; }
  if (active) active.setAttribute("aria-expanded", "false");
  active = button; pinned = pin;
  const d = symbols[button.dataset.symbol];
  button.setAttribute("aria-expanded", "true");
  body.innerHTML = `<div class="hover-origin"><span class="origin-label">${esc(d.origin)}</span>${d.local ? `<span>${esc(d.bindingKind || 'Local binding')}</span>` : ''}</div>${d.hover ? markdown(d.hover) : `<p>${esc(d.fallback)}</p>`}${d.definition ? `<details class="hover-definition" open><summary>${d.local ? 'Binding in this source' : 'Definition in the source'}</summary><pre><code>${esc(d.definition)}</code></pre></details>` : ''}${definitionLink(d)}`;
  popup.hidden = false; popup.classList.add("visible"); body.scrollTop = 0; place();
}
function scheduleClose() {
  clearTimeout(showTimer);
  if (!pinned) hideTimer = setTimeout(close, 220);
}
document.addEventListener("pointerover", e => {
  const b = e.target.closest(".lean-symbol");
  if (b && !pinned) { clearTimeout(hideTimer); clearTimeout(showTimer); showTimer = setTimeout(() => show(b), hoverDelay); }
});
document.addEventListener("pointerout", e => {
  if (e.target.closest(".lean-symbol") && !popup.contains(e.relatedTarget)) scheduleClose();
});
document.addEventListener("focusin", e => {
  const b = e.target.closest(".lean-symbol");
  if (b) show(b);
  else if (!popup.contains(e.target)) close();
});
document.addEventListener("click", e => {
  const jump = e.target.closest(".definition-jump");
  if (jump && !e.metaKey && !e.ctrlKey && !e.shiftKey && !e.altKey) {
    e.preventDefault(); revealDefinition(decodeURIComponent(jump.hash.slice(1)), true); return;
  }
  const b = e.target.closest(".lean-symbol");
  if (b) {
    if (active === b && pinned) close();
    else { show(b,true); if (e.detail === 0) document.getElementById("lean-hover-close").focus({preventScroll:true}); }
  }
  else if (!popup.contains(e.target)) close();
});
popup.addEventListener("pointerenter", () => { clearTimeout(hideTimer); clearTimeout(showTimer); });
popup.addEventListener("pointerleave", scheduleClose);
document.getElementById("lean-hover-close").addEventListener("click", () => {
  const previous = active; close();
  if (previous) { previous.focus({preventScroll:true}); close(); }
});
document.addEventListener("keydown", e => {
  if (e.key === "Escape") {
    const previous = active, inside = popup.contains(document.activeElement);
    close();
    if (previous && inside) { previous.focus({preventScroll:true}); close(); }
  }
});
window.addEventListener("resize", place);
window.addEventListener("scroll", e => {
  if (e.target instanceof Node && popup.contains(e.target)) return;
  if (pinned) place(); else close();
}, true);
toggle.addEventListener("change", () => {
  close(); document.body.classList.toggle("reading-only", !toggle.checked);
});

window.addEventListener("hashchange", () => revealDefinition(decodeURIComponent(location.hash.slice(1))));
revealDefinition(decodeURIComponent(location.hash.slice(1)));
