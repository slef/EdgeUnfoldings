'use strict';
(() => {
  const cards = Array.from(document.querySelectorAll('.graph-card'));
  const buttons = Array.from(document.querySelectorAll('[data-filter]'));
  function filter(value) {
    for (const card of cards) card.hidden = value !== 'all' && card.dataset.status !== value;
    for (const section of document.querySelectorAll('.graph-group')) {
      section.hidden = !Array.from(section.querySelectorAll('.graph-card')).some(card => !card.hidden);
    }
    for (const button of buttons) button.setAttribute('aria-pressed', String(button.dataset.filter === value));
    const visible = cards.filter(card => !card.hidden).length;
    document.getElementById('visible-count').textContent = `Showing ${visible} of 34 graphs${value === 'all' ? '' : ` (${value})`}.`;
  }
  for (const button of buttons) button.addEventListener('click', () => filter(button.dataset.filter));
  document.getElementById('show-cuts').addEventListener('change', event => document.body.classList.toggle('show-cuts', event.target.checked));
  function revealAnchor() {
    const id = decodeURIComponent(location.hash.slice(1));
    const target = document.getElementById(id);
    if (!target) return;
    if (target.matches('.graph-card,.graph-group') && target.hidden) filter('all');
    if (target.matches('details')) target.open = true;
    if (id) target.scrollIntoView({block: 'start'});
  }
  window.addEventListener('hashchange', revealAnchor);
  if (location.hash) revealAnchor();
})();
