// Regression for links which changed content invisibly or stopped at the same hash.
const fs = require('node:fs'), vm = require('node:vm'), assert = require('node:assert/strict');
const path = require('node:path');
const html = fs.readFileSync(path.join(__dirname, '../notes/status.html'), 'utf8');
const script = html.match(/<script>([\s\S]*?)<\/script>/)[1];
const marker = script.indexOf('let showAll = false;');
const handlers = {}, elements = new Map(), visits = [];
function element(id) {
  return {id, innerHTML:'', style:{}, setAttribute(){}, appendChild(){},
    focus(){visits.push(['focus',id]);}, scrollIntoView(){visits.push(['scroll',id]);}};
}
for (const id of ['detail','strip','tree','expandAll','progress-history']) elements.set(id,element(id));
const document = {
  addEventListener(name, f){ (handlers[name] ||= []).push(f); },
  getElementById(id){
    if (elements.has(id)) return elements.get(id);
    if (elements.get('detail').innerHTML.includes(`id="${id}"`)) return element(id);
    return null;
  },
  querySelectorAll(){return [];}, createElement(){return {...element(''),dataset:{}};}
};
const window = {addEventListener(name,f){handlers[name] = [f];}};
const location = {hash:''};
const ctx = vm.createContext({document,window,location,console});
vm.runInContext(script.slice(0,marker),ctx);
// Router integration uses the actual article renderer; graphics and glossary are checked separately.
vm.runInContext('linkTerms = () => {}; mountViewers = () => {}; initWidget = () => {};',ctx);
vm.runInContext(script.slice(marker),ctx);
assert.equal(visits.length,0,'Fresh overview stays at its progress notes');
function click(id, extra={}) {
  const e = {button:0, defaultPrevented:false, target:{closest(selector){return selector === 'a[href^="#"]' ? {getAttribute(){return '#'+id;}} : null;}},
    preventDefault(){this.defaultPrevented=true;},...extra};
  for (const f of handlers.click) f(e);
  return e;
}
assert(click('F_basecones').defaultPrevented);
assert.equal(location.hash,'F_basecones'); // Browser normalizes assignment with #.
location.hash = '#F_basecones'; handlers.hashchange[0]();
assert(elements.get('detail').innerHTML.includes('Why the large-angle branches'));
assert.deepEqual(visits.at(-1),['scroll','a-F_basecones']);
const before=visits.length;
click('F_basecones');
assert.equal(visits.length,before+2,'Same hash focuses and scrolls again');
location.hash='#t_octa_minus'; handlers.hashchange[0]();
assert(elements.get('detail').innerHTML.includes('These are not 409 sample shapes'));
assert.deepEqual(visits.at(-1),['scroll','a-t_octa_minus']);
location.hash='#F_basecones'; handlers.hashchange[0](); // back/forward event
assert.deepEqual(visits.at(-1),['scroll','a-F_basecones']);
location.hash='#defs-H'; handlers.hashchange[0]();
assert.deepEqual(visits.at(-1),['scroll','defs-H']);
elements.get('expandAll').onclick();
assert(elements.get('detail').innerHTML.includes('id="a-t_prismd"'));
assert.deepEqual(visits.at(-1),['scroll','defs-H']);
assert(!click('F_basecones',{ctrlKey:true}).defaultPrevented);
assert(!click('unrecognized-id').defaultPrevented);
const ids = vm.runInContext('new Set([...NODES.map(n=>n.id),...DEFS.map(d=>d[0])])',ctx);
const rendered = vm.runInContext("NODES.map(n=>article(n,true)).join('') + progressHistory()",ctx);
for (const m of rendered.matchAll(/<a\b[^>]*href="#([^"]+)"/g)) assert(ids.has(m[1]),`Broken result link: ${m[1]}`);
assert(!/__\w+__/.test(html),'No unresolved build tokens');
console.log('Navigation: changed/same hash, history, definitions, show-all, modified clicks, and all result links pass.');
