const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');
const root = path.resolve(__dirname, '..');
const html = fs.readFileSync(path.join(root, 'index.html'), 'utf8');
const graphs = JSON.parse(fs.readFileSync(path.join(root, 'results/catalogue.json'))).graphs;
const group = r => r.universal_vertices.length ? 'A' : r.dome_bases.length ? 'B' : r.degree_five_cofacial_sources.length ? 'C' : r.cofacial_sources.length ? 'D' : 'E';
function element(kind, id, dataset={}) {
  return {kind,id,dataset,hidden:false,attributes:{},events:{},
    addEventListener(type, fn){this.events[type]=fn},setAttribute(k,v){this.attributes[k]=v},
    matches(selector){return selector.split(',').includes(kind)},scrollIntoView(){this.scrolled=true}};
}
const cards = graphs.map(r => element('.graph-card', r.id, {status:r.status,group:group(r)}));
const sections = ['A','B','C','D','E'].map(g => Object.assign(element('.graph-group',`group-${g}`),{querySelectorAll(){return cards.filter(c=>c.dataset.group===g)}}));
const buttons = ['all','open','solved'].map(f=>element('button',f,{filter:f}));
const count=element('p','visible-count'), cuts=element('input','show-cuts');
const nodes=[...cards,...sections,count,cuts];const flags={};const hooks={};
const document={
  querySelectorAll(s){return s==='.graph-card'?cards:s==='[data-filter]'?buttons:s==='.graph-group'?sections:[]},
  getElementById(id){return nodes.find(n=>n.id===id)},
  body:{classList:{toggle(key,val){flags[key]=val}}}
};
const location={hash:''};const window={addEventListener(k,fn){hooks[k]=fn}};
vm.runInNewContext(fs.readFileSync(path.join(root,'overview.js'),'utf8'),{document,location,window});
buttons[1].events.click();assert.equal(cards.filter(c=>!c.hidden).length,24);assert.equal(buttons[1].attributes['aria-pressed'],'true');
buttons[2].events.click();assert.equal(cards.filter(c=>!c.hidden).length,10);
location.hash='#N7-A992';hooks.hashchange();assert.equal(cards.filter(c=>!c.hidden).length,34);assert(nodes.find(n=>n.id==='N7-A992').scrolled);
cuts.events.change({target:{checked:true}});assert.equal(flags['show-cuts'],true);
cuts.events.change({target:{checked:false}});assert.equal(flags['show-cuts'],false);
assert.equal((html.match(/class="graph-card /g)||[]).length,34);
assert(html.includes('ARGUMENTS.html#cofacial-core'));assert(html.includes('BIPYRAMID_PATCHES.html#lemma-l7'));
console.log('Overview status filters, cut visibility, deep links, and all 34 cards passed.');
