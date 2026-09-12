const assert=require('node:assert/strict');
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const root=path.resolve(__dirname,'..');
const html=fs.readFileSync(path.join(root,'bipyramid-morph-demo.html'),'utf8');
const json=html.match(/<script id="morph-data" type="application\/json">([\s\S]*?)<\/script>/)[1];
const data=JSON.parse(json);
for(const row of data.examples)for(const rule of row.nets){assert.equal(rule.length,101);for(const net of rule){assert.equal(net.length,10);for(const tri of net){assert.equal(tri.length,3);for(const p of tri){assert.equal(p.length,2);p.forEach(x=>assert(Number.isFinite(x)));}}}}
const nodes={};
for(const id of ['morph-data','solid','net','example','rule','time','start','end','reset-view','time-label','geometry-text','certificate-state','cut-text'])nodes[id]={value:'0',events:{},innerHTML:'',textContent:'',className:'',addEventListener(k,fn){this.events[k]=fn},setPointerCapture(){}};
nodes['morph-data'].textContent=json;
vm.runInNewContext(fs.readFileSync(path.join(root,'bipyramid-morph.js'),'utf8'),{document:{getElementById:id=>nodes[id]}});
assert.match(nodes['certificate-state'].textContent,/starting net: safe/);
nodes.end.events.click();assert.match(nodes['certificate-state'].textContent,/overlap in positive area/);
assert.equal(nodes.net.innerHTML.match(/<polygon/g).length,10);
assert.equal(nodes.solid.innerHTML.match(/<polygon/g).length,10);
assert(!/NaN|Infinity|undefined/.test(nodes.net.innerHTML+nodes.solid.innerHTML));
if(process.env.MORPH_QA_DIR){for(const id of ['solid','net'])fs.writeFileSync(path.join(process.env.MORPH_QA_DIR,'morph-'+id+'.svg'),`<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 580 400" width="870" height="600">${nodes[id].innerHTML}</svg>`);}
nodes.rule.value='1';nodes.rule.events.input();assert.match(nodes['certificate-state'].textContent,/256 closed rational intervals/);
nodes.time.value='47';nodes.time.events.input();assert.match(nodes['time-label'].textContent,/0.47/);
const before=nodes.solid.innerHTML;nodes.solid.events.pointerdown({clientX:0,clientY:0,pointerId:1});nodes.solid.events.pointermove({clientX:20,clientY:15});assert.notEqual(nodes.solid.innerHTML,before);nodes.solid.events.pointerup();
nodes.example.value='1';nodes.example.events.input();assert.match(nodes['certificate-state'].textContent,/8 closed rational intervals/);
nodes.start.events.click();assert.match(nodes['geometry-text'].textContent,/Six true vertices/);
console.log('Insertion slider, tree comparison, certificate labels, 3D rotation, and 404 finite frames passed.');
