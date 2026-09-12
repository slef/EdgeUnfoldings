const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const root=path.resolve(__dirname,'..'),html=fs.readFileSync(path.join(root,'bipyramid-aligned-demo.html'),'utf8');
const json=html.match(/<script id="aligned-data" type="application\/json">([\s\S]*?)<\/script>/)[1],data=JSON.parse(json);
assert.equal(data.frames.length,101);assert.equal(data.cuts.length,6);
const nodes={};
for(const id of ['aligned-data','solid','net','completion','time','start','end','reset-view','time-label','geometry-text','proof-state','completion-text','cut-text'])nodes[id]={value:'50',events:{},innerHTML:'',textContent:'',addEventListener(k,fn){this.events[k]=fn},setPointerCapture(){}};
nodes['aligned-data'].textContent=json;
vm.runInNewContext(fs.readFileSync(path.join(root,'bipyramid-aligned.js'),'utf8'),{document:{getElementById:id=>nodes[id]}});
const initialCuts=nodes['cut-text'].textContent,branches=new Set();
for(let i=0;i<=100;i++){
 const f=data.frames[i];assert.equal(f.points[6][2],-5);assert.equal(f.net.length,10);f.net.flat(2).forEach(x=>assert(Number.isFinite(x)));
 nodes.time.value=String(i);nodes.time.events.input();assert.equal(nodes['cut-text'].textContent,initialCuts);
 assert.equal(nodes.net.innerHTML.match(/<polygon/g).length,10);assert.equal(nodes.solid.innerHTML.match(/<polygon/g).length,10);
 assert(!/NaN|Infinity|undefined/.test(nodes.net.innerHTML+nodes.solid.innerHTML+nodes.completion.innerHTML));branches.add(f.added);
 if(process.env.ALIGNED_QA_DIR&&[0,50,100].includes(i))for(const id of ['solid','net','completion'])fs.writeFileSync(path.join(process.env.ALIGNED_QA_DIR,`aligned-${id}-${i}.svg`),`<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 580 400" width="870" height="600">${nodes[id].innerHTML}</svg>`);
}
assert.equal(branches.size,2);assert.match(nodes['completion-text'].textContent,/already a convex polygon/);
nodes.start.events.click();assert.match(nodes['proof-state'].textContent,/Six true vertices/);assert.match(nodes['completion-text'].textContent,/flat start/);
nodes.end.events.click();assert.match(nodes['proof-state'].textContent,/every positive height/);
const before=nodes.solid.innerHTML;nodes.solid.events.pointerdown({clientX:0,clientY:0,pointerId:1});nodes.solid.events.pointermove({clientX:20,clientY:12});nodes.solid.events.pointerup();assert.notEqual(nodes.solid.innerHTML,before);
console.log('Aligned insertion: 101 finite drawing frames, fixed cuts, both proof branches, status labels, and 3D rotation passed.');
