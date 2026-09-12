const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const root=path.resolve(__dirname,'..'),html=fs.readFileSync(path.join(root,'bipyramid-switch-demo.html'),'utf8');
const json=html.match(/<script id="switch-data" type="application\/json">([\s\S]*?)<\/script>/)[1],data=JSON.parse(json);
assert.equal(data.frames.length,101);
const nodes={};
for(const id of ['switch-data','solid','net','time','start','before','after','end','reset-view','time-label','geometry-text','proof-state','cut-text'])nodes[id]={value:'50',events:{},innerHTML:'',textContent:'',addEventListener(k,fn){this.events[k]=fn},setPointerCapture(){}};
nodes['switch-data'].textContent=json;
vm.runInNewContext(fs.readFileSync(path.join(root,'bipyramid-switch.js'),'utf8'),{document:{getElementById:id=>nodes[id]}});
const slits=new Set();
for(let i=0;i<=100;i++){
 const f=data.frames[i];assert.deepEqual(f.points[6],[32,29,164]);assert.equal(f.net.length,10);assert.equal(f.cuts.length,6);f.net.flat(2).forEach(x=>assert(Number.isFinite(x)));
 nodes.time.value=String(i);nodes.time.events.input();slits.add(f.slit);
 assert.equal(nodes.net.innerHTML.match(/<polygon/g).length,10);assert.equal(nodes.solid.innerHTML.match(/<polygon/g).length,10);
 assert(!/NaN|Infinity|undefined/.test(nodes.net.innerHTML+nodes.solid.innerHTML));
 if(process.env.SWITCH_QA_DIR&&[0,4,5,100].includes(i))for(const id of ['solid','net'])fs.writeFileSync(path.join(process.env.SWITCH_QA_DIR,`switch-${id}-${i}.svg`),`<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 580 400" width="870" height="600">${nodes[id].innerHTML}</svg>`);
}
assert.deepEqual([...slits],[2,0]);nodes.before.events.click();assert.match(nodes['cut-text'].textContent,/p–u2/);nodes.after.events.click();assert.match(nodes['cut-text'].textContent,/p–u0/);
nodes.start.events.click();assert.match(nodes['proof-state'].textContent,/Six true vertices/);nodes.end.events.click();assert.match(nodes['proof-state'].textContent,/throughout/);
const before=nodes.solid.innerHTML;nodes.solid.events.pointerdown({clientX:0,clientY:0,pointerId:1});nodes.solid.events.pointermove({clientX:20,clientY:12});nodes.solid.events.pointerup();assert.notEqual(nodes.solid.innerHTML,before);
console.log('Switch insertion: 101 finite frames, both selected cuts, transition controls, theorem labels, and 3D rotation passed.');
