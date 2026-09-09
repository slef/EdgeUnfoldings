// Keep both interactive cut choices tied to the exact example they explain.
const fs=require('node:fs'),vm=require('node:vm'),assert=require('node:assert/strict'),path=require('node:path');
const root=path.join(__dirname,'../..');
const html=fs.readFileSync(path.join(root,'durer_small_n/notes/status.html'),'utf8');
const script=html.match(/<script>([\s\S]*?)<\/script>/)[1];
const ctx=vm.createContext({document:{addEventListener(){}},console});
vm.runInContext(script.slice(0,script.indexOf('let showAll = false;')),ctx);
const article=vm.runInContext('article(byId.minus_pair,false)',ctx);
assert(article.includes('7 of those 28 whole geometric classes'));
assert(article.includes('fan at C') && article.includes('fan at D'));
assert(article.includes('16 closed cells, one tree, and 336 pair checks'));
const models=[];
for(const apex of ['P','Q']) {
  const name='minus_pair_'+apex;
  assert(article.includes(`data-model="${name}"`));
  const model=vm.runInContext(`FIGS.models.${name}`,ctx);
  const cert=JSON.parse(fs.readFileSync(path.join(root,`n6/results/minus-pair-${apex}.certificate.json`),'utf8'));
  assert.equal(JSON.stringify(model.faces),JSON.stringify(cert.faces));
  assert.equal(JSON.stringify(model.cut),JSON.stringify(cert.cut_edges));
  const points=cert.coordinate_polynomials.map(p=>p.map(polynomial=>polynomial.reduce((sum,[c,powers])=>{
    assert(powers.every(power=>power===0));
    assert(/^-?\d+$/.test(c),'This displayed example has integer coordinates');
    return sum+Number(c);
  },0)));
  assert.equal(JSON.stringify(model.P),JSON.stringify(points));
  const buttons=[{dataset:{viewTurn:'-0.35'}},{dataset:{viewTurn:'0.35'}},{dataset:{}}];
  buttons.forEach(b=>b.addEventListener=(k,f)=>{b.click=f;});
  const panel={querySelectorAll(s){return s==='[data-view-turn]'?buttons.slice(0,2):buttons.slice(2);}};
  const listeners={};
  const el={dataset:{model:name,size:'340'},style:{},setAttribute(){},
    addEventListener(k,f){listeners[k]=f;},closest(){return panel;}};
  ctx.mountRoot={querySelectorAll(){return [el];}};
  vm.runInContext('mountViewers(mountRoot)',ctx);
  const first=el.innerHTML;
  assert.equal((first.match(/<line /g)||[]).length,11);
  assert.equal((first.match(/class="(?:hid |vis )cut"/g)||[]).length,5);
  assert.equal((first.match(/<circle /g)||[]).length,6);
  assert(!/NaN|undefined/.test(first));
  buttons[0].click();assert.notEqual(el.innerHTML,first);
  buttons[2].click();assert.equal(el.innerHTML,first);
  listeners.keydown({key:'ArrowRight',preventDefault(){}});assert.notEqual(el.innerHTML,first);
  listeners.keydown({key:'Home',preventDefault(){}});assert.equal(el.innerHTML,first);
  models.push(model);
}
assert.equal(JSON.stringify(models[0].P),JSON.stringify(models[1].P));
assert.notEqual(JSON.stringify(models[0].cut),JSON.stringify(models[1].cut));
const proof=vm.runInContext('article(byId.minus_neighborhood,false)',ctx);
assert.equal((proof.match(/data-minus-class=/g)||[]).length,28);
assert.equal((proof.match(/>Excluded<\/span>/g)||[]).length,7);
assert.equal((proof.match(/>Open<\/span>/g)||[]).length,21);
assert(proof.includes('Pinciu paper, Theorem 1'));
assert(proof.includes('The two-tree algorithm remains open'));
assert.equal(vm.runInContext('byId.minus_pair.status',ctx),'open');
assert.equal(vm.runInContext('byId.minus_neighborhood.status',ctx),'proved');
console.log('Minus-edge: both exact cut choices, 3D controls, and open proof scope pass.');
