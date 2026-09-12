(() => {
  'use strict';
  const points = [[1.34,.085,.055],[.8,.8,0],[0,0,0],[-1.2,1.7,1.1],[1,0,0],[-1.4,.4,0],[1.8,.2,0]];
  const faces = [[0,3,2,4],[0,3,6],[0,4,6],[1,3,5],[1,3,6],[1,5,2,4,6],[2,3,5]];
  const colors = ['#e6b257','#e78075','#a7c4b8','#a7c4b8','#a7c4b8','#b9d7ea','#a7c4b8'];
  const cuts = {left:['0-3','0-4','1-3','2-3','3-5','3-6'],right:['0-3','0-4','0-6','1-3','2-3','3-5']};
  const edge = (a,b) => [a,b].sort((x,y)=>x-y).join('-');
  document.querySelectorAll('.a992-model').forEach(box => {
    const svg=box.querySelector('svg'); let yaw=.55,pitch=1.05,rule='left',running=false,last=null,drag=null,frame=null;
    const center=[0,0,0].map((_,i)=>points.reduce((s,p)=>s+p[i],0)/points.length);
    function draw() {
      const ca=Math.cos(yaw),sa=Math.sin(yaw),cb=Math.cos(pitch),sb=Math.sin(pitch);
      const ps=points.map(p=>{
        const [x,y,z]=p.map((v,i)=>v-center[i]); const u=ca*x-sa*y,v=sa*x+ca*y;
        return [310+132*u,205-132*(cb*v+sb*z),-sb*v+cb*z];
      });
      let out='<title>Exact A992 counterexample; drag to rotate</title>';
      faces.map((f,i)=>({f,i,z:f.reduce((s,v)=>s+ps[v][2],0)/f.length})).sort((a,b)=>a.z-b.z).forEach(({f,i})=>{
        out+=`<polygon points="${f.map(v=>ps[v].slice(0,2).join(',')).join(' ')}" fill="${colors[i]}" stroke="#56656d" stroke-width="1.2"/>`;
        f.forEach((a,j)=>{const b=f[(j+1)%f.length];if(cuts[rule].includes(edge(a,b)))out+=`<line x1="${ps[a][0]}" y1="${ps[a][1]}" x2="${ps[b][0]}" y2="${ps[b][1]}" stroke="#b92c40" stroke-width="3.4"/>`;});
      });
      ps.forEach((p,i)=>{
        const dx=i===0?20:i===4?12:-13,dy=i===0?22:i===4?-15:-12;
        out+=`<circle cx="${p[0]}" cy="${p[1]}" r="3.7" fill="#203440"/><line x1="${p[0]}" y1="${p[1]}" x2="${p[0]+dx*.65}" y2="${p[1]+dy*.65}" stroke="#526875" stroke-width=".7"/><text x="${p[0]+dx}" y="${p[1]+dy}" text-anchor="middle" font-size="16" font-weight="600" fill="#172c3b" stroke="#fafaf7" stroke-width="3" paint-order="stroke">${i}</text>`;
      });
      svg.innerHTML=out;
      box.querySelector('[data-action="left"]').setAttribute('aria-pressed',String(rule==='left'));
      box.querySelector('[data-action="right"]').setAttribute('aria-pressed',String(rule==='right'));
    }
    function tick(t) {if(!running)return;if(last!==null)yaw+=(t-last)*.00035;last=t;draw();frame=requestAnimationFrame(tick);}
    box.querySelectorAll('button').forEach(b=>b.addEventListener('click',()=>{
      const a=b.dataset.action;
      if(a==='left'||a==='right')rule=a;
      if(a==='reset'){yaw=.55;pitch=1.05;running=false;last=null;cancelAnimationFrame(frame);frame=null;}
      if(a==='rotate'){running=!running;last=null;cancelAnimationFrame(frame);frame=null;if(running)frame=requestAnimationFrame(tick);}
      box.querySelector('[data-action="rotate"]').textContent=running?'Stop rotation':'Rotate';draw();
    }));
    svg.addEventListener('pointerdown',e=>{drag=[e.clientX,e.clientY];svg.setPointerCapture(e.pointerId);});
    svg.addEventListener('pointermove',e=>{if(!drag)return;yaw+=(e.clientX-drag[0])*.009;pitch=Math.max(-1.5,Math.min(1.5,pitch-(e.clientY-drag[1])*.009));drag=[e.clientX,e.clientY];draw();});
    ['pointerup','pointercancel','lostpointercapture'].forEach(name=>svg.addEventListener(name,()=>{drag=null;}));
    draw();
  });
})();
