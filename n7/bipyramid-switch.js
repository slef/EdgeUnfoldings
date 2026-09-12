(() => {
  'use strict';
  const get=id=>document.getElementById(id), data=JSON.parse(get('switch-data').textContent);
  const solid=get('solid'), net=get('net');
  let yaw=.2,pitch=1.25,drag=null;
  const edge=(a,b)=>[a,b].sort((x,y)=>x-y).join('-');
  const label=v=>v<5?'u'+v:v===5?'p':'q';
  function fit(ps) {
    const lo=[0,1].map(i=>Math.min(...ps.map(p=>p[i]))),hi=[0,1].map(i=>Math.max(...ps.map(p=>p[i])));
    const scale=Math.min(490/Math.max(hi[0]-lo[0],1e-9),310/Math.max(hi[1]-lo[1],1e-9));
    return p=>[290+scale*(p[0]-(lo[0]+hi[0])/2),200-scale*(p[1]-(lo[1]+hi[1])/2)];
  }
  const polygon=(ps,fill,stroke='#506a77',width=1.2)=>`<polygon points="${ps.map(p=>p.join(',')).join(' ')}" fill="${fill}" stroke="${stroke}" stroke-width="${width}"/>`;
  const text=(p,s,color='#264656')=>`<text x="${p[0]+7}" y="${p[1]-8}" font-size="14" fill="${color}" stroke="white" stroke-width="3" paint-order="stroke">${s}</text>`;
  function draw() {
    const i=Number(get('time').value),t=i/100,f=data.frames[i],p=f.points,cuts=f.cuts.map(e=>edge(...e));
    const project=([x,y,z])=>{const a=Math.cos(yaw)*x-Math.sin(yaw)*y,b=Math.sin(yaw)*x+Math.cos(yaw)*y;return [a,Math.cos(pitch)*b+Math.sin(pitch)*z,-Math.sin(pitch)*b+Math.cos(pitch)*z];};
    const raw=p.map(project),place=fit([...data.frames[0].points,...data.frames[100].points].map(project)),ps=raw.map(place);
    let out='<title>Selected cuts at insertion t = '+t.toFixed(2)+'</title>';
    data.faces.map((face,k)=>({face,k,z:face.reduce((s,v)=>s+raw[v][2],0)/3})).sort((a,b)=>a.z-b.z).forEach(({face,k})=>{
      out+=polygon(face.map(v=>ps[v]),k<5?'#bbd5e4':'#e6c78b');
      face.forEach((a,j)=>{const b=face[(j+1)%3];if(cuts.includes(edge(a,b)))out+=`<line x1="${ps[a][0]}" y1="${ps[a][1]}" x2="${ps[b][0]}" y2="${ps[b][1]}" stroke="#b43c48" stroke-width="2.7"/>`;});
    });
    const a=place(project(data.frames[0].points[5])),b=place(project(data.frames[100].points[5]));out+=`<line x1="${a[0]}" y1="${a[1]}" x2="${b[0]}" y2="${b[1]}" stroke="#1d799a" stroke-width="2.5" stroke-dasharray="5 4"/>`;
    ps.forEach((pt,v)=>{out+=`<circle cx="${pt[0]}" cy="${pt[1]}" r="${v===5?5:3}" fill="${v===5?'#1d799a':'#264656'}"/>`+text(v===2?[pt[0]-31,pt[1]-4]:v===3?[pt[0]-31,pt[1]+24]:pt,label(v));});solid.innerHTML=out;
    const np=fit(f.net.flat());out='<title>Safe net by the supporting-plane insertion theorem</title>';
    f.net.forEach((tri,k)=>out+=polygon(tri.map(np),k<5?'#bbd5e4':'#e6c78b'));
    f.net.forEach((tri,k)=>{const q=tri.map(np),c=[0,1].map(j=>q.reduce((s,p)=>s+p[j],0)/3);out+=`<text x="${c[0]}" y="${c[1]+4}" text-anchor="middle" font-size="11" fill="#264656" stroke="white" stroke-width="2" paint-order="stroke">${(k<5?'W':'V')+(k%5)}</text>`;});net.innerHTML=out;
    get('time-label').textContent='Insertion t = '+t.toFixed(2);
    get('geometry-text').textContent=`New-pole curvature ≈ ${Math.max(0,f.gap*180/Math.PI).toFixed(2)}° · selected slit p–u${f.slit} · the inserted vertex stays least curved`;
    get('proof-state').textContent=i===0?'Six true vertices: the marked point is flat in the original base. The limiting net is the pyramid’s safe edge-star unfolding.':'Seven true vertices. The written family theorem proves the selected rule safe throughout the interval, including the change of slit.';
    get('cut-text').textContent='Selected cuts: '+f.cuts.map(([a,b])=>label(a)+'–'+label(b)).join(', ')+'.';
  }
  get('before').addEventListener('click',()=>{get('time').value='4';draw();});get('after').addEventListener('click',()=>{get('time').value='5';draw();});get('time').addEventListener('input',draw);get('start').addEventListener('click',()=>{get('time').value='0';draw();});get('end').addEventListener('click',()=>{get('time').value='100';draw();});get('reset-view').addEventListener('click',()=>{yaw=.2;pitch=1.25;draw();});
  solid.addEventListener('pointerdown',e=>{drag=[e.clientX,e.clientY];solid.setPointerCapture(e.pointerId);});
  solid.addEventListener('pointermove',e=>{if(!drag)return;yaw+=(e.clientX-drag[0])*.01;pitch=Math.max(-1.5,Math.min(1.5,pitch-(e.clientY-drag[1])*.01));drag=[e.clientX,e.clientY];draw();});
  ['pointerup','pointercancel','lostpointercapture'].forEach(name=>solid.addEventListener(name,()=>drag=null));
  draw();
})();
