(() => {
  'use strict';
  const data=JSON.parse(document.getElementById('morph-data').textContent);
  const get=id=>document.getElementById(id), solid=get('solid'), net=get('net');
  let yaw=.95,pitch=.6,drag=null;
  const edge=(a,b)=>[a,b].sort((x,y)=>x-y).join('-');
  function fit(ps) {
    const xs=ps.map(p=>p[0]),ys=ps.map(p=>p[1]);
    const lo=[Math.min(...xs),Math.min(...ys)], hi=[Math.max(...xs),Math.max(...ys)];
    const scale=Math.min(510/Math.max(hi[0]-lo[0],1e-9),330/Math.max(hi[1]-lo[1],1e-9));
    return p=>[290+scale*(p[0]-(lo[0]+hi[0])/2),200-scale*(p[1]-(lo[1]+hi[1])/2)];
  }
  function label(p,s,color='#233e46') {return `<text x="${p[0]+8}" y="${p[1]-8}" font-size="15" fill="${color}" stroke="white" stroke-width="3" paint-order="stroke">${s}</text>`;}
  function curvature(points,v) {
    let sum=0;
    data.faces.filter(f=>f.includes(v)).forEach(f=>{
      const [a,b]=f.filter(x=>x!==v).map(i=>points[i].map((x,k)=>x-points[v][k]));
      const dot=a.reduce((s,x,k)=>s+x*b[k],0),la=Math.hypot(...a),lb=Math.hypot(...b);
      sum+=Math.acos(Math.max(-1,Math.min(1,dot/(la*lb))));
    });
    return Math.max(0,(2*Math.PI-sum)*180/Math.PI);
  }
  function draw() {
    const ex=Number(get('example').value),rule=Number(get('rule').value),i=Number(get('time').value),t=i/100,row=data.examples[ex];
    const points=row.start.map((p,v)=>p.map((x,k)=>x+t*(row.points[v][k]-x)));
    const project=p=>{const [x,y,z]=p,u=Math.cos(yaw)*x-Math.sin(yaw)*y,v=Math.sin(yaw)*x+Math.cos(yaw)*y;return [u,Math.cos(pitch)*v+Math.sin(pitch)*z,-Math.sin(pitch)*v+Math.cos(pitch)*z];};
    const raw=points.map(project),s=fit([...row.start,...row.points].map(project)),ps=raw.map(s),cuts=row.cuts[rule].map(e=>edge(...e));
    let out='<title>Convex insertion, t = '+t.toFixed(2)+'</title>';
    data.faces.map((f,k)=>({f,k,z:f.reduce((sum,v)=>sum+raw[v][2],0)/3})).sort((a,b)=>a.z-b.z).forEach(({f,k})=>{
      const color=ex===0&&(k===0||k===6)?'#eab1b8':k<5?'#ebd09b':'#b8d4df';
      out+=`<polygon points="${f.map(v=>ps[v].join(',')).join(' ')}" fill="${color}" stroke="#526b74" stroke-width="1.2"/>`;
      f.forEach((a,j)=>{const b=f[(j+1)%3];if(cuts.includes(edge(a,b)))out+=`<line x1="${ps[a][0]}" y1="${ps[a][1]}" x2="${ps[b][0]}" y2="${ps[b][1]}" stroke="#b73248" stroke-width="2.8"/>`;});
    });
    const a=s(project(row.start[row.vertex])),b=s(project(row.points[row.vertex]));
    out+=`<line x1="${a[0]}" y1="${a[1]}" x2="${b[0]}" y2="${b[1]}" stroke="#188553" stroke-width="3" stroke-dasharray="5 4"/>`;
    ps.forEach((p,v)=>{const col=v===row.vertex?'#138750':'#253d47';out+=`<circle cx="${p[0]}" cy="${p[1]}" r="${v===row.vertex?5:3}" fill="${col}"/>`+label(p,v<5?'u'+v:v===5?'v':'w',col);});solid.innerHTML=out;
    const triangles=row.nets[rule][i],n=fit(triangles.flat());out='<title>Unfolded ten-triangle net</title>';
    triangles.forEach((tri,k)=>{const q=tri.map(n),col=ex===0&&(k===0||k===6)?'#e8a0b3':k<5?'#e9c883':'#a9cdda';out+=`<polygon points="${q.map(p=>p.join(',')).join(' ')}" fill="${col}" fill-opacity=".70" stroke="#486673" stroke-width="1.1"/>`;const c=[0,1].map(j=>q.reduce((sum,p)=>sum+p[j],0)/3);out+=`<text x="${c[0]}" y="${c[1]}" text-anchor="middle" font-size="13" fill="#213f47" stroke="white" stroke-width="2" paint-order="stroke">${k}</text>`;});net.innerHTML=out;
    get('time-label').textContent='Insertion t = '+t.toFixed(2);
    get('geometry-text').textContent=`Moving u${row.vertex} · curvature ≈ ${curvature(points,row.vertex).toFixed(2)}° · ${i===0?'Six true vertices and one intrinsically flat marked point.':'Seven true vertices; convexity is proved for every positive t.'}`;
    const state=get('certificate-state');state.className='morph-stat';
    if(ex===1||rule===1) state.textContent=`Certified for the entire insertion, including this parameter: ${ex===1?8:256} closed rational intervals cover [0,1]. Every interval checks all 45 face pairs.`;
    else if(i===0)state.textContent='Exact starting net: safe. All 45 pairs are certified. This same tree will overlap at the endpoint.';
    else if(i===100){state.className+=' failure';state.textContent='Exact endpoint: faces 0 and 6 overlap in positive area. A rational point lies strictly inside both. Choose the other tree to see a certified repair.';}
    else state.textContent='Initial tree: this drawing is an illustration at the selected parameter. The start is certified safe and the endpoint is certified overlapping; intermediate frames are not proof claims.';
    get('cut-text').textContent='Cuts: '+row.cuts[rule].map(([a,b])=>`${a===5?'v':a===6?'w':'u'+a}–${b===5?'v':b===6?'w':'u'+b}`).join(', ')+'.';
  }
  ['example','rule','time'].forEach(id=>get(id).addEventListener('input',draw));
  get('start').addEventListener('click',()=>{get('time').value='0';draw();});get('end').addEventListener('click',()=>{get('time').value='100';draw();});get('reset-view').addEventListener('click',()=>{yaw=.95;pitch=.6;draw();});
  solid.addEventListener('pointerdown',e=>{drag=[e.clientX,e.clientY];solid.setPointerCapture(e.pointerId);});
  solid.addEventListener('pointermove',e=>{if(!drag)return;yaw+=(e.clientX-drag[0])*.01;pitch=Math.max(-1.5,Math.min(1.5,pitch-(e.clientY-drag[1])*.01));drag=[e.clientX,e.clientY];draw();});
  ['pointerup','pointercancel','lostpointercapture'].forEach(name=>solid.addEventListener(name,()=>drag=null));
  draw();
})();
