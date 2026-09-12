"""Metric planar sketches of the three patch types; not spatial witnesses."""
from pathlib import Path
import math
ROOT=Path(__file__).resolve().parent

def build():
    panels=[('Convex patch',{4:(0,0),0:(3,0),6:(1.6,1.6),3:(4,2)},None),
            ('Inward corner at 0',{4:(0,0),0:(3,0),6:(1.6,1.6),3:(5,-1)},0),
            ('Inward corner at 6',{4:(0,0),0:(3,0),6:(1.05,1.45),3:(.3,4)},6)]
    s=['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 960 330" role="img" aria-labelledby="title desc">',
       '<title id="title">Three flattened patch shapes</title>',
       '<desc id="desc">Blue triangle 046 and coral triangle 036 joined along 06; dashed rays enclose each patch at vertex 4. Explanatory planar sketches, not certified polyhedra.</desc>',
       '<rect width="960" height="330" fill="#fafbf8"/>',
       '<style>text{font-family:system-ui,sans-serif;fill:#243d4c}.title{font-size:18px;font-weight:650}.label{font-size:17px;font-weight:650}.note{font-size:14px;fill:#60707a}</style>']
    for k,(title,p,inward) in enumerate(panels):
        x0=320*k
        s.append(f'<text class="title" x="{x0+160}" y="34" text-anchor="middle">{title}</text>')
        if k:s.append(f'<path d="M{x0},55 V285" stroke="#dde4e1"/>')
        xmin,xmax=min(v[0] for v in p.values()),max(v[0] for v in p.values())
        ymin,ymax=min(v[1] for v in p.values()),max(v[1] for v in p.values())
        scale=min(232/(xmax-xmin),168/(ymax-ymin))
        cx=x0+160;cy=171
        xy={v:(cx+(x-(xmin+xmax)/2)*scale,cy-(y-(ymin+ymax)/2)*scale) for v,(x,y) in p.items()}
        def pts(vs):return ' '.join(f'{xy[v][0]:.2f},{xy[v][1]:.2f}' for v in vs)
        rays=[0,6] if inward is None else [3,6] if inward==0 else [0,3]
        for v in rays:
            a,b=xy[4],xy[v];dx,dy=b[0]-a[0],b[1]-a[1];L=math.hypot(dx,dy)
            c=(b[0]+14*dx/L,b[1]+14*dy/L)
            s.append(f'<path d="M{a[0]:.2f},{a[1]:.2f} L{c[0]:.2f},{c[1]:.2f}" stroke="#81949d" stroke-dasharray="5 4" stroke-width="2"/>')
        for vs,fill in [([4,0,6],'#acd2df'),([0,3,6],'#edb1a0')]:
            s.append(f'<polygon points="{pts(vs)}" fill="{fill}" fill-opacity=".82" stroke="#506674" stroke-width="1.7" stroke-linejoin="round"/>')
        labels={4:(-12,18),0:(0,23),3:(11,-8),6:(-15,-8)}
        if k==2:labels[6]=(16,5)
        for v,(x,y) in xy.items():
            color='#b7413a' if v==inward else '#324d5c'
            s.append(f'<circle cx="{x:.2f}" cy="{y:.2f}" r="{4.4 if v==inward else 3}" fill="{color}"/>')
            dx,dy=labels[v]
            s.append(f'<text class="label" x="{x+dx:.2f}" y="{y+dy:.2f}" text-anchor="middle">{v}</text>')
        note='Left is always safe here' if inward is None else 'Only the severe-angle part remains' if inward==0 else 'Only the sharp-4 part remains'
        s.append(f'<text class="note" x="{x0+160}" y="302" text-anchor="middle">{note}</text>')
    s.append('</svg>')
    (ROOT/'figures/a992-patch-cases.svg').write_text('\n'.join(s)+'\n')

if __name__=='__main__':build()
