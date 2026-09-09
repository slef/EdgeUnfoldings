"""Illustrate the independently checked local angular-separation failure."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n6.bisector import selected_flanks,opposite_flank_development
from n6.local_radial import verify,interior_petal_point
from n6.polycert import verify as verify_net


def render():
    root=Path(__file__).resolve().parent
    cert=json.loads((root/'results/local-radial-failure.certificate.json').read_text())
    verify(cert);verify_net(cert)
    g,v,w,u,ring,_=selected_flanks(cert,cert['local_radial_failure'])
    fan,petal,_=opposite_flank_development(g,v,w,ring,'first')
    def xy(p):return np.array([float((x.lo+x.hi)/2) for x in p])
    f={k:xy(p) for k,p in fan.items()};p={k:xy(q) for k,q in petal.items()}
    inside=xy(interior_petal_point(petal,v));direction=inside-f[w]
    # Display ray intersections only; the proof uses exact determinant signs.
    fig,ax=plt.subplots(figsize=(11,4.8))
    ax.add_patch(Polygon(list(f.values()),facecolor='#b9d9ee',edgecolor='#236691',linewidth=1.8))
    ax.add_patch(Polygon(list(p.values()),facecolor='#f3c9a0',edgecolor='#a65821',linewidth=1.8))
    ray_end=f[w]+direction*1.12
    ax.annotate('',xy=ray_end,xytext=f[w],arrowprops=dict(arrowstyle='->',color='#5d485e',linewidth=2,linestyle='--'))
    ax.plot(*inside,'o',color='#5d485e',markersize=5)
    for point,label,offset in [(f[w],'w',(0,-18)),(p[v],'petal apex',(-8,12)),
                               (f[u],'last copy of u',(-15,23)),(p[u],'first copy of u',(12,-18))]:
        ax.plot(*point,'o',color='#263b4c',markersize=4)
        ax.annotate(label,point,xytext=offset,textcoords='offset points',fontsize=10,
                    ha='right' if label in ('petal apex','last copy of u') else 'left',color='#263b4c')
    ax.text(91,36,'Opposite fan face',fontsize=11,color='#236691',ha='center')
    ax.text(-65,-21,'First petal',fontsize=11,color='#a65821',ha='center')
    ax.text(-110,49,'One ray passes through both interiors',fontsize=11,color='#5d485e')
    ax.set_xlim(-190,158);ax.set_ylim(-53,66);ax.set_aspect('equal');ax.axis('off')
    fig.suptitle('Shared directions, but no overlap',x=.055,ha='left',fontsize=17,fontweight='bold')
    fig.text(.055,.065,'The triangles occupy different distances along the dashed ray. All 28 face pairs of this net are exactly certified nonoverlapping.',fontsize=10,color='#44525d')
    fig.subplots_adjust(left=.025,right=.98,top=.9,bottom=.15)
    out=root/'figures/local-radial-failure';out.parent.mkdir(exist_ok=True)
    fig.savefig(out.with_suffix('.svg'));fig.savefig(out.with_suffix('.png'),dpi=150)
    svg=out.with_suffix('.svg');svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')
    plt.close(fig)


if __name__=='__main__':render()
