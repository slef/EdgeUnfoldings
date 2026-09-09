"""Illustrate the exactly checked need to switch between the two candidate nets."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n6.polycert import Geometry,verify,verify_overlap
from n6.certify import tree_path
from n6.minus_pair import FACE_NAMES
from n6.render_witnesses import clip_polygon

ROOT=Path(__file__).resolve().parent


def render():
    fig,axes=plt.subplots(1,2,figsize=(12,5.5))
    for ax,apex,fan in zip(axes,('P','Q'),({0,1,6},{0,3,4})):
        cert=json.loads((ROOT/'results'/f'minus-pair-{apex}.certificate.json').read_text())
        (verify_overlap if apex=='P' else verify)(cert)
        g=Geometry(cert);polys=[]
        for fi,f in enumerate(g.faces):
            q=g.develop(tree_path(g.adj,0,fi))
            polys.append(np.array([[float((x.lo+x.hi)/2) for x in q[v]] for v in f]))
        for fi,p in enumerate(polys):
            ax.add_patch(Polygon(p,facecolor='#8fc1dd' if fi in fan else '#e6af78',
                                 alpha=.5,edgecolor='#293b4a',linewidth=.85))
            center=p.mean(axis=0)
            ax.text(*center,FACE_NAMES[fi],fontsize=8,ha='center',va='center',color='#142b3c')
        if apex=='P':
            a,b=cert['overlap_witness']['faces'];overlap=clip_polygon(polys[a],polys[b])
            ax.add_patch(Polygon(overlap,facecolor='#af2443',alpha=.85,edgecolor='#af2443'))
        ax.relim();ax.autoscale_view();ax.margins(.12);ax.set_aspect('equal');ax.axis('off')
        ax.set_title(f'Cut at {apex}: '+('fails on this shape' if apex=='P' else 'works on the same shape'),loc='left',fontsize=14)
    fig.suptitle('Two candidate unfoldings; the choice matters',x=.04,ha='left',fontsize=18,fontweight='bold')
    fig.text(.04,.055,'Each color is one uncut vertex fan, so faces of that color cannot overlap.',fontsize=11)
    fig.text(.04,.018,'The red overlap on the left and all 21 nonoverlap checks on the right are certified exactly.',fontsize=10,color='#40515e')
    fig.subplots_adjust(left=.03,right=.98,top=.85,bottom=.14,wspace=.12)
    out=ROOT/'figures/minus-pair-switch'
    fig.savefig(out.with_suffix('.svg'));fig.savefig(out.with_suffix('.png'),dpi=140)
    svg=out.with_suffix('.svg');svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')
    plt.close(fig)


if __name__=='__main__':render()
