"""Illustrate the two retained Lemma F pairs; the figure is not a proof."""
from pathlib import Path

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon

from durer_small_n.octa import Octa


def render():
    o = Octa(np.array([[0,0,3],[0,0,-1],[1,0,0],[0,1,0],[-1,0,0],[0,-1,0]]), 0)
    net = o.Z(0)
    fig, axes = plt.subplots(1, 2, figsize=(11,5.4))
    for ax, petal, fan, title in [(axes[0],2,0,'Check 1: V₂ against W₀'),
                                  (axes[1],1,3,'Check 2: V₁ against W₃')]:
        for kind in ('W','V'):
            for t in range(4):
                selected = t == (petal if kind=='V' else fan)
                color = ('#eda460' if kind=='V' else '#7ab5df') if selected else '#eff1f2'
                edge = ('#a85d26' if kind=='V' else '#2e6a95') if selected else '#b6bec4'
                ax.add_patch(Polygon(net[kind,t], facecolor=color, edgecolor=edge,
                                     lw=1.8 if selected else .8, zorder=3 if selected else 1))
                if selected:
                    xy = net[kind,t].mean(axis=0)
                    ax.text(*xy,kind+str(t),ha='center',va='center',fontsize=12,weight='bold',zorder=4)
        for t,point_index in [(0,1),(3,2)]:
            endpoint = net['W',t][point_index]
            ax.plot([0,endpoint[0]],[0,endpoint[1]],color='#b34b53',lw=2,ls='--',zorder=5)
        ax.plot(0,0,'o',ms=4,color='#304556',zorder=6)
        ax.annotate('w',(0,0),xytext=(-11,-13),textcoords='offset points',fontsize=10)
        ax.set_title(title,fontsize=13,loc='left',pad=10)
        points=np.concatenate([net[k,t] for k in ('W','V') for t in range(4)])
        lo,hi=points.min(0),points.max(0)
        ax.set_xlim(lo[0]-.25,hi[0]+.25);ax.set_ylim(lo[1]-.3,hi[1]+.3)
        ax.set_aspect('equal');ax.axis('off')
    fig.suptitle('Two blue–orange checks now suffice',x=.04,ha='left',fontsize=17,weight='bold')
    fig.text(.04,.075,'If both checks pass: opposite petals are safe → interior fan triangles are safe → the whole net is safe.',
             fontsize=10,color='#364c5d')
    fig.text(.04,.035,'Dashed red: the two copies of the radial cut. Illustration shown with slit index 0; the universal two checks remain open.',
             fontsize=9,color='#53646f')
    fig.subplots_adjust(left=.04,right=.98,top=.85,bottom=.15,wspace=.13)
    out=Path(__file__).resolve().parent/'figures/lemma-F-two-pairs'
    fig.savefig(out.with_suffix('.svg'));fig.savefig(out.with_suffix('.png'),dpi=150)
    svg=out.with_suffix('.svg')
    svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')
    plt.close(fig)


if __name__ == '__main__':
    render()
