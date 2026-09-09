"""Illustrate exactly checked fixed-tree failures; pictures are not certificates."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Rectangle
from n6.polycert import Geometry, verify_overlap
from n6.certify import tree_path

ROOT = Path(__file__).resolve().parent


def clip_polygon(subject, boundary):
    """Floating clipping used only to place the zoom window and illustration."""
    out = np.asarray(subject)
    for a, b in zip(boundary, np.roll(boundary, -1, axis=0)):
        if not len(out):
            break
        edge = b-a
        def side(p): return edge[0]*(p-a)[1]-edge[1]*(p-a)[0]
        new = []
        for p, q in zip(out, np.roll(out, -1, axis=0)):
            sp, sq = side(p), side(q)
            if sp >= 0: new.append(p)
            if (sp < 0) != (sq < 0): new.append(p+(q-p)*sp/(sp-sq))
        out = np.asarray(new)
    return out


def render(stem, title, labels, output):
    cert = json.loads((ROOT/'results'/f'{stem}.certificate.json').read_text())
    verify_overlap(cert)
    g = Geometry(cert)
    def midpoint(q): return float((q.lo+q.hi)/2)
    polygons = []
    for f in range(len(g.faces)):
        positions = g.develop(tree_path(g.adj, 0, f))
        polygons.append(np.array([[midpoint(q) for q in positions[v]] for v in g.faces[f]]))
    a,b = cert['overlap_witness']['faces']
    overlap = clip_polygon(polygons[a], polygons[b])
    if len(overlap) < 3: raise ValueError('Illustration could not resolve certified overlap')
    lo,hi = overlap.min(axis=0),overlap.max(axis=0)
    center = (lo+hi)/2; half = max(hi-lo)*.8
    fig, axes = plt.subplots(1,2,figsize=(11,5),gridspec_kw={'width_ratios':[1.2,1]})
    for ax in axes:
        for f, p in enumerate(polygons):
            color = '#2878b5' if f == a else '#d26b32' if f == b else '#dce3e9'
            ax.add_patch(Polygon(p,facecolor=color,alpha=.34,edgecolor='#263b4c',linewidth=1))
        ax.add_patch(Polygon(overlap,facecolor='#a71930',edgecolor='#a71930',alpha=.8))
        ax.set_aspect('equal');ax.axis('off')
    for f,p in enumerate(polygons):
        c=p.mean(axis=0)
        axes[0].text(*c,labels[f],ha='center',va='center',fontsize=11,fontweight='bold')
    axes[0].relim();axes[0].autoscale_view();axes[0].margins(.12)
    axes[0].add_patch(Rectangle(center-half,2*half,2*half,fill=False,edgecolor='#a71930',linestyle='--'))
    axes[0].set_title('Specified unfolding',loc='left',fontsize=12)
    axes[1].set_xlim(center[0]-half,center[0]+half)
    axes[1].set_ylim(center[1]-half,center[1]+half)
    axes[1].set_title(f'Overlap of {labels[a]} and {labels[b]} — enlarged',loc='left',fontsize=12)
    fig.suptitle(title,x=.05,ha='left',fontsize=16,fontweight='bold')
    fig.text(.05,.035,'The red region has positive area, certified by exact rational bounds. The drawing is illustrative.',fontsize=10,color='#44525d')
    fig.subplots_adjust(left=.04,right=.97,bottom=.11,top=.83,wspace=.08)
    output.parent.mkdir(parents=True,exist_ok=True)
    fig.savefig(output.with_suffix('.svg'))
    svg = output.with_suffix('.svg')
    svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')
    fig.savefig(output.with_suffix('.png'),dpi=160)
    plt.close(fig)


def main():
    out=ROOT/'figures'
    render('thesis-chart-DF',"DiBiase's displayed tree: a certified DF overlap",
           ['root','A','B','C','D','E','F','G'],out/'thesis-DF')
    render('prism-two-pair-failure','Prism with one diagonal: the two-pair tree can fail',
           ['base','Q1','T2','Q3','T4','top'],out/'prism-two-pair')
    print('Rendered two exact-witness illustrations in',out)


if __name__ == '__main__': main()
