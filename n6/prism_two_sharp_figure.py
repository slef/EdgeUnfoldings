"""Actual original-face net for the two-sharp-end theorem; no geometric stretching."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n6.certify import edge,tree_path
from n6.polycert import Geometry
from n6.prism_two_sharp_ends import specification


def main():
    plt.rcParams.update({'svg.fonttype':'none','font.family':'DejaVu Sans'})
    spec=specification();g=Geometry(spec);cuts=set(map(tuple,spec['cut_edges']))
    fig,ax=plt.subplots(figsize=(8.8,6.3));fig.patch.set_facecolor('#f7fafc')
    for i,f in enumerate(g.faces):
        q=g.develop(tree_path(g.adj,2,i))
        points={v:np.array([float((x.lo+x.hi)/2) for x in q[v]]) for v in f}
        p=np.array([points[v] for v in f]);color='#9bc7dd' if i in (1,3) else '#edc189' if i in (0,5) else '#e2e8e8'
        ax.add_patch(Polygon(p,facecolor=color,edgecolor='#4b6572',lw=1.25))
        for a,b in zip(f,f[1:]+f[:1]):
            if edge(a,b) in cuts:
                line=np.array([points[a],points[b]]);ax.plot(line[:,0],line[:,1],color='#af4850',lw=2)
        center=p.mean(axis=0);ax.text(*center,'ABCDEF'[i],fontsize=17,ha='center',va='center',color='#233e4c',weight='bold')
    ax.relim();ax.autoscale_view();ax.margins(.12);ax.set_aspect('equal');ax.axis('off')
    fig.suptitle('Two sharp ends: the two-pair net always works',x=.045,y=.97,ha='left',fontsize=17,weight='bold',color='#253d4b')
    fig.text(.045,.90,'Cut all edges at 2 and 5. Only the gold pair A/F and blue pair B/D need a proof.',fontsize=10.5,color='#405766')
    fig.text(.045,.065,'The central faces C/E stay joined. Red boundaries are original cut edges.',fontsize=10.5,color='#405766')
    fig.text(.045,.025,'This exact example illustrates the theorem for κ₂ ≥ 180° and κ₅ ≥ 180°; equality is included.',fontsize=10,color='#405766')
    fig.subplots_adjust(left=.045,right=.97,top=.83,bottom=.12)
    path=Path(__file__).parent/'figures/prism-two-sharp-ends.svg';fig.savefig(path,facecolor=fig.get_facecolor());plt.close(fig)
    path.write_text('\n'.join(line.rstrip() for line in path.read_text().splitlines())+'\n')


if __name__=='__main__':main()
