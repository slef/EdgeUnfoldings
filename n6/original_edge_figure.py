"""True-scale original-face nets illustrating the new curvature theorem."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n6.certify import edge,tree_path
from n6.intervals import set_precision
from n6.original_edge_examples import specification
from n6.polycert import Geometry


def main():
    set_precision(240);plt.rcParams.update({'svg.fonttype':'none','font.family':'DejaVu Sans'})
    fig,axes=plt.subplots(1,2,figsize=(11,5.8));fig.patch.set_facecolor('#f7fafc')
    for ax,kind,title,slit in zip(axes,['minus','prism'],['Octahedron minus an edge','Prism with one diagonal'],[(1,2),(2,5)]):
        spec=specification(kind);g=Geometry(spec);cuts=set(map(tuple,spec['cut_edges']))
        for i,f in enumerate(g.faces):
            q=g.develop(tree_path(g.adj,0,i))
            points={v:np.array([float((x.lo+x.hi)/2) for x in q[v]]) for v in f}
            p=np.array([points[v] for v in f])
            ax.add_patch(Polygon(p,facecolor='#a0c9dd' if len(f)==4 else '#ecd0aa',edgecolor='#566a76',lw=.9))
            for a,b in zip(f,f[1:]+f[:1]):
                if edge(a,b) in cuts:
                    x=np.array([points[a],points[b]])
                    ax.plot(x[:,0],x[:,1],color='#ab6900' if edge(a,b)==slit else '#b75151',lw=2)
            center=p.mean(axis=0)
            ax.text(*center,'Q' if len(f)==4 else 'T'+str(i),fontsize=10,ha='center',va='center',color='#253d4b')
        ax.relim();ax.autoscale_view();ax.margins(.10);ax.set_aspect('equal');ax.axis('off')
        ax.set_title(title,fontsize=13,color='#253d4b',pad=12)
    fig.suptitle('Put the sharp vertex at the fifth cut',x=.045,y=.97,ha='left',fontsize=17,weight='bold',color='#253d4b')
    fig.text(.045,.90,'Two new proved families whose four-cut sources have curvature below 180°.',fontsize=11,color='#405766')
    fig.text(.045,.065,'Blue quadrilaterals stay whole. Red: source cuts. Gold: the fifth cut. Each net preserves its shape.',fontsize=10,color='#405766')
    fig.text(.045,.025,'The drawings illustrate exact examples; the geometric inequalities prove the families.',fontsize=10,color='#405766')
    fig.subplots_adjust(left=.045,right=.97,top=.79,bottom=.13,wspace=.17)
    path=Path(__file__).parent/'figures/original-rule-families.svg';fig.savefig(path,facecolor=fig.get_facecolor());plt.close(fig)
    path.write_text('\n'.join(line.rstrip() for line in path.read_text().splitlines())+'\n')


if __name__=='__main__':main()
