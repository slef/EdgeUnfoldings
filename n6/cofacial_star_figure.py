"""True-scale comparison of a shortest-path star and its two original-edge routes."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n6.certify import edge,tree_path
from n6.intervals import set_precision
from n6.low_curvature_examples import specification
from n6.polycert import Geometry


def main():
    set_precision(240);plt.rcParams.update({'svg.fonttype':'none','font.family':'DejaVu Sans'})
    spec=specification('minus');star=[[0,2],[0,3],[0,4],[0,5]]
    nets=[]
    for c in (2,3):
        g=Geometry({**spec,'cut_edges':star+[[1,c]]});net=[]
        for i,f in enumerate(g.faces):
            q=g.develop(tree_path(g.adj,2,i))
            net.append({v:np.array([float((x.lo+x.hi)/2) for x in q[v]]) for v in f})
        nets.append(net)
    ref=[([(0,3,1),nets[0][0]],'Q₂'), ([(0,2,1),nets[1][0]],'Q₁')]
    common=[([tuple(f),nets[0][i]],str(i)) for i,f in enumerate(spec['faces']) if i]
    panels=[ref+common, [([tuple(f),nets[0][i]],'Q' if i==0 else str(i)) for i,f in enumerate(spec['faces'])],
            [([tuple(f),nets[1][i]],'Q' if i==0 else str(i)) for i,f in enumerate(spec['faces'])]]
    titles=['Known nonoverlapping star','Original route via C','Original route via D']
    allp=np.array([p for panel in panels for (f,q),label in panel for p in q.values()])
    lo=allp.min(axis=0);hi=allp.max(axis=0);pad=.09*max(hi-lo)
    fig,axes=plt.subplots(1,3,figsize=(12,5.3));fig.patch.set_facecolor('#f7fafc')
    for k,(ax,panel,title) in enumerate(zip(axes,panels,titles)):
        for (f,q),label in panel:
            p=np.array([q[v] for v in f]);isq=label.startswith('Q')
            ax.add_patch(Polygon(p,facecolor='#e6b774' if isq else '#9bc6d9',edgecolor='#425d6a',lw=1))
            for a,b in zip(f,f[1:]+f[:1]):
                if 0 in (a,b) or (k>0 and edge(a,b)==(1,2 if k==1 else 3)):
                    z=np.array([q[a],q[b]]);ax.plot(z[:,0],z[:,1],color='#b44950',lw=1.7,
                              linestyle='--' if k==0 and edge(a,b)==(0,1) else '-')
            ax.text(*p.mean(axis=0),label,ha='center',va='center',fontsize=11,color='#243f4a',weight='bold' if isq else 'normal')
        ax.set_xlim(lo[0]-pad,hi[0]+pad);ax.set_ylim(lo[1]-pad,hi[1]+pad)
        ax.set_aspect('equal');ax.axis('off');ax.set_title(title,fontsize=12,color='#243f4a')
    fig.suptitle('Only the quadrilateral changes place',x=.04,y=.97,ha='left',fontsize=18,weight='bold',color='#253d4b')
    fig.text(.04,.89,'The six blue faces have exactly the same placement in all three developments.',fontsize=11,color='#405766')
    fig.text(.04,.065,'Left: the dashed diagonal splits Q. Right: Q stays whole, attached along one boundary edge.',fontsize=10.5,color='#405766')
    fig.text(.04,.025,'All panels use the same scale. This illustration is a rounded example; the reduction applies to every convex shape.',fontsize=10,color='#405766')
    fig.subplots_adjust(left=.035,right=.98,top=.79,bottom=.13,wspace=.08)
    path=Path(__file__).parent/'figures/cofacial-star-comparison.svg';fig.savefig(path,facecolor=fig.get_facecolor());plt.close(fig)
    path.write_text('\n'.join(line.rstrip() for line in path.read_text().splitlines())+'\n')


if __name__=='__main__':main()
