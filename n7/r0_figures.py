"""Draw an illustrative triangular bipyramid for the new local theorem.

The figure uses a separate rational example; it is not a numerical premise.
"""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n7.a992 import unfold
from n7.r0_identity import FACES
ROOT=Path(__file__).resolve().parent

def build():
    p=np.zeros((7,3));p[3]=(0,0,0);p[6]=(2,0,0);p[5]=(1,2,0)
    p[0]=(1,.3,.5);p[1]=(1,.7,-1)
    cut=((0,3),(0,5),(0,6),(1,3))
    n=unfold(p,cut,FACES,4)
    plt.rcParams.update({'font.family':'DejaVu Sans','svg.fonttype':'none','svg.hashsalt':'a992-r0-proof'})
    fig,ax=plt.subplots(figsize=(10,6.2));fig.patch.set_facecolor('#fafbf8');ax.set_facecolor('#fafbf8')
    colors={0:'#edb1a0',1:'#b8d5b1',3:'#b3d1df',4:'#b3d1df',5:'#d0c2e1'}
    for i in (3,4,5,1,0):
        poly=n[i];ax.add_patch(Polygon(poly,closed=True,facecolor=colors[i],edgecolor='#526b76',lw=1.5))
        center=poly.mean(axis=0)
        label={0:'E = 036',1:'Auxiliary 056',3:'136',4:'156',5:'Target 135'}[i]
        ax.text(*center,label,ha='center',va='center',fontsize=11,color='#233e4b')
    for i in (0,1):
        v=n[i][FACES[i].index(0)];c=n[i][FACES[i].index(6)]
        ax.plot([v[0],c[0]],[v[1],c[1]],color='#546b38',lw=2.6,ls=(0,(4,3)))
    labels=[(n[0][0],'0 in E',(0,-15)),(n[1][0],'0 in auxiliary face',(8,9)),
            (n[0][1],'3 first',(-13,9)),(n[5][2],'3 last',(9,-12)),
            (n[4][0],'1',(0,10)),(n[4][1],'6',(-12,-8)),(n[4][2],'5',(10,-7))]
    for xy,label,offset in labels:
        ax.plot(*xy,'o',color='#29434c',ms=4)
        ax.annotate(label,xy,xytext=offset,textcoords='offset points',fontsize=11,fontweight='bold',ha='center')
    pts=np.vstack([n[i] for i in colors]);span=np.ptp(pts,axis=0)
    ax.set_xlim(pts[:,0].min()-.17*span[0],pts[:,0].max()+.17*span[0]);ax.set_ylim(pts[:,1].min()-.17*span[1],pts[:,1].max()+.17*span[1])
    ax.set_aspect('equal');ax.axis('off')
    fig.suptitle('Two copies of edge 06 have exactly the same length',fontsize=17,fontweight='bold',color='#233e4b',y=.96)
    fig.text(.5,.045,'Blue and purple: the fan at 1. Green: a comparison triangle used only in the proof.',ha='center',fontsize=10,color='#52636c')
    fig.subplots_adjust(top=.86,bottom=.11,left=.04,right=.96)
    path=ROOT/'figures/a992-r0-comparison.svg';fig.savefig(path,metadata={'Date':None})
    path.write_text('\n'.join(line.rstrip() for line in path.read_text().splitlines())+'\n')
    plt.close(fig)

if __name__=='__main__':build()
