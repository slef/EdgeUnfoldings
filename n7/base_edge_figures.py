"""Schematic base-edge regimes; dimensions are illustrative, not proof data."""
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
ROOT=Path(__file__).resolve().parent

def build():
    plt.rcParams.update({'font.family':'DejaVu Sans','svg.fonttype':'none','svg.hashsalt':'n7-base-edges'})
    fig,axes=plt.subplots(1,3,figsize=(12,5.2));fig.patch.set_facecolor('#fafbf8')
    cases=[('Converging',(.7,.65),(.3,.65),'Proved', '#286449'),
           ('Parallel',(1,.65),(0,.65),'Proved', '#286449'),
           ('Diverging',(1.3,.65),(-.3,.65),'Still open', '#986317')]
    for ax,(title,U,V,status,col) in zip(axes,cases):
        C=(1,0);D=(0,0)
        ax.set_facecolor('#fafbf8')
        if title=='Converging':
            x=(.5,13/12)
            ax.add_patch(Polygon([C,x,D],closed=True,fc='#dfebda',ec='none',alpha=.7))
            ax.plot([C[0],x[0],D[0]],[C[1],x[1],D[1]],'--',color='#5e775b',lw=1.7)
            ax.plot(*x,'o',color='#286449',ms=4);ax.annotate('x',x,xytext=(0,10),textcoords='offset points',ha='center',weight='bold',fontsize=13)
        else:
            for a,b in ((C,U),(D,V)):
                z=(a[0]+1.8*(b[0]-a[0]),a[1]+1.8*(b[1]-a[1]))
                ax.plot([a[0],z[0]],[a[1],z[1]],'--',color='#778795',lw=1.7)
        ax.add_patch(Polygon([C,U,V,D],closed=True,fc='#b9d3df',ec='#3f6070',lw=1.5))
        for a,b in ((C,U),(D,V)):ax.plot([a[0],b[0]],[a[1],b[1]],color='#286e91',lw=3)
        for xy,lab,off in ((C,'6',(9,-10)),(D,'2',(-9,-10)),(U,'1',(11,0)),(V,'5',(-11,0))):
            ax.plot(*xy,'o',ms=4,color='#294653');ax.annotate(lab,xy,xytext=off,textcoords='offset points',fontsize=12,weight='bold',ha='center')
        ax.text(.5,.31,'B',ha='center',color='#315466',fontsize=13)
        ax.set_title(title,color='#233e4b',fontsize=16,weight='bold',pad=14)
        ax.text(.5,-.16,status,transform=ax.transAxes,ha='center',fontsize=13,color=col,weight='bold')
        ax.set_xlim(-.65,1.65);ax.set_ylim(-.13,1.4);ax.set_aspect('equal');ax.axis('off')
    fig.suptitle('Extend the two base hinges',fontsize=19,weight='bold',color='#233e4b',y=.97)
    fig.text(.5,.05,'Status assumes the angle at 0 in E is at least 90°. R0 guarantees this.',ha='center',fontsize=11,color='#52636c')
    fig.subplots_adjust(top=.81,bottom=.2,wspace=.1,left=.03,right=.97)
    path=ROOT/'figures/a992-base-edge-regimes.svg';fig.savefig(path,metadata={'Date':None})
    path.write_text('\n'.join(line.rstrip() for line in path.read_text().splitlines())+'\n');plt.close(fig)
if __name__=='__main__':build()
