"""A planar, true-scale illustration of the wider Case A separating line."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon,Arc


def main():
    plt.rcParams.update({'svg.fonttype':'none','font.family':'DejaVu Sans'})
    u=np.array([0.,0.]);up=np.array([1.,0.]);root=np.sqrt(.5)
    P=.3*np.array([root,root]);Q=up+.8*np.array([-root,root]);meet=np.array([.5,.5])
    M=np.array([.225,np.sqrt(.3**2-.225**2)])
    fig,ax=plt.subplots(figsize=(9.5,6.5));fig.patch.set_facecolor('#f7fafc')
    for p,color in [(np.array([u,up,M]),'#dbe4e8'),(np.array([u,P,P+[0,.34]]),'#e3b16b'),
                    (np.array([up,Q,Q+[.34,0]]),'#b6a0cf')]:
        ax.add_patch(Polygon(p,facecolor=color,edgecolor='#435c6a',lw=1.5))
    ax.plot([0,.7],[0,.7],ls=':',color='#7c8e98',lw=1.5)
    ax.plot([1,.3],[0,.7],ls=':',color='#7c8e98',lw=1.5)
    ax.axvline(P[0],color='#2f856b',ls='--',lw=2)
    for p,label,offset in [(u,'u',(-.04,-.03)),(up,"u′",(.015,-.025)),(M,'M',(.015,-.045)),
                            (P,'P',(-.045,.015)),(Q,'Q',(-.045,.035)),(meet,'ray intersection',(.035,-.025))]:
        ax.plot(*p,'o',ms=4,color='#284553');ax.text(*(p+offset),label,fontsize=12,color='#284553')
    ax.add_patch(Arc(P,.12,.12,theta1=90,theta2=225,color='#8a5629',lw=1.2))
    ax.text(-.035,.59,'Short side\nangle 135°',fontsize=12,color='#875221',ha='center')
    ax.annotate('',P+[0,.05],(-.02,.56),arrowprops=dict(arrowstyle='-',color='#875221'))
    ax.text(.22,.745,'Separating line',fontsize=12,color='#2f856b',ha='center')
    ax.text(.765,.61,'Other face',fontsize=12,color='#705189')
    ax.text(.55,.07,'Middle triangle',fontsize=11,color='#526874')
    ax.set_xlim(-.18,1.08);ax.set_ylim(-.065,.80);ax.set_aspect('equal');ax.axis('off')
    fig.suptitle('A short side can tolerate an obtuse apex',x=.045,y=.97,ha='left',fontsize=18,weight='bold',color='#253d4b')
    fig.text(.045,.90,'Here θ = 90°, so the new bound is (180° + θ) / 2 = 135°.',fontsize=11.5,color='#405766')
    fig.text(.045,.065,'P stops before the rays meet; Q passes their meeting point. The green line still separates the faces.',fontsize=10.5,color='#405766')
    fig.text(.045,.025,'Planar proof illustration, with no stretching. This is not presented as a six-vertex polyhedron.',fontsize=10,color='#405766')
    fig.subplots_adjust(left=.05,right=.97,top=.84,bottom=.12)
    path=Path(__file__).parent/'figures/case-A-wide-cones.svg';fig.savefig(path,facecolor=fig.get_facecolor());plt.close(fig)
    path.write_text('\n'.join(line.rstrip() for line in path.read_text().splitlines())+'\n')


if __name__=='__main__':main()
