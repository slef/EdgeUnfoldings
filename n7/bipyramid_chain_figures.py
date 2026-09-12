"""Planar proof schematic. Coordinates illustrate the pocket, not a full polyhedron."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon,Arc
ROOT=Path(__file__).resolve().parent

def figure():
 a=np.array([0.,0.]);P=np.array([1.,0.]);p=np.array([.9,1.8]);M=np.array([np.cos(np.deg2rad(50)),np.sin(np.deg2rad(50))]);b=np.array([.85,1.35])
 fig,ax=plt.subplots(figsize=(9,6.5));fig.patch.set_facecolor('#fbfaf6')
 ax.add_patch(Polygon([a,p,P],facecolor='#f2e1bd',edgecolor='#b68b43',linewidth=1.7,linestyle='--'))
 ax.add_patch(Polygon([p,a,b],facecolor='#bed9e7',edgecolor='#537d92',linewidth=1.7))
 ax.add_patch(Polygon([M,a,b],facecolor='#c9e0c4',edgecolor='#4a7956',linewidth=1.7))
 ax.plot([a[0],P[0]],[a[1],P[1]],color='#b64545',lw=2.8)
 ax.plot([a[0],M[0]],[a[1],M[1]],color='#b64545',lw=2.8)
 ax.plot([P[0],M[0]],[P[1],M[1]],color='#776650',lw=1.5,linestyle=':')
 ax.add_patch(Arc(a,.5,.5,theta1=0,theta2=50,color='#8c3c39',lw=1.4));ax.text(.31,.09,r'$\kappa_a$',fontsize=15,color='#8c3c39')
 for z,label,off in((a,'a',(-16,-10)),(P,'P',(9,-8)),(p,'p',(4,10)),(M,'M',(9,-2)),(b,'b',(8,0))):
  ax.plot(*z,'o',color='#243f45',ms=4);ax.annotate(label,z,xytext=off,textcoords='offset points',fontsize=15,fontweight='bold')
 ax.annotate('Fan triangle',(.38,.75),xytext=(-.7,1.1),arrowprops={'arrowstyle':'-','color':'#537d92'},fontsize=12,color='#315f74')
 ax.annotate('Receiver petal',(.60,.88),xytext=(1.22,1.12),arrowprops={'arrowstyle':'-','color':'#4a7956'},fontsize=12,color='#355f3f')
 ax.annotate('Same cut edge,\ntwo copies',(.6,0),xytext=(1.15,.2),arrowprops={'arrowstyle':'-','color':'#b64545'},fontsize=12,color='#8c3c39')
 ax.text(-.70,1.95,'A long extension traps its receiver inside a triangle',fontsize=15,fontweight='bold')
 ax.text(-.70,-.30,r'$|aP|=|aM|$  and  $M$ is strictly inside $apP$.',fontsize=14)
 ax.text(-.70,-.50,r'Therefore $\angle aPp > (\pi-\kappa_a)/2$.',fontsize=14)
 ax.set_xlim(-.8,2.4);ax.set_ylim(-.62,2.1);ax.set_aspect('equal');ax.axis('off');fig.tight_layout()
 fig.savefig(ROOT/'figures/bipyramid-chain-pocket.svg',facecolor=fig.get_facecolor());plt.close(fig)
if __name__=='__main__':figure()
