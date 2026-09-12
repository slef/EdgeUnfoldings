"""Two exact-geometry schematics of the radial proof; drawings are illustrative."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon,Circle
ROOT=Path(__file__).resolve().parent

def figure():
 a=np.array([0.,0.]);P=np.array([1.,0.]);F=np.array([.9,1.3]);k=np.pi/6;M=np.array([np.cos(k),np.sin(k)]);b=np.array([.89,.9]);db=np.linalg.norm(F-b)+np.linalg.norm(M-b)
 rot=np.array([[np.cos(k),np.sin(k)],[-np.sin(k),np.cos(k)]]);Fp=rot@F;bp=rot@b
 fig,axs=plt.subplots(1,2,figsize=(12,7.1));fig.patch.set_facecolor('#fbfaf6')
 for ax in axs:ax.set_aspect('equal');ax.axis('off')
 ax=axs[0];ax.add_patch(Circle(F,db,facecolor='#dbe9f1',edgecolor='#5d8fa5',lw=1.5,alpha=.75));ax.add_patch(Polygon([a,F,P],fill=False,edgecolor='#ad884e',linestyle='--',lw=1.7));ax.add_patch(Polygon([F,a,b],facecolor='#b1cfdf',edgecolor='#4c758a',lw=1.4));ax.add_patch(Polygon([M,a,b],facecolor='#cbe0c6',edgecolor='#4b7551',lw=1.4));ax.add_patch(Polygon([[-.75,-.33],a,P],facecolor='#e7b48b',edgecolor='#a96e41',lw=1.2));ax.plot([0,1],[0,0],color='#ab4141',lw=2.5)
 for z,label,off in((a,'a',(-16,-9)),(P,'P',(8,-8)),(F,'f',(-4,10)),(M,'M',(9,-3)),(b,'b',(9,0))):
  ax.plot(*z,'o',ms=4,color='#24424c');ax.annotate(label,z,xytext=off,textcoords='offset points',fontsize=13)
 ax.text(-.8,2.3,'A. View from the long-extension pole',fontsize=13,fontweight='bold');ax.text(-.8,-1.08,'The protrusion stays outside the disk.\nThe far-vertex distance sum sets its radius.',fontsize=11,color='#41565e');ax.set_xlim(-.9,2.05);ax.set_ylim(-1.3,2.5)
 ax=axs[1];gamma=np.arctan2(*(F-P)[::-1]);angles=np.linspace(gamma,np.pi,40);cone=np.vstack([P,P+1.15*np.c_[np.cos(angles),np.sin(angles)]])
 ax.add_patch(Polygon(cone,facecolor='#e9ddf0',edgecolor='#9c75ad',alpha=.7,lw=1.4));ax.add_patch(Circle(P,db,facecolor='#dbe9f1',edgecolor='#5d8fa5',alpha=.7,lw=1.4));ax.add_patch(Polygon([P,a,bp],facecolor='#b1cfdf',edgecolor='#4c758a',lw=1.4));ax.add_patch(Polygon([Fp,a,bp],facecolor='#cbe0c6',edgecolor='#4b7551',lw=1.4));ax.plot([P[0],F[0]],[P[1],F[1]],linestyle='--',color='#9c75ad',lw=1.8)
 for z,label,off in((a,'a',(-15,-8)),(P,'q',(7,-15)),(Fp,"f′",(8,0)),(bp,"b′",(8,-8))):
  ax.plot(*z,'o',ms=4,color='#24424c');ax.annotate(label,z,xytext=off,textcoords='offset points',fontsize=13)
 ax.text(-.25,2.3,'B. View from the other pole',fontsize=13,fontweight='bold');ax.text(-.25,1.78,'Purple: the bad patch’s cone\nBlue: the same distance-sum disk',fontsize=11,color='#41565e');ax.text(-.25,-1.08,'Together they cover the entire receiver.\nA distant bad patch misses both parts.',fontsize=11,color='#41565e');ax.set_xlim(-.35,2.6);ax.set_ylim(-1.3,2.5)
 fig.subplots_adjust(left=.035,right=.985,bottom=.03,top=.99,wspace=.17);fig.savefig(ROOT/'figures/bipyramid-radial.svg',facecolor=fig.get_facecolor());plt.close(fig)
if __name__=='__main__':figure()
