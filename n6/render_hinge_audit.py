"""Draw the exactly checked slit-boundary counterexample; pixels are illustrative."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n6.hinge_audit import verify
from n6.polycert import Geometry,tree_path
from n6.intervals import set_precision
from durer_small_n.octa import clip_convex
ROOT=Path(__file__).resolve().parent

def render():
 set_precision(240);s=json.loads((ROOT/'results/hinge-boundary-counterexample.certificate.json').read_text());verify(s);g=Geometry(s)
 xy=lambda q:np.array([float((a.lo+a.hi)/2) for a in q])
 nets=[g.develop(tree_path(g.adj,0,i)) for i in range(8)]
 raw=np.array([xy(q[v]) for q in nets for v in q]);_,_,V=np.linalg.svd(raw-raw.mean(axis=0),full_matrices=False);R=V.T
 if np.linalg.det(R)<0:R[:,1]*=-1
 pol=[np.array([xy(q[v])@R for v in f]) for q,f in zip(nets,g.faces)]
 w,u=xy(nets[0][1])@R,xy(nets[0][2])@R
 cross=clip_convex(pol[0],pol[6]);fig,axes=plt.subplots(1,2,figsize=(12,4.7),gridspec_kw=dict(width_ratios=[1.15,1]))
 for k,ax in enumerate(axes):
  for i,T in enumerate(pol):
   if k and i not in (0,6):continue
   color='#61a9d3' if i==0 else '#e89a52' if i==6 else '#dce5eb'
   ax.add_patch(Polygon(T,facecolor=color,edgecolor='#415366',alpha=.72,linewidth=.9))
  ax.add_patch(Polygon(cross,facecolor='#b92346',edgecolor='#b92346',alpha=.8,hatch='///'))
  ax.plot(*np.array([w,u]).T,color='#b92346',ls='--',lw=1.8)
  ax.set_aspect('equal');ax.axis('off')
  if k:
   lo=pol[0].min(axis=0);hi=pol[0].max(axis=0);span=hi-lo;margin=.2*max(span)
   ax.set_xlim(lo[0]-margin,hi[0]+margin);ax.set_ylim(lo[1]-margin,hi[1]+margin)
   ax.annotate('cut edge w–u0',(w+u)/2,xytext=(20,35),textcoords='offset points',fontsize=11,color='#8f1736',arrowprops=dict(arrowstyle='->',color='#8f1736'))
   ax.annotate('positive-area overlap',cross.mean(axis=0),xytext=(-75,-35),textcoords='offset points',fontsize=10,color='#8f1736',arrowprops=dict(arrowstyle='->',color='#8f1736'))
   for label,pos in [('w',w),('u0',u)]:ax.annotate(label,pos,xytext=(3,5),textcoords='offset points',fontsize=11)
  else:ax.relim();ax.autoscale_view();ax.margins(.06)
 axes[0].set_title('The whole net: 27 pairs are safe',loc='left',fontsize=14)
 axes[1].set_title('V2 enters W0 through the cut',loc='left',fontsize=13)
 fig.suptitle('A cut boundary is not an interior hinge',x=.04,ha='left',fontsize=18,fontweight='bold')
 fig.text(.04,.045,'Blue: W0. Orange: V2. Red: their overlap. The source v is not the sharpest vertex.',fontsize=11,color='#344659')
 fig.subplots_adjust(left=.04,right=.97,bottom=.14,top=.82,wspace=.18)
 stem=ROOT/'figures/hinge-boundary-counterexample';fig.savefig(stem.with_suffix('.svg'));fig.savefig(stem.with_suffix('.png'),dpi=140);plt.close(fig)
 p=stem.with_suffix('.svg');p.write_text('\n'.join(x.rstrip() for x in p.read_text().splitlines())+'\n')
if __name__=='__main__':render()
