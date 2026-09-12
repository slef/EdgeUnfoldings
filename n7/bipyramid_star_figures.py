"""Schematic proof figures. Coordinates here are explanatory, not certificates."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon,Arc,FancyArrowPatch
ROOT=Path(__file__).resolve().parent

def e(a):return np.array([np.cos(a),np.sin(a)])
def add_triangle(ax,points,color,alpha=.55):
 ax.add_patch(Polygon(points,facecolor=color,edgecolor=color,linewidth=1.7,alpha=alpha))
def main(output=None):
 fig,axs=plt.subplots(1,2,figsize=(11.6,5.5));fig.patch.set_facecolor('#fbfaf6')
 for ax in axs:ax.set_aspect('equal');ax.axis('off');ax.set_facecolor('#fbfaf6')
 ax=axs[0];k=np.deg2rad(220);a=np.deg2rad(35);b=np.deg2rad(80);r=np.sin(b)/np.sin(np.pi-a-b);p=np.zeros(2);q0=e(0);q1=e(k);u=r*e(-a);up=r*e(k-a)
 xx,yy=np.meshgrid(np.linspace(-1.55,1.35,400),np.linspace(-1.12,1.55,400));ang=np.mod(np.arctan2(yy,xx),2*np.pi)
 mask=(ang<=k)&(xx<=1)&(xx*q1[0]+yy*q1[1]<=1)
 ax.contourf(xx,yy,mask.astype(int),levels=[.5,1.5],colors=['#dbece0'],alpha=.8)
 ax.add_patch(Arc(p,2,2,theta1=0,theta2=220,color='#5d9874',linestyle=':',linewidth=1.2))
 add_triangle(ax,[p,q0,u],'#4d87ba',.35);add_triangle(ax,[p,q1,up],'#d58924',.7)
 for q,t in((q0,e(np.pi/2)),(q1,e(k-np.pi/2))):
  end=q+1.7*t;ax.plot([0,q[0]],[0,q[1]],color='#204637',linewidth=1.8);ax.plot([q[0],end[0]],[q[1],end[1]],'--',color='#3b7655',linewidth=1.2)
 ax.add_patch(FancyArrowPatch(.60*e(-a/2),.60*e(k-a/2),connectionstyle='arc3,rad=1.1',arrowstyle='-|>',mutation_scale=14,color='#84601c',linewidth=1.5))
 for pt,label,offset in((p,'p',(6,4)),(q0,'q₀',(7,-2)),(q1,'q₁',(-4,-18)),(u,'u',(6,-8)),(up,"u′",(-18,-4))):
  ax.plot(*pt,'o',color='#21332d',markersize=3);ax.annotate(label,pt,xytext=offset,textcoords='offset points',fontsize=12)
 ax.text(-1.27,1.25,'Region already known empty',fontsize=11,color='#28553d')
 ax.text(-1.20,.85,'Curvature gap ≥ 180°',fontsize=11,color='#28553d')
 ax.text(.35,-.88,'Old half',fontsize=11,color='#38638b')
 ax.text(-1.40,-.88,'Moved half',fontsize=11,color='#975714')
 ax.set_xlim(-1.55,1.35);ax.set_ylim(-1.1,1.55);ax.set_title('A. The perpendicular empty region',fontsize=13,loc='left',pad=14,fontweight='bold')
 ax=axs[1];a=np.deg2rad(40);b=np.deg2rad(30);k=np.deg2rad(25);r=np.sin(b)/np.sin(np.pi-a-b);q0=e(0);q1=e(k);u=r*e(-a);up=r*e(k-a)
 th=np.linspace(0,k,80);ax.add_patch(Polygon(np.vstack([p,np.array([e(t) for t in th]),p]),facecolor='#dbece0',edgecolor='none'))
 add_triangle(ax,[p,q0,u],'#4d87ba',.35);add_triangle(ax,[p,q1,up],'#d58924',.55)
 ax.plot([0,q0[0]],[0,q0[1]],color='#37654b',linewidth=1.3);ax.plot([0,q1[0]],[0,q1[1]],color='#37654b',linewidth=1.3)
 for pt,label,offset in((p,'p',(-12,0)),(q0,'q₀',(8,-4)),(q1,'q₁',(6,2)),(u,'u',(0,-18)),(up,"u′",(-8,-18))):
  ax.plot(*pt,'o',color='#21332d',markersize=3);ax.annotate(label,pt,xytext=offset,textcoords='offset points',fontsize=12)
 ax.annotate('Ring corner ≥ 90°',u,xytext=(.03,-.59),textcoords='data',fontsize=11,color='#38638b',arrowprops={'arrowstyle':'-','color':'#38638b'})
 ax.annotate('New part enters\nthe empty sector',(.82,.17),xytext=(.28,.71),fontsize=11,color='#28553d',arrowprops={'arrowstyle':'-','color':'#28553d'})
 ax.text(-.06,-.84,'The part below pq₀ stays inside\nthe old half, which has been removed.',fontsize=11,color='#44504d',linespacing=1.5)
 ax.set_xlim(-.18,1.27);ax.set_ylim(-.94,.95);ax.set_title('B. A right or obtuse ring corner',fontsize=13,loc='left',pad=14,fontweight='bold')
 fig.text(.04,.055,'Schematic sufficient conditions. The final cut uses an original edge; the shortest-path cut is only a comparison.',fontsize=10,color='#485751')
 fig.subplots_adjust(left=.04,right=.98,top=.88,bottom=.17,wspace=.22)
 output=Path(output) if output else ROOT/'figures/bipyramid-star-replacement.svg';fig.savefig(output,facecolor=fig.get_facecolor());plt.close(fig)
if __name__=='__main__':main()
