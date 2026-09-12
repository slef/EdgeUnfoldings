"""Scientific illustrations and 101 display frames, never proof predicates."""
from pathlib import Path
import json,math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n7.a992 import unfold
from n7.bipyramid_morph import FACES,cut_at
ROOT=Path(__file__).resolve().parent
BASE=[[-2,-1,0],[.2,-1.2,0],[2,0,0],[.7,1.4,0],[-1.5,1,0]]
CENTER=[.3,.1]

def geometry(h,H):
 p=np.array(BASE+[CENTER+[h],CENTER+[-H]],float);k=0;n=unfold(p,cut_at(6,k),FACES,0);O=n[k][0]
 boundary=np.array([n[(k+i)%5][1] for i in range(5)]+[n[(k+4)%5][2]])
 angles=[]
 for i in range(5):
  a=p[i]-p[5];b=p[(i+1)%5]-p[5];angles.append(math.atan2(np.linalg.norm(np.cross(a,b)),a@b))
 gap=2*math.pi-sum(angles);return p,n,O,boundary,gap

def figure(output=None):
 fig,axs=plt.subplots(1,2,figsize=(11,5.8));fig.patch.set_facecolor('#fbfaf6')
 for ax,(h,H),title in zip(axs,[(1.3,1.3),(3,5)],['A. Small curvature: fill the missing triangle','B. Large curvature: the fan is already convex']):
  p,n,O,boundary,gap=geometry(h,H)
  for i in range(5):
   ax.add_patch(Polygon(n[i],facecolor='#bfd7e4',edgecolor='#4c6e80',linewidth=1.1));c=n[i].mean(axis=0);ax.text(*c,'W'+str(i),ha='center',va='center',fontsize=11,color='#254e63')
  if gap<math.pi:
   B=boundary;ax.add_patch(Polygon([O,boundary[0],boundary[-1]],facecolor='#e5c27f',edgecolor='#9f7529',linewidth=1.2));d=np.array([O,boundary[0],boundary[-1]]).mean(axis=0);ax.text(*d,'Added\ntriangle',fontsize=10,ha='center',va='center',color='#6e4d19')
  else:B=np.vstack([O,boundary])
  ax.add_patch(Polygon(B,fill=False,edgecolor='#285c41',linewidth=2.3));ax.plot(*O,'o',color='#1c5b77',markersize=5);ax.annotate('P',O,xytext=(-15,-8),textcoords='offset points',fontsize=12,color='#154c65')
  for U,label in((boundary[0],'u₀⁻'),(boundary[-1],'u₀⁺')):
   ax.plot(*U,'o',color='#1c5b77',markersize=4);ax.annotate(label,U,xytext=(7,-16),textcoords='offset points',fontsize=10)
  ax.autoscale_view();ax.margins(.20);ax.set_aspect('equal');ax.axis('off');ax.set_title('',fontsize=12)
  fig.text(.045 if h<2 else .535,.15,'Convex boundary in green · pole curvature ≈ '+str(round(gap*180/math.pi))+'°',fontsize=10,color='#3e5c4c')
 fig.text(.045,.92,'A. Small curvature: fill the missing triangle',fontsize=12,fontweight='bold')
 fig.text(.535,.92,'B. Large curvature: the fan is already convex',fontsize=12,fontweight='bold')
 fig.text(.04,.055,'The auxiliary pyramid stands on this convex polygon. Its lateral triangles have exactly the original petal lengths.',fontsize=10,color='#44534c')
 fig.subplots_adjust(left=.045,right=.96,top=.86,bottom=.20,wspace=.23)
 output=Path(output) if output else ROOT/'figures/bipyramid-aligned-completion.svg';fig.savefig(output,facecolor=fig.get_facecolor());plt.close(fig)

def demo(output=None):
 H=5.;target=3.;frames=[]
 for i in range(101):
  p,n,O,boundary,gap=geometry(target*i/100,H)
  B=boundary if gap<math.pi else np.vstack([O,boundary]);frames.append({'points':p.tolist(),'net':[x.tolist() for x in n],'fan_center':O.tolist(),'boundary':boundary.tolist(),'completion':B.tolist(),'gap':gap,'added':gap<math.pi})
 data={'faces':FACES,'cuts':cut_at(6,0),'height':target,'source_height':H,'frames':frames,'scope':'Rounded illustration only. A written theorem proves the entire height interval.'}
 template=(ROOT/'aligned-demo-template.html').read_text();output=Path(output) if output else ROOT/'bipyramid-aligned-demo.html';output.write_text(template.replace('ALIGNED_DATA',json.dumps(data,separators=(',',':'))))
if __name__=='__main__':figure();demo()
