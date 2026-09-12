"""Illustrate proved parameter restrictions and the exact collision example."""
from fractions import Fraction as F
import json,math
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n7.bipyramid_morph import ROOT,exact_points,morph_geometry,develop

def save(fig,name):
 p=ROOT/'figures'/name;fig.savefig(p,metadata={'Date':None},facecolor=fig.get_facecolor(),bbox_inches='tight',pad_inches=.16);plt.close(fig)
 p.write_text('\n'.join(line.rstrip() for line in p.read_text().splitlines())+'\n')

def gate_figure():
 fig,ax=plt.subplots(figsize=(6.7,5.6));fig.patch.set_facecolor('#f7f8f4');ax.set_facecolor('#dbece1')
 ax.add_patch(Polygon([(0,0),(180,0),(120,120),(0,180)],facecolor='#f2dfbd',edgecolor='#8c7350',linewidth=1.5))
 ax.plot([90,180],[180,0],color='#277a60',linewidth=1.5);ax.plot([0,180],[180,90],color='#277a60',linewidth=1.5)
 # Only the boundary segments of the residual region matter; the complete
 # lines show the two sufficient weighted-curvature tests.
 ax.text(153,151,'Proved\nreceiver gate',ha='center',fontsize=13,color='#1b6048')
 ax.text(66,63,'May still require\na metric argument',ha='center',fontsize=13,color='#77592d')
 ax.set_xlim(0,180);ax.set_ylim(0,180);ax.set_aspect('equal');ax.set_xticks([0,60,120,180]);ax.set_yticks([0,60,120,180]);ax.set_xlabel('Curvature at v (degrees)');ax.set_ylabel('Curvature at w (degrees)')
 ax.set_title('Both poles below 180°: three two-receiver patterns',loc='left',fontsize=12,pad=13)
 save(fig,'bipyramid-receiver-region.svg')

def collision_figure():
 row=json.loads((ROOT/'results/bipyramid-morph.json').read_text())['examples'][1];p=exact_points(row['points']);p0,_=morph_geometry(p,2,[1,3])
 def net(t):return [np.array([[x.mid() for x in q] for q in face]) for face in develop([[a+t*(b-a) for a,b in zip(q,r)] for q,r in zip(p0,p)],row['initial_cut'])]
 n=net(F(0));root=n[0];C=n[5][0];A=root[2];V=root[0];trace=np.array([net(F(i,100))[6][1] for i in range(101)]);contact=net(F(12520747,20000000))[6][1]
 fig,axes=plt.subplots(1,2,figsize=(10.3,4.8));fig.patch.set_facecolor('#f7f8f4')
 for i,ax in enumerate(axes):
  ax.set_facecolor('#f7f8f4');ax.add_patch(Polygon(root,facecolor='#edce90',edgecolor='#526873',alpha=.7));ax.plot(root[[2,0],0],root[[2,0],1],color='#8d3150',linewidth=2)
  ax.plot(trace[:,0],trace[:,1],color='#21805e',linewidth=2.2)
  if i==0:
   arc=np.linspace(math.atan2(trace[-1,1]-C[1],trace[-1,0]-C[0])-.08,math.atan2(A[1]-C[1],A[0]-C[0])+.06,150);r=np.linalg.norm(A-C);arc=C+r*np.c_[np.cos(arc),np.sin(arc)];ax.plot(arc[:,0],arc[:,1],color='#9aaaad',linestyle='--')
   ax.plot([C[0],A[0]],[C[1],A[1]],color='#a4afb2',linestyle=':');ax.plot([C[0],contact[0]],[C[1],contact[1]],color='#a4afb2',linestyle=':')
   for q,txt in[(C,'C = fan pole w'),(A,'A = fixed u₁'),(V,'V = fixed v')]:ax.plot(*q,'o',color='#314d59',markersize=4);ax.annotate(txt,q,xytext=(7,7),textcoords='offset points',fontsize=10)
   ax.set_xlim(-.15,1.3);ax.set_ylim(-.13,1.77);ax.set_title('A fixed circle and a fixed cut edge',fontsize=12,loc='left');ax.axis('off')
  else:
   for q,txt,offset,col in[(trace[0],'t = 0',(-25,25),'#21805e'),(contact,'first contact',(-20,40),'#284c8b'),(trace[-1],'t = 1: inside',(-105,-32),'#b32f50')]:
    ax.plot(*q,'o',color=col,markersize=5);ax.annotate(txt,q,xytext=offset,textcoords='offset points',fontsize=10,color=col,arrowprops={'arrowstyle':'->','color':col})
   center=trace.mean(axis=0);width=max(np.ptp(trace[:,0]),np.ptp(trace[:,1]))*1.45;ax.set_xlim(center[0]-width/2,center[0]+width/2);ax.set_ylim(center[1]-width/2,center[1]+width/2);ax.set_title('Magnified: the moving copy A′ enters the petal',fontsize=12,loc='left');ax.tick_params(labelsize=8);ax.set_xlabel('Developed x coordinate');ax.set_ylabel('Developed y coordinate')
  ax.set_aspect('equal')
 fig.tight_layout();save(fig,'bipyramid-first-collision.svg')

if __name__=='__main__':gate_figure();collision_figure()
