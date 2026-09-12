"""Illustrative geometry for a written theorem, not proof by plotting."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon,Arc
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from n7.bipyramid_morph import support,exact_points,FACES
ROOT=Path(__file__).resolve().parent
def figure():
 pts=np.array([[2,0,0],[1,2,.2],[-2,1,-.1],[-1,-2,.1],[1,-2,-.1],[0,0,-1],[.3,.2,2.]])
 support(exact_points(pts.tolist()))
 fig=plt.figure(figsize=(12,6.2),facecolor='#fbfaf6');a=fig.add_subplot(121,projection='3d');b=fig.add_subplot(122)
 axis=pts[6]-pts[5];e=axis/np.linalg.norm(axis);x=np.cross(e,[1,0,0]);x/=np.linalg.norm(x);y=np.cross(e,x)
 plane=[pts[6]+2.4*(sx*x+sy*y) for sx,sy in [(-1,-1),(1,-1),(1,1),(-1,1)]]
 a.add_collection3d(Poly3DCollection([plane],facecolors='#bdd9cc',edgecolors='#7caa92',alpha=.22))
 a.add_collection3d(Poly3DCollection([pts[list(f)] for f in FACES],facecolors=['#a7c9db']*5+['#e8c38e']*5,edgecolors='#3e5661',alpha=.58,linewidths=1.1))
 a.plot(*pts[[5,6]].T,color='#aa4141',linestyle='--',linewidth=2)
 a.scatter(*pts.T,color='#203d4b',s=20,depthshade=False)
 a.text(*(pts[6]+np.array([.1,0,.2])),'q',fontsize=15,color='#203d4b');a.text(*(pts[5]+np.array([.1,0,-.4])),'p',fontsize=15,color='#203d4b')
 a.set_xlim(-2.8,2.8);a.set_ylim(-2.8,2.8);a.set_zlim(-1.6,2.8);a.set_box_aspect((1,1,.8));a.view_init(23,-64);a.set_axis_off();a.text2D(.02,.95,'A. A plane through the source pole',transform=a.transAxes,fontsize=13,fontweight='bold');a.text2D(.02,.03,'Every ring vertex stays on p’s side.\nThe equator can be nonplanar.',transform=a.transAxes,fontsize=11,color='#41565e')
 O=np.array([.9,1.3]);A=np.array([0.,0.]);P=np.array([1.,0.]);M=np.array([np.sqrt(3)/2,.5]);b.set_aspect('equal');b.axis('off')
 b.add_patch(Polygon([A,O,P],facecolor='#f0dfcc',edgecolor='#ac875d',linewidth=1.5));t=np.linspace(0,.95,100);b.plot(np.cos(t),np.sin(t),color='#6993aa',linestyle='--',linewidth=1.5)
 b.plot(*np.array([A,M,O]).T,color='#3d707e',linewidth=2);b.plot(*np.array([A,P]).T,color='#3d707e',linewidth=2)
 for z,label,off in [(A,'a',(-15,-6)),(P,'P',(8,-5)),(M,'M',(10,0)),(O,'p',(-4,10))]:
  b.plot(*z,'o',color='#24424c',markersize=4);b.annotate(label,z,xytext=off,textcoords='offset points',fontsize=14)
 b.text(-.15,1.86,'B. The obstruction cannot occur',fontsize=13,fontweight='bold');b.text(-.15,-.45,'A captured copy M forces angle aMp > 90°.\nThe supporting plane forces it below 90°.',fontsize=11,color='#41565e');b.text(-.15,1.55,'Equal cut-edge lengths: aM = aP',fontsize=11,color='#41565e');b.set_xlim(-.3,1.5);b.set_ylim(-.63,2)
 fig.subplots_adjust(left=.03,right=.97,top=.96,bottom=.03,wspace=.10);fig.savefig(ROOT/'figures/bipyramid-source-plane.svg',facecolor=fig.get_facecolor());plt.close(fig)
if __name__=='__main__':figure()
