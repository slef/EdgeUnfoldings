"""Rounded offline illustrations for the exact insertion examples."""
import json
from pathlib import Path
from fractions import Fraction as F
from n7.bipyramid_morph import ROOT,FACES,exact_points,develop,morph_geometry

def normalize_svg(name):
 p=ROOT/'figures'/name
 p.write_text('\n'.join(line.rstrip() for line in p.read_text().splitlines())+'\n')

def frames(row):
 p=exact_points(row['points']);p0,_=morph_geometry(p,row['inserted_vertex'],row['subdivision_edge'])
 result={'id':row['id'],'points':[[float(x) for x in v] for v in p],
  'start':[[float(x) for x in v] for v in p0],'vertex':row['inserted_vertex'],
  'cuts':[row['initial_cut'],row['cover'][0]['cut']],'nets':[]}
 for cut in result['cuts']:
  nets=[]
  for i in range(101):
   q=[[a+F(i,100)*(b-a) for a,b in zip(v,w)] for v,w in zip(p0,p)]
   nets.append([[[round(x.mid(),9) for x in pt] for pt in tri] for tri in develop(q,cut)])
  result['nets'].append(nets)
 return result

def build():
 rows=json.loads((ROOT/'results/bipyramid-morph.json').read_text())['examples']
 data={'faces':FACES,'examples':[frames(row) for row in reversed(rows)]}
 template=(ROOT/'morph-demo-template.html').read_text()
 (ROOT/'bipyramid-morph-demo.html').write_text(template.replace('MORPH_DATA',json.dumps(data,separators=(',',':'))))
 print('Built two insertion illustrations, each with 101 frames and two cut choices. Frames are not proof predicates.')


def projection_figure():
 import math
 import matplotlib.pyplot as plt
 from matplotlib.patches import Polygon
 q=[(math.cos(2*math.pi*i/5),math.sin(2*math.pi*i/5)) for i in range(5)]
 fig,axes=plt.subplots(1,3,figsize=(12,3.4));fig.patch.set_facecolor('#f7f8f4')
 for ax,o,title in zip(axes,[(0,0),(.72,0),(q[1][0],0)],['A · octahedron','B · new pole edge','Boundary · one flat cap']):
  ax.set_facecolor('#f7f8f4');ax.add_patch(Polygon(q,fill=False,edgecolor='#9babae',linestyle='--',linewidth=1.2))
  ax.add_patch(Polygon(q[1:],facecolor='#dae9e0',edgecolor='#315d60',linewidth=1.6))
  ax.plot([q[1][0],q[4][0]],[q[1][1],q[4][1]],color='#217b68',linewidth=2)
  for i,p in enumerate(q):
   ax.plot(*p,'o',color='#188556' if i==0 else '#345560',markersize=5)
   if i in(0,1,4):ax.text(p[0]+.06,p[1]+.05,['q₀ = removed x','a','','','b'][i],fontsize=11)
  ax.plot(*o,'o',color='#b03851',markersize=6);ax.text(o[0]-.04,o[1]-.22,'O = image of w',fontsize=10,ha='center',color='#962a43')
  ax.set_title(title,fontsize=14,loc='left',pad=16);ax.set_aspect('equal');ax.set_xlim(-1,1.7);ax.set_ylim(-1.25,1.28);ax.axis('off')
 fig.text(.035,.02,'Central projection from pole v. Green is the remaining equator polygon; the location of O determines the cap.',fontsize=11,color='#40565c')
 fig.tight_layout(rect=[0,.09,1,1]);fig.savefig(ROOT/'figures/bipyramid-deletion.svg',metadata={'Date':None},facecolor=fig.get_facecolor());plt.close(fig)
 normalize_svg('bipyramid-deletion.svg')

def overlap_figure():
 import numpy as np
 import matplotlib.pyplot as plt
 from matplotlib.patches import Polygon
 row=json.loads((ROOT/'results/bipyramid-morph.json').read_text())['examples'][1]
 net=[np.array([[x.mid() for x in p] for p in tri]) for tri in develop(exact_points(row['points']),row['initial_cut'])]
 witness=np.array([float(F(x)) for x in row['overlap_witness']])
 fig,axes=plt.subplots(1,2,figsize=(10,5));fig.patch.set_facecolor('#f7f8f4')
 for ai,ax in enumerate(axes):
  ax.set_facecolor('#f7f8f4')
  for k,tri in enumerate(net):
   if ai==1 and k not in (0,6):continue
   color='#e595ae' if k in(0,6) else '#a7cdda' if k>=5 else '#e7c781'
   ax.add_patch(Polygon(tri,facecolor=color,alpha=.7,edgecolor='#49646d',linewidth=1))
   if ai==0:ax.text(*tri.mean(axis=0),str(k),ha='center',fontsize=10)
  ax.plot(*witness,'o',color='#a5193c',markersize=4)
  ax.set_aspect('equal')
  if ai==0:ax.autoscale_view();ax.margins(.07);ax.axis('off');ax.set_title('The initially safe tree at t = 1',loc='left',fontsize=13)
  else:
   ax.set_xlim(witness[0]-.011,witness[0]+.011);ax.set_ylim(witness[1]-.011,witness[1]+.011)
   ax.set_title('Magnified: strictly inside faces 0 and 6',loc='left',fontsize=13)
   ax.set_xlabel('Developed x coordinate');ax.set_ylabel('Developed y coordinate');ax.tick_params(labelsize=9)
   ax.annotate('Exact rational witness',xy=witness,xytext=(witness[0]-.01,witness[1]+.008),fontsize=10,arrowprops={'arrowstyle':'->','color':'#a5193c'},color='#a5193c')
 fig.tight_layout();fig.savefig(ROOT/'figures/bipyramid-morph-overlap.svg',metadata={'Date':None},facecolor=fig.get_facecolor(),bbox_inches='tight',pad_inches=.18);plt.close(fig)
 normalize_svg('bipyramid-morph-overlap.svg')

if __name__=='__main__':
 projection_figure()
 overlap_figure()
 build()
