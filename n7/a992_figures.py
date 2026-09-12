"""Draw the certified A992 example at its true metric proportions."""
import json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n7.a992_exact import ROOT,geometry,develop,FACES
from n7.a992 import intersection_polygon
COLORS=['#e6b257','#e78075','#a7c4b8','#a7c4b8','#a7c4b8','#b9d7ea','#a7c4b8']

def build():
    c=json.loads((ROOT/'results/a992-exact-counterexample.json').read_text())
    p,_=geometry(c['geometry']['parameters'])
    nets=[develop(p,c[k]) for k in ['failed_cut','successful_cut']]
    nets=[[np.array([[v.mid() for v in x] for x in poly]) for poly in net] for net in nets]
    root=ROOT/'figures';root.mkdir(exist_ok=True)
    plt.rcParams.update({'font.family':'DejaVu Sans','svg.fonttype':'none','svg.hashsalt':'n7-a992','font.size':11})
    fig,axs=plt.subplots(1,2,figsize=(12,6.4));fig.patch.set_facecolor('#fafaf7')
    coords=np.concatenate(nets[0]+nets[1]);lo=coords.min(axis=0)-.3;hi=coords.max(axis=0)+.3
    for k,(ax,net) in enumerate(zip(axs,nets)):
        ax.set_facecolor('#fafaf7')
        for i in [5,0,2,3,4,6,1]:
            xy=net[i];ax.add_patch(Polygon(xy,facecolor=COLORS[i],edgecolor='#44535b',alpha=.78,lw=1.1))
            label={0:'Q',1:'E',5:'P'}.get(i,str(i))
            m=xy.mean(axis=0);ax.text(*m,label,ha='center',va='center',fontsize=13 if i in [0,1,5] else 10,fontweight='bold',color='#182b36')
        if k==0:
            inter=intersection_polygon(net[0],net[1]);ax.add_patch(Polygon(inter,facecolor='#b72c40',edgecolor='#b72c40'))
        ax.set(xlim=(lo[0],hi[0]),ylim=(lo[1],hi[1]),aspect='equal');ax.axis('off')
        ax.set_title(['Left: overlap','Right: E moves to the other attachment'][k],fontweight='bold',fontsize=15,pad=18,color='#182b36')
    fig.tight_layout(pad=2);fig.savefig(root/'a992-nets.svg',facecolor=fig.get_facecolor(),metadata={'Date':None});fig.savefig('/private/tmp/a992-nets.png',dpi=150,facecolor=fig.get_facecolor());plt.close(fig)
    net=nets[0];inter=intersection_polygon(net[0],net[1]);w=np.array(list(map(lambda x:float(F(x)),c['interior_witness'])))
    fig,ax=plt.subplots(figsize=(7.2,4.4));fig.patch.set_facecolor('#fafaf7');ax.set_facecolor('#fafaf7')
    for i in [0,1]:ax.add_patch(Polygon(net[i],facecolor=COLORS[i],edgecolor='#44535b',lw=1.4,alpha=.65))
    ax.add_patch(Polygon(inter,facecolor='#b72c40',alpha=.75,edgecolor='#b72c40'))
    ax.scatter(*w,s=34,color='#172e41',zorder=5)
    ax.annotate('Exact interior witness\n(1.291, −0.132)',xy=w,xytext=(1.45,-.25),arrowprops={'arrowstyle':'->','color':'#172e41'},color='#172e41',fontsize=12)
    ax.text(1.16,-.065,'Q',fontsize=15,fontweight='bold',color='#705118');ax.text(1.48,.09,'E',fontsize=15,fontweight='bold',color='#8d3340')
    ax.set(xlim=(1.13,1.83),ylim=(-.33,.20),aspect='equal');ax.axis('off');ax.set_title('Magnified: a positive area of overlap',fontsize=15,pad=15,fontweight='bold')
    fig.tight_layout();fig.savefig(root/'a992-overlap.svg',facecolor=fig.get_facecolor(),metadata={'Date':None});fig.savefig('/private/tmp/a992-overlap.png',dpi=150,facecolor=fig.get_facecolor());plt.close(fig)
    for path in root.glob('a992-*.svg'):
        path.write_text('\n'.join(line.rstrip() for line in path.read_text().splitlines())+'\n')
    print('Built two figures from the certified center coordinates.')
if __name__=='__main__':build()
