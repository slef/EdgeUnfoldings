"""True-scale drawings of the two exactly certified local overlaps.

Floating-point drawing coordinates are illustrations only. The proof of
positive-area overlap is the separate rational interval certificate.
"""
from pathlib import Path
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n6.low_local_failure import specification
from n6.polycert import Geometry
from n6.intervals import set_precision


def clip_polygon(polygon,clip):
    result=list(polygon)
    sign=1 if sum(np.linalg.det(np.array([clip[i],clip[(i+1)%len(clip)]])) for i in range(len(clip)))>0 else -1
    for a,b in zip(clip,np.roll(clip,-1,axis=0)):
        old=result;result=[]
        if not old:break
        def side(p):return sign*np.linalg.det(np.array([b-a,p-a]))
        for p,q in zip(old,old[1:]+old[:1]):
            sp,sq=side(p),side(q)
            if sp>=0:result.append(p)
            if (sp>0 and sq<0) or (sp<0 and sq>0):
                result.append(p+(q-p)*sp/(sp-sq))
    return result


def main():
    set_precision(240);g=Geometry(specification())
    plt.rcParams.update({'svg.fonttype':'none','font.family':'DejaVu Sans'})
    fig,axes=plt.subplots(1,2,figsize=(11,4.8));fig.patch.set_facecolor('#f7fafc')
    for ax,(a,b),title in zip(axes,[(3,4),(3,7)],['Orange petal against blue fan face','One petal against the other']):
        _,A,B=g.pair_geometry(a,b);polys=[]
        for face,xy,color in [(a,A,'#e7ad72'),(b,B,'#91c6df' if b==4 else '#a8bf79')]:
            p=np.array([[(float(x.lo)+float(x.hi))/200000 for x in xy[v]] for v in g.faces[face]])
            polys.append(p)
            ax.add_patch(Polygon(p,facecolor=color,edgecolor='#465b69',alpha=.7,lw=1.8))
            center=p.mean(axis=0)
            ax.annotate('F'+str(face),center,fontsize=12,weight='bold',ha='center',
                        xytext=(0,9 if face==a else -14),textcoords='offset points',color='#253d4b')
        overlap=clip_polygon(polys[0],polys[1])
        if len(overlap)<3:raise ValueError('Illustration lost the certified overlap')
        ax.add_patch(Polygon(overlap,facecolor='#c84065',edgecolor='#982e4a',alpha=.7,hatch='///',lw=1.3))
        allp=np.concatenate(polys);lo=allp.min(axis=0);hi=allp.max(axis=0);pad=.08*max(hi-lo)
        ax.set_xlim(lo[0]-pad,hi[0]+pad);ax.set_ylim(lo[1]-pad,hi[1]+pad)
        ax.set_aspect('equal');ax.axis('off');ax.set_title(title,fontsize=12,pad=14,color='#253d4b')
    fig.suptitle('A poor slit can create local overlap even at the sharpest source',
                 fontsize=15,weight='bold',x=.04,ha='left',y=.96,color='#253d4b')
    fig.text(.04,.055,'Hatched regions are the certified overlaps. Only the indicated face pairs are shown, at true scale.',fontsize=10,color='#465b69')
    fig.text(.04,.018,'All six far pairs remain safe. Switching the fifth cut from 3–2 to 3–4 makes all 28 pairs safe.',fontsize=10,color='#465b69')
    fig.subplots_adjust(left=.05,right=.97,top=.81,bottom=.14,wspace=.22)
    output=Path(__file__).parent/'figures/low-local-failure.svg'
    fig.savefig(output,facecolor=fig.get_facecolor());plt.close(fig)
    output.write_text('\n'.join(line.rstrip() for line in output.read_text().splitlines())+'\n')


if __name__=='__main__':main()
