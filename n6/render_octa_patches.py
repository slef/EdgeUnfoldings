"""Illustrate the exact one-nonconvex-patch witness; drawings are not proofs."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n6.polycert import Geometry,verify
from n6.convex_patches import classify
from n6.certify import tree_path
from n6.intervals import set_precision

ROOT=Path(__file__).resolve().parent


def render():
    set_precision(192)
    cert=json.loads((ROOT/'results/octa-patches-one.certificate.json').read_text())
    result=classify(cert);verify(cert);g=Geometry(cert)
    def xy(q):return np.array([float((x.lo+x.hi)/2) for x in q])
    def style(ax):
        ax.relim();ax.autoscale_view();ax.margins(.18);ax.set_aspect('equal');ax.axis('off')
    def save(fig,name):
        out=ROOT/'figures'/name
        fig.savefig(out.with_suffix('.svg'));fig.savefig(out.with_suffix('.png'),dpi=140)
        p=out.with_suffix('.svg');p.write_text('\n'.join(x.rstrip() for x in p.read_text().splitlines())+'\n');plt.close(fig)
    fig,axes=plt.subplots(1,4,figsize=(12,3.3))
    for i,ax in enumerate(axes):
        fan=g.develop((i,));petal=g.develop((i,i+4))
        for fi,q,color in ((i,fan,'#8fc1dd'),(i+4,petal,'#e6af78')):
            ax.add_patch(Polygon([xy(q[u]) for u in g.faces[fi]],facecolor=color,edgecolor='#33495b',alpha=.8,linewidth=1))
        a,b=2+i,2+(i+1)%4
        bad=not result['patches'][i]['convex']
        if bad:
            u=(a,b)[result['patches'][i]['corner_relations_to_pi'].index('>')]
            pos=xy(petal[u]);ax.scatter(*pos,s=25,color='#ad2945',zorder=5)
            ax.annotate('inward corner',pos,xytext=(10,-30),textcoords='offset points',fontsize=10,color='#ad2945',arrowprops=dict(arrowstyle='->',color='#ad2945'))
        ax.annotate('w',xy(fan[1]),xytext=(-8,-13),textcoords='offset points',fontsize=10)
        ax.annotate('v',xy(petal[0]),xytext=(4,6),textcoords='offset points',fontsize=10)
        ax.set_title(f'Q{i}: '+('nonconvex' if bad else 'convex'),fontsize=13,color='#ad2945' if bad else '#244c42')
        style(ax)
    fig.suptitle('Four two-face patches of the same exact octahedron',x=.03,ha='left',fontsize=17,fontweight='bold')
    fig.text(.03,.025,'Each blue–orange pair is flattened separately along its shared edge. Panels are scaled individually.',fontsize=10,color='#40515e')
    fig.subplots_adjust(left=.035,right=.985,bottom=.15,top=.79,wspace=.25)
    save(fig,'octa-convex-patches')
    fig,ax=plt.subplots(figsize=(6,4.8))
    for fi,f in enumerate(g.faces):
        q=g.develop(tree_path(g.adj,0,fi));poly=np.array([xy(q[u]) for u in f])
        ax.add_patch(Polygon(poly,facecolor='#8fc1dd' if fi<4 else '#e6af78',edgecolor='#33495b',alpha=.8,linewidth=.8))
        ax.text(*poly.mean(axis=0),('W' if fi<4 else 'V')+str(fi%4),fontsize=9,ha='center',va='center')
    style(ax);ax.set_title('A certified successful opening at u3',fontsize=14,loc='left')
    fig.subplots_adjust(left=.04,right=.96,top=.9,bottom=.035)
    save(fig,'octa-one-patch-net')


if __name__=='__main__':render()
