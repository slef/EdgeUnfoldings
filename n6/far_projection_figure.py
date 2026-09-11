"""Proof schematics, not a numerical octahedron or an overlap witness."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Circle, Arc


def main():
    plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':11, 'svg.fonttype':'none',
                         'svg.hashsalt':'lemma-f-pole-angle'})
    fig, axes = plt.subplots(1, 2, figsize=(10.5, 4.9))
    fig.subplots_adjust(left=.03, right=.98, top=.78, bottom=.16, wspace=.16)
    fig.suptitle('Two ways to keep a remote petal off the cut', x=.035, ha='left', y=.96,
                 fontsize=16, fontweight='bold')
    fig.text(.035, .87, 'Proof schematics • A hypothetical crossing leads to a geometric contradiction.',
             color='#536370', fontsize=10)
    blue, orange, red, gray = '#2878a5', '#be7029', '#b52d42', '#536370'
    ax = axes[0]
    a, w, p, M = map(np.array, [(0,0), (1.1,1.7), (1.25,-.38), (1.8,0)])
    ax.add_patch(Polygon([w,a,p], facecolor='#dcecf6', edgecolor=blue, lw=1.7))
    ax.plot(*np.array([a,M]).T, color=orange, lw=2)
    ax.plot([1.8,1.8], [-.65,1.95], '--', color=red, lw=1.5)
    ax.plot(*np.array([w,M]).T, ':', color=gray, lw=1.2)
    for point,label,offset in [(a,'a',(-.16,-.08)), (w,'w',(-.06,.1)),
                                (p,'p',(-.04,-.23)), (M,'M',(.06,.03))]:
        ax.plot(*point,'o',color=gray,ms=4)
        ax.text(*(point+offset),label,fontstyle='italic')
    ax.text(.48,.55,'triangle T',color=blue)
    ax.text(.55,-.18,'length s',color=orange,fontsize=10)
    ax.text(1.91,1.14,'supporting\nline',color=red,fontsize=10)
    ax.set_title('1. The neighboring apex cannot fit', loc='left', fontsize=12, pad=13)
    ax.set_xlim(-.3,2.55); ax.set_ylim(-.8,2.05)
    ax = axes[1]
    w, a = np.array([0.,0.]), np.array([2.25,0.])
    s=1.1; P=a+s*np.array([-.35,-np.sqrt(1-.35**2)])
    b=1.85*np.array([np.cos(np.deg2rad(-115)),np.sin(np.deg2rad(-115))])
    ax.add_patch(Circle(a,s,facecolor='#fff1e3',edgecolor=orange,lw=1.5))
    ax.plot(*np.array([w,a]).T,color=blue,lw=1.5)
    ax.plot(*np.array([a,P]).T,color=orange,lw=2)
    ax.plot(*np.array([w,b]).T,color=red,lw=2)
    ax.plot([0,0],[-1.8,1.25],'--',color=gray,lw=1)
    ax.add_patch(Arc(w,1.1,1.1,theta1=-115,theta2=0,color=red,lw=1.2))
    for point,label,offset in [(w,'w',(-.2,.12)), (a,'a',(.04,.1)),
                                (P,'P',(-.18,-.25)), (b,'cut endpoint',(-.05,-.23))]:
        ax.plot(*point,'o',color=gray,ms=4);ax.text(*(point+offset),label)
    ax.text(.04,-.82,'at least 90°',color=red,fontsize=10)
    ax.text(1.5,.48,'petal apex P\nlies on this circle',color=orange,fontsize=10)
    ax.set_title('2. A short radius cannot reach the gap', loc='left', fontsize=12, pad=13)
    ax.set_xlim(-1.25,3.7); ax.set_ylim(-2.05,1.45)
    for ax in axes:
        ax.set_aspect('equal');ax.axis('off')
    fig.text(.035,.045,'Left: crossing would trap M inside T, but the nonobtuse angle puts M beyond T.\n'
             'Right: when |aP| ≤ |aw|, the petal cannot lean 90° backward from wa.',
             color=gray,fontsize=10,linespacing=1.6)
    destination = Path(__file__).resolve().parent/'figures/lemma-F-pole-angle.svg'
    fig.savefig(destination,metadata={'Date':None})
    destination.write_text('\n'.join(line.rstrip() for line in destination.read_text().splitlines())+'\n')


if __name__ == '__main__':
    main()
