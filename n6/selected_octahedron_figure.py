"""Draw the hypothetical equal-radius configuration used in the proof.

This is a planar proof schematic, not a realizable octahedron counterexample.
The drawn angles satisfy the crossing inequality; convex-solid curvature
constraints, explained in LEMMA_F_CHORD.md, rule that inequality out.
"""
from pathlib import Path
import math
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Arc


def main():
    plt.rcParams.update({'svg.fonttype':'none', 'font.family':'DejaVu Sans'})
    fig, (ax, text) = plt.subplots(1, 2, figsize=(11, 4.8),
                                 gridspec_kw={'width_ratios':[1.1,1]})
    fig.patch.set_facecolor('#f7fafc')
    ax.set_facecolor('#f7fafc')
    theta, gap, delta = map(math.radians, (20,20,30))
    s, r = 1.8, 3
    a, w = (0,0), (r,0)
    M = (s*math.cos(theta), s*math.sin(theta))
    P = (s*math.cos(theta+gap), s*math.sin(theta+gap))
    t = r*math.sin(delta)/(s*math.sin(theta+gap+delta))
    q = (t*P[0], t*P[1])
    ax.add_patch(Arc(a,2*s,2*s,theta1=0,theta2=52,color='#8595a3',ls='--',lw=1.4))
    ax.add_patch(Polygon([a,w,q],closed=True,facecolor='#dceaf1',edgecolor='#486a80',lw=1.5))
    ax.plot([a[0],M[0]],[a[1],M[1]],color='#277b97',lw=2.4)
    ax.plot([a[0],P[0]],[a[1],P[1]],color='#c67b28',lw=2.4)
    ax.plot([w[0],q[0]-.18*math.cos(delta)],
            [w[1],q[1]+.18*math.sin(delta)],color='#b82f4b',lw=2)
    for name, point, offset in [('a',a,(-10,-17)),('w',w,(6,-13)),
                                ('M',M,(8,3)),('P',P,(-10,10)),('q',q,(-17,-1))]:
        ax.scatter(*point,s=27,color='#243b49',zorder=5)
        ax.annotate(name,point,xytext=offset,textcoords='offset points',fontsize=13)
    ax.annotate('two copies of one cut edge\n|aM| = |aP|',(.55,.2),
                xytext=(-.1,1.55),fontsize=11,color='#243b49',
                arrowprops={'arrowstyle':'-','color':'#8595a3'})
    ax.text(1.7,1.4,'hypothetical cut entry',fontsize=10,color='#b82f4b')
    ax.text(.85,-.35,'M must stay on a’s side of the cut line.',fontsize=10,ha='center')
    ax.set_aspect('equal'); ax.set_xlim(-.2,3.2);ax.set_ylim(-.55,1.85);ax.axis('off')
    text.axis('off')
    text.text(0,.91,'A crossing would require',fontsize=13,weight='bold',color='#243b49')
    text.text(0,.77,'2θ + 2δ + κₐ < 180°',fontsize=20,color='#b82f4b')
    text.text(0,.59,'But if every curvature is ≤180°:',fontsize=12,color='#243b49')
    text.text(0,.43,'2θ + 2δ + κₐ > 180°',fontsize=20,color='#24775d')
    text.text(0,.29,'The two equal edge lengths give the first bound.\n'
              'The total curvature and a face-angle bound\n'
              'give the second. Both cannot hold.',fontsize=11,linespacing=1.55,color='#243b49',va='top')
    fig.suptitle('The missing distance argument: equal cut edges forbid entry',
                 fontsize=16,weight='bold',x=.05,ha='left',y=.96,color='#243b49')
    fig.text(.05,.035,'Proof schematic only. The displayed planar crossing cannot satisfy the low-curvature octahedron hypotheses.',
             fontsize=10,color='#4d6372')
    fig.subplots_adjust(left=.06,right=.97,top=.85,bottom=.13,wspace=.22)
    output=Path(__file__).parent/'figures/lemma-F-equal-lengths.svg'
    fig.savefig(output,facecolor=fig.get_facecolor())
    plt.close(fig)


if __name__=='__main__':
    main()
