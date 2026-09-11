"""Draw the exact example with the newly proved cut-edge separator."""
import json
from pathlib import Path

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon

from n6.certify import tree_path
from n6.intervals import set_precision
from n6.local_small_sum import verify_cut_separator
from n6.polycert import Geometry


def render():
    root = Path(__file__).resolve().parent
    spec = json.loads((root/'results/local-gate-radial-point.certificate.json').read_text())
    set_precision(240)
    report = verify_cut_separator(spec)
    g = Geometry(spec)
    own = report['own_face']
    a, b = report['oriented_cut_edge']
    raw = g.develop([own])
    xy = lambda p: np.array([float((q.lo+q.hi)/2) for q in p])
    origin = xy(raw[a])
    direction = xy(raw[b])-origin
    length = np.linalg.norm(direction)
    up = direction/length
    right = np.array([up[1], -up[0]])
    def position(face):
        points = g.develop(tree_path(g.adj, own, face))
        return {x: np.array([np.dot(xy(p)-origin, right), np.dot(xy(p)-origin, up)])
                for x, p in points.items()}
    first = position(own)
    fan, last = [position(q['face']) for q in report['opposite_face_checks']]
    fig, ax = plt.subplots(figsize=(8.6,6.2))
    for points, fill, edge in [(fan,'#cce3f3','#2d6c94'),(last,'#e2dbef','#78628e'),
                               (first,'#f7d1ac','#a56229')]:
        ax.add_patch(Polygon(list(points.values()), facecolor=fill, edgecolor=edge, lw=1.7))
    ax.axvline(0, color='#277466', ls='--', lw=2)
    ax.plot([0,0],[0,length], color='#277466', lw=2.8)
    v,w,u = 0,4,2
    for point,label,offset in [(first[u],'first u',(-12,-15)),(first[v],'first apex v',(-13,10)),
                               (fan[u],'other u',(12,-17)),(fan[w],'w',(8,0)),
                               (last[v],'other apex v',(8,5))]:
        ax.plot(*point,'o',color='#263b4c',ms=4)
        ax.annotate(label,point,xytext=offset,textcoords='offset points',fontsize=10,
                    ha='right' if offset[0]<0 else 'left',color='#263b4c')
    allpoints = np.array(list(first.values())+list(fan.values())+list(last.values()))
    low, high = allpoints.min(axis=0), allpoints.max(axis=0)
    ax.set_xlim(low[0]-30,high[0]+50)
    ax.set_ylim(low[1]-24,high[1]+25)
    ax.set_aspect('equal'); ax.axis('off')
    fig.suptitle('The cut edge separates both opposite faces', x=.055, ha='left',
                 fontsize=16, fontweight='bold')
    fig.text(.055,.077,'Orange: inward petal. Blue and purple: opposite fan and petal.\n'
             'The green line is the petal’s cut edge, extended. Both opposite faces lie strictly to its right.',
             fontsize=10,color='#44525d')
    fig.subplots_adjust(left=.025,right=.975,top=.91,bottom=.15)
    out=root/'figures/local-small-sum'
    fig.savefig(out.with_suffix('.svg'));fig.savefig(out.with_suffix('.png'),dpi=150)
    svg=out.with_suffix('.svg')
    svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')
    plt.close(fig)


if __name__ == '__main__':
    render()
