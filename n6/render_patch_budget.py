"""Draw exact examples of the new budget proof and its remaining regime."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Arc
from n6.polycert import Geometry, verify as verify_net
from n6.patch_budget import verify, analyze
from n6.certify import tree_path
from n6.intervals import set_precision

ROOT = Path(__file__).resolve().parent
BLUE, ORANGE = '#8fc1dd', '#e6af78'


def xy(q):
    return np.array([float((x.lo+x.hi)/2) for x in q])


def panel(ax):
    ax.relim(); ax.autoscale_view(); ax.margins(.22)
    ax.set_aspect('equal'); ax.axis('off')


def save(fig, stem):
    out = ROOT / 'figures' / stem
    fig.savefig(out.with_suffix('.svg'))
    fig.savefig('/private/tmp/' + stem + '.png', dpi=150)
    path = out.with_suffix('.svg')
    path.write_text('\n'.join(line.rstrip() for line in path.read_text().splitlines())+'\n')
    plt.close(fig)


def patch(ax, g, i, report, labels=False):
    W, V = g.develop([i]), g.develop([i, i+4])
    for fi, q, color in ((i, W, BLUE), (i+4, V, ORANGE)):
        ax.add_patch(Polygon([xy(q[u]) for u in g.faces[fi]], facecolor=color,
                            edgecolor='#33495b', alpha=.85, linewidth=1))
    d = report['directions'][i]
    if d:
        a, b = report['patches'][i]['equator_edge']
        r, c = (b, a) if d == 'F' else (a, b)
        ax.scatter(*xy(V[r]), color='#ad2945', s=25, zorder=5)
        if labels:
            w, v, u = xy(W[1]), xy(V[0]), xy(V[c])
            ax.plot([w[0], v[0]], [w[1], v[1]], '--', color='#667786', linewidth=1)
            for name, p in [('w', w), ('v′', v)]:
                ax.annotate(name, p, xytext=(-8, -14), textcoords='offset points', fontsize=12)
            ax.annotate('inward corner', xy(V[r]), xytext=(20, 16),
                        textcoords='offset points', fontsize=10, color='#ad2945',
                        arrowprops=dict(arrowstyle='->', color='#ad2945'))
            span = max(np.linalg.norm(v-w), np.linalg.norm(u-w), np.linalg.norm(u-v))
            values = []
            for origin, outer, color in [(w, v, '#286a99'), (v, w, '#a66127')]:
                a1 = np.degrees(np.arctan2(*(xy(V[r])-origin)[::-1])) % 360
                a2 = np.degrees(np.arctan2(*(outer-origin)[::-1])) % 360
                diff = (a2-a1) % 360
                if diff > 180: a1, a2 = a2, a1; diff = 360-diff
                radius = .17*span
                ax.add_patch(Arc(origin, 2*radius, 2*radius, theta1=a1, theta2=a1+diff,
                                 color=color, linewidth=2))
                mid = np.radians(a1+diff/2)
                text = origin+1.4*radius*np.array([np.cos(mid), np.sin(mid)])
                ax.text(*text, f'{diff:.1f}°', color=color, fontsize=11, ha='center', va='center')
                values.append(diff)
            ax.set_xlabel('')
            ax.text(.5, -.10, f'{values[0]:.1f}° + {values[1]:.1f}° = {sum(values):.1f}° of reflex excess',
                    transform=ax.transAxes, ha='center', fontsize=11, color='#40515e')
    return W, V


def render():
    set_precision(240)
    cert = json.loads((ROOT / 'results/patch-budget-adjacent-below-pi.certificate.json').read_text())
    report = verify(cert); verify_net(cert); g = Geometry(cert)
    fig, axes = plt.subplots(1, 2, figsize=(12, 5.8))
    patch(axes[0], g, 2, report, labels=True)
    axes[0].set_title('One patch, viewed from both poles', loc='left', fontsize=13)
    panel(axes[0])
    ax = axes[1]
    for fi, f in enumerate(g.faces):
        q = g.develop(tree_path(g.adj, 0, fi))
        p = np.array([xy(q[u]) for u in f])
        ax.add_patch(Polygon(p, facecolor=BLUE if fi < 4 else ORANGE,
                            edgecolor='#33495b', alpha=.85, linewidth=.9))
        ax.text(*p.mean(axis=0), ('W' if fi < 4 else 'V')+str(fi % 4),
                fontsize=9, ha='center', va='center')
    ax.set_title('A certified net with both poles below 180°', loc='left', fontsize=13)
    panel(ax)
    fig.suptitle('The two poles share an angle budget', x=.035, ha='left',
                 fontsize=18, fontweight='bold')
    fig.text(.035, .035, 'One exact convex octahedron with two adjacent bad patches. The decimal angles illustrate the exact geometric identity.',
             fontsize=10, color='#40515e')
    fig.subplots_adjust(left=.035, right=.985, bottom=.18, top=.84, wspace=.28)
    save(fig, 'octa-patch-budget')

    cert = json.loads((ROOT / 'results/patch-budget-three-same.certificate.json').read_text())
    report = analyze(cert); verify_net(cert); g = Geometry(cert)
    fig, axes = plt.subplots(1, 4, figsize=(12, 3.8))
    for ax, i in zip(axes, (3, 0, 1, 2)):
        patch(ax, g, i, report)
        bad = bool(report['directions'][i])
        ax.set_title(f'Q{i}: '+('backward' if bad else 'convex'), fontsize=13,
                     color='#ad2945' if bad else '#244c42')
        panel(ax)
    fig.suptitle('The remaining pattern: three bad patches lean the same way',
                 x=.035, ha='left', fontsize=17, fontweight='bold')
    fig.text(.035, .03, 'The same exact octahedron, with each patch scaled separately. This example unfolds; its whole geometric family remains open.',
             fontsize=10, color='#40515e')
    fig.subplots_adjust(left=.035, right=.985, bottom=.15, top=.78, wspace=.3)
    save(fig, 'octa-three-same')


if __name__ == '__main__':
    render()
