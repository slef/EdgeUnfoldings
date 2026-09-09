"""Draw the exact adjacent-patch example and its theorem-selected net."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Wedge
from n6.polycert import Geometry, verify as verify_net
from n6.half_fan import verify
from n6.certify import tree_path
from n6.intervals import set_precision

ROOT = Path(__file__).resolve().parent


def render():
    set_precision(240)
    cert = json.loads((ROOT / 'results/half-fan-bf.certificate.json').read_text())
    report = verify(cert)
    verify_net(cert)
    g = Geometry(cert)
    k = report['slit_index']

    def xy(q):
        return np.array([float((x.lo+x.hi)/2) for x in q])

    fig = plt.figure(figsize=(12, 5.8))
    grid = fig.add_gridspec(2, 2, width_ratios=[1, 1.6])
    for row, i in enumerate((2, 3)):
        ax = fig.add_subplot(grid[row, 0])
        for fi, route in [(i, [i]), (i+4, [i, i+4])]:
            q = g.develop(route)
            ax.add_patch(Polygon([xy(q[u]) for u in g.faces[fi]],
                                facecolor='#8fc1dd' if fi < 4 else '#e6af78',
                                edgecolor='#33495b', alpha=.85))
        corner = report['patches'][i]['equator_edge'][0 if i == 2 else 1]
        pos = xy(q[corner])
        ax.scatter(*pos, color='#ad2945', s=25, zorder=5)
        ax.annotate('inward corner', pos, xytext=(12, -22),
                    textcoords='offset points', color='#ad2945', fontsize=10,
                    arrowprops=dict(arrowstyle='->', color='#ad2945'))
        ax.set_title(f'Q{i}: leans ' + ('backward' if i == 2 else 'forward'),
                     loc='left', fontsize=12)
        ax.relim(); ax.autoscale_view(); ax.margins(.2)
        ax.set_aspect('equal'); ax.axis('off')

    ax = fig.add_subplot(grid[:, 1])
    positions = {}
    for fi, f in enumerate(g.faces):
        q = g.develop(tree_path(g.adj, k, fi))
        positions[fi] = {u: xy(q[u]) for u in f}
        points = np.array([positions[fi][u] for u in f])
        ax.add_patch(Polygon(points, facecolor='#8fc1dd' if fi < 4 else '#e6af78',
                            edgecolor='#33495b', linewidth=.9, alpha=.85, zorder=2))
        ax.text(*points.mean(axis=0), ('W' if fi < 4 else 'V')+str(fi % 4),
                ha='center', va='center', fontsize=9, zorder=3)
    w = positions[k][1]
    last = positions[(k-1) % 4][2+k]-w
    theta = np.degrees(np.arctan2(last[1], last[0])) % 360
    radius = .23 * max(np.linalg.norm(q-w) for row in positions.values() for q in row.values())
    ax.add_patch(Wedge(w, radius, theta, 360, facecolor='#f1e5eb',
                       edgecolor='#ad748d', linestyle='--', linewidth=.8, zorder=0))
    ray = np.array([np.cos(np.radians((theta+360)/2)), np.sin(np.radians((theta+360)/2))])
    ax.annotate(f'Fan opening\n{360-theta:.1f}°', w + .9*radius*ray,
                xytext=(0, -16), textcoords='offset points', ha='center', va='top',
                fontsize=11, color='#854461')
    ax.annotate('w', w, xytext=(-11, 5), textcoords='offset points', fontsize=12)
    ax.set_title(f'Cut the four edges at v, then w–u{k}', fontsize=14, loc='left')
    ax.relim(); ax.autoscale_view(); ax.margins(.17)
    ax.set_aspect('equal'); ax.axis('off')
    fig.suptitle('Two adjacent inward corners: a proved opening rule',
                 x=.035, ha='left', fontsize=17, fontweight='bold')
    fig.text(.035, .035,
             'One exact convex octahedron. Left: the two bad patches, at separate scales. Right: all eight faces in the selected net.',
             fontsize=10, color='#40515e')
    fig.subplots_adjust(left=.035, right=.985, bottom=.12, top=.85, hspace=.32, wspace=.24)
    out = ROOT / 'figures/octa-half-fan'
    fig.savefig(out.with_suffix('.svg'))
    fig.savefig('/private/tmp/octa-half-fan.png', dpi=150)
    svg = out.with_suffix('.svg')
    svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')
    plt.close(fig)


if __name__ == '__main__':
    render()
