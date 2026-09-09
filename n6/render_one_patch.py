"""Illustrate the two prescribed nets of one exactly certified octahedron."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n6.polycert import Geometry, verify as verify_net
from n6.one_patch import verify
from n6.certify import tree_path
from n6.intervals import set_precision

ROOT = Path(__file__).resolve().parent


def render():
    set_precision(240)
    fig, axes = plt.subplots(1, 2, figsize=(12, 5.5))
    for j, (letter, ax) in enumerate(zip('AB', axes)):
        cert = json.loads((ROOT / f'results/one-patch-{letter}.certificate.json').read_text())
        report = verify(cert); verify_net(cert); g = Geometry(cert)
        candidate = report['candidates'][report['selected_candidate']]
        fan = candidate['fan_vertex']; root = 0 if fan == 1 else 4
        for fi, f in enumerate(g.faces):
            q = g.develop(tree_path(g.adj, root, fi))
            p = np.array([[float((x.lo+x.hi)/2) for x in q[u]] for u in f])
            ax.add_patch(Polygon(p, facecolor='#8fc1dd' if fan in f else '#e6af78',
                                edgecolor='#33495b', alpha=.85, linewidth=.9))
            ax.text(*p.mean(axis=0), ('W' if fi < 4 else 'V')+str(fi % 4),
                    fontsize=10, ha='center', va='center')
        name, other = ('v', 'w') if j == 0 else ('w', 'v')
        ax.set_title(f'{letter}: four cuts at {name}; fifth edge {other}–u₃',
                     fontsize=14, loc='left')
        ax.relim(); ax.autoscale_view(); ax.margins(.14)
        ax.set_aspect('equal'); ax.axis('off')
    fig.suptitle('One inward corner: exchange the two opposite vertices',
                 x=.035, ha='left', fontsize=17, fontweight='bold')
    fig.text(.035, .055,
             'The same exact octahedron, at separate scales. Both nets happen to work here; the theorem guarantees at least one.',
             fontsize=10, color='#40515e')
    fig.subplots_adjust(left=.035, right=.985, bottom=.14, top=.82, wspace=.16)
    out = ROOT / 'figures/octa-one-patch-two-poles'
    fig.savefig(out.with_suffix('.svg'))
    fig.savefig('/private/tmp/octa-one-patch-two-poles.png', dpi=150)
    svg = out.with_suffix('.svg')
    svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')
    plt.close(fig)


if __name__ == '__main__':
    render()
