"""Illustrate the stronger three-chain theorem with its exact example net."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon

from n6.certify import tree_path
from n6.intervals import set_precision
from n6.polycert import Geometry, verify as verify_net
from n6.three_chain import verify
from n6.half_fan import setup
from n6.patch_budget import pole_angles_and_leans
from n6.curvature import angle_product

ROOT = Path(__file__).resolve().parent


def xy(point):
    return np.array([float((x.lo+x.hi)/2) for x in point])


def phase(z):
    x, y = xy(z)
    return np.degrees(np.arctan2(y, x)) % 360


def render():
    set_precision(240)
    cert = json.loads((ROOT / 'results/three-chain-switch.certificate.json').read_text())
    report = verify(cert)
    verify_net(cert)
    g = Geometry(cert)
    patches, directions, lookup = setup(g, 0, 1, [2,3,4,5])
    _, leans = pole_angles_and_leans(g, 0, 1, [2,3,4,5], directions, lookup)
    K = {p: 360-phase(angle_product(g.p, g.faces, g.h, p)) for p in (0,1,3)}
    L = {p: phase(leans[p][1]) for p in (0,1)}
    rho = L[0]+L[1]
    fig, (left, right) = plt.subplots(1, 2, figsize=(12, 5.6), gridspec_kw={'width_ratios':[1.05,1]})
    left.axis('off')
    left.text(0, .97, 'The stronger theorem applies', fontsize=14, fontweight='bold', va='top')
    rows = [
        ('Middle extension at v fits its gap', f'{L[0]:.3f}°  ≤  {K[0]:.3f}°'),
        ('Middle extension at w fits its gap', f'{L[1]:.3f}°  ≤  {K[1]:.3f}°'),
        ('Middle excess fits the combined bound', f'{rho:.3f}°  ≤  {min(K[0],K[1])+K[3]:.3f}°'),
    ]
    for y, (label, comparison) in zip((.77,.54,.31), rows):
        left.text(0, y, label, fontsize=11, color='#40515e')
        left.text(0, y-.10, comparison, fontsize=17, color='#216c52')
    left.text(0, -.01, f'The simpler test fails: {rho:.3f}° > {min(K[0],K[1]):.3f}°.\nThe combined bound also uses curvature at u₁.',
              fontsize=10, color='#815129', va='top', linespacing=1.6)
    for fi, face in enumerate(g.faces):
        q = g.develop(tree_path(g.adj, 0, fi))
        points = np.array([xy(q[u]) for u in face])
        right.add_patch(Polygon(points, facecolor='#8fc1dd' if fi<4 else '#e6af78',
                                edgecolor='#33495b', linewidth=.9, alpha=.85))
    right.relim(); right.autoscale_view(); right.margins(.07)
    right.set_aspect('equal'); right.axis('off')
    right.set_title('The same solid: a certified original-edge net', loc='left', fontsize=12)
    right.text(.5, -.06, 'Four cuts at v, plus w–u₂\nAll 28 face pairs checked independently',
               ha='center', va='top', transform=right.transAxes, fontsize=11, color='#40515e')
    fig.suptitle('A proved subfamily with three patches leaning the same way',
                 x=.035, ha='left', fontsize=17, fontweight='bold')
    fig.text(.035,.025,'Rounded angles explain the example. The proof and coordinate-region certificates use exact identities and rational bounds.',
             fontsize=10,color='#40515e')
    fig.subplots_adjust(left=.035,right=.98,bottom=.21,top=.83,wspace=.23)
    out=ROOT / 'figures/octa-three-chain.svg'
    fig.savefig(out)
    fig.savefig('/private/tmp/octa-three-chain.png',dpi=150)
    out.write_text('\n'.join(line.rstrip() for line in out.read_text().splitlines())+'\n')
    plt.close(fig)


if __name__ == '__main__':
    render()
