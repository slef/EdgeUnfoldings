"""draw the top configurations of a caseB_sub pickle: caseB_draw.py PKL [n]"""
import numpy as np, pickle, sys
from octa import *
from caseB_sub import geom, sub_of, describe
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
res = pickle.load(open(sys.argv[1], "rb")); idxs = [int(a) for a in sys.argv[2:]] or [0]
def closest(P, Q):
    """closest pair of points between convex polygons P, Q (vertex-edge)"""
    best = (np.inf, None, None)
    for S, T in ((P, Q), (Q, P)):
        for a in S:
            for t in range(len(T)):
                b, c = T[t], T[(t + 1) % len(T)]; d = c - b; s = np.clip(np.dot(a - b, d) / np.dot(d, d), 0, 1); q = b + s * d
                dist = np.linalg.norm(a - q)
                if dist < best[0]: best = (dist, a, q)
    return best
for idx in idxs:
    b, P = res[idx]; o = Octa(P, b[1]); i = b[2]; k = (i - 1) % 4; net = o.Z(k); j, jj, m = (i + 1) % 4, (i + 2) % 4, (i - 1) % 4
    g = geom(o, i); describe(o, i)
    fig, ax = plt.subplots(figsize=(9, 9))
    for key, T in net.items():
        if not isinstance(key, tuple): continue
        ax.fill(T[:, 0], T[:, 1], color='#9ecae1' if key[0] == 'W' else '#fdd0a2', alpha=0.6, ec='k', lw=0.6); c = T.mean(0)
        ax.text(c[0], c[1], '%s_%s' % (key[0], {i: 'i', j: 'j', jj: 'jj', m: 'm'}[key[1]]), ha='center', fontsize=9)
    for T, col in ((g['Xi'], 'red'), (g['Xjj'], 'purple')):
        if len(T) >= 3: ax.fill(T[:, 0], T[:, 1], color=col, alpha=0.5)
    L = 1.5 * o.scale
    for P0, d, col in ((g['u'], g['dA'], 'green'), (g['up'], g['dC'], 'brown')):
        d = d / np.linalg.norm(d); ax.plot([P0[0] - L * d[0], P0[0] + L * d[0]], [P0[1] - L * d[1], P0[1] + L * d[1]], color=col, lw=0.8, ls='--')
    X = g['X']; ax.plot([X[0]], [X[1]], 'k+', ms=12); ax.text(X[0], X[1], ' X')
    ax.plot([0], [0], 'ks'); ax.text(0, 0, ' w')
    for t in range(4):
        W = net[('W', (k + t) % 4)]; ax.text(W[1][0], W[1][1], 'u%d' % ((k + t) % 4), color='navy', fontsize=8)
    W = net[('W', (k + 3) % 4)]; ax.text(W[2][0], W[2][1], "u%d" % k, color='navy', fontsize=8)
    if len(g['Xi']) >= 3 and len(g['Xjj']) >= 3:
        dist, a, q = closest(g['Xi'], g['Xjj']); ax.plot([a[0], q[0]], [a[1], q[1]], 'k-', lw=2); print("closest dist %.4f (%.2f%% diam) at %s -- %s" % (dist, 100 * dist / o.scale, np.round(a, 3), np.round(q, 3)))
        for nm, pt in (('v_i', g['Vi'][0]), ('v_jj', g['Vjj'][0]), ('u', g['u']), ("u'", g['up']), ('u_i', g['ui']), ('u_k', g['ujj1'])):
            print("   |%s - a| = %.3f  |%s - q| = %.3f" % (nm, np.linalg.norm(pt - a), nm, np.linalg.norm(pt - q)))
    pts = np.vstack([T for key, T in net.items() if isinstance(key, tuple)]); c = pts.mean(0); r = np.ptp(pts, 0).max() * 0.55
    ax.set_xlim(c[0] - r, c[0] + r); ax.set_ylim(c[1] - r, c[1] + r); ax.set_aspect('equal')
    out = sys.argv[1].replace('.pkl', '_%d.png' % idx); fig.savefig(out, dpi=100); print('->', out)
