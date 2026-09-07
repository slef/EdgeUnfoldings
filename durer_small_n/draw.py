"""Draw a net Z_k of an Octa to PNG (matplotlib).  draw_net(o, k, fname, highlight=[pair names])"""
import numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from octa import Octa, clip_convex

def draw_net(o, k, fname, highlight=(), title=None, zoom=None, labels=True):
    net = o.Z(k)
    fig, ax = plt.subplots(figsize=(9, 9))
    cols = {'W': '#9ecae1', 'V': '#fdd0a2'}
    for key, T in net.items():
        if not isinstance(key, tuple): continue
        typ, j = key
        prime = "'" if (typ in 'WV' and (j - k) % 4 == 3) else ''
        ax.fill(T[:, 0], T[:, 1], color=cols[typ], alpha=0.6, ec='k', lw=0.8)
        if labels:
            c = T.mean(0)
            ax.text(c[0], c[1], '%s_%d%s' % (typ, (j - k) % 4, prime), ha='center', va='center', fontsize=8, clip_on=True)
    for nm in highlight:
        X = o.intersection(k, nm)
        if len(X) >= 3: ax.fill(X[:, 0], X[:, 1], color='red', alpha=0.9)
    # vertices
    if labels:
        for t in range(4):
            j = (k + t) % 4; W = net[('W', j)]; V = net[('V', j)]
            ax.text(W[1, 0], W[1, 1], 'u%d%s' % (t, "'" if t == 0 and False else ''), fontsize=7, color='navy', clip_on=True)
            ax.text(V[0, 0], V[0, 1], 'v', fontsize=7, color='darkred', clip_on=True)
        W = net[('W', (k + 3) % 4)]
        ax.text(W[2, 0], W[2, 1], "u0'", fontsize=7, color='navy', clip_on=True)
    ax.plot([0], [0], 'ko', ms=3); ax.text(0, 0, ' w', fontsize=8, clip_on=True)
    ax.set_aspect('equal'); ax.grid(alpha=0.2)
    if zoom is not None:
        cx, cy, r = zoom; ax.set_xlim(cx - r, cx + r); ax.set_ylim(cy - r, cy + r)
    t = title or 'Z_%d  (v=%d, w=%d)  kv=%.3f kw=%.3f ku=%s' % (k, o.v, o.w, o.kv, o.kw, np.round(o.ku, 3))
    ax.set_title(t, fontsize=9)
    fig.savefig(fname, dpi=110, bbox_inches=None if zoom is not None else 'tight'); plt.close(fig)
    return fname
