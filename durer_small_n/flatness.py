"""Is flatness what makes the far pairs tight?  For random octahedra with v the sharpest vertex (H) and the rule slit,
measure thickness t = (smallest extent / diameter) via SVD and the minimum separation of the six far pairs and of the
three local pairs.  Report by thickness bin, and the thickness of the adversarial near-misses."""
import numpy as np, sys, pickle, collections
from octa import *
from adv_opp import separation, DELTA
def thickness(P):
    Q = P - P.mean(0); sv = np.linalg.svd(Q, compute_uv=False); return float(sv[-1] / sv[0])
rng = np.random.default_rng(int(sys.argv[1])); N = int(sys.argv[2])
rows = []
for P, faces, adj in random_octahedra(rng, N):
    o = sharpest_apex(P, faces, adj); k = int(np.argmax(o.ku))
    deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
    far = min(separation(*o.pair_faces(k, nm)) for nm in Octa.OPP + Octa.FARFAN) / o.scale
    loc = min(separation(*o.pair_faces(k, nm)) for nm in Octa.LOCAL) / o.scale
    rows.append((thickness(P), far, loc, deg == 0, o.kv, min(o.kappa.values())))
R = np.array(rows)
print("N=%d   (separation < 0 means disjoint; the closer to 0 the tighter)" % len(R))
bins = [0, 0.02, 0.05, 0.1, 0.2, 0.35, 0.5, 1.01]
print("%-14s %6s %10s %10s %10s %10s" % ("thickness", "n", "far:min", "far:median", "loc:min", "loc:median"))
for a, b in zip(bins, bins[1:]):
    m = (R[:, 0] >= a) & (R[:, 0] < b)
    if m.sum(): print("[%.2f, %.2f) %6d %10.4f %10.4f %10.4f %10.4f" % (a, b, m.sum(), R[m, 1].max(), np.median(R[m, 1]), R[m, 2].max(), np.median(R[m, 2])))
import json; json.dump([dict(lo=a, hi=b, n=int(((R[:,0]>=a)&(R[:,0]<b)).sum()), far_min=float(R[(R[:,0]>=a)&(R[:,0]<b),1].max()), far_med=float(np.median(R[(R[:,0]>=a)&(R[:,0]<b),1])), loc_min=float(R[(R[:,0]>=a)&(R[:,0]<b),2].max())) for a,b in zip(bins,bins[1:]) if ((R[:,0]>=a)&(R[:,0]<b)).sum()], open('notes/thickness.json','w'))
print("overall max far separation (closest) %.4f at thickness %.3f ; closest local %.4f at thickness %.3f" % (R[:, 1].max(), R[np.argmax(R[:, 1]), 0], R[:, 2].max(), R[np.argmax(R[:, 2]), 0]))
# adversarial near-misses
for f in ['adv_opp_H3_d.pkl', 'adv_opp_H1_d.pkl']:
    res = pickle.load(open(f, 'rb'))
    print(f, "top-5 near-misses: (separation, thickness, min kappa)", [(round(float(b[4]), 4), round(thickness(P), 3), round(float(min(Octa(P, b[1]).kappa.values())), 3)) for b, P in res[:5]])
