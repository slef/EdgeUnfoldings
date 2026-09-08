"""Adversarial search: how close can opposite petals V_i, V_{i+2} come under a curvature hypothesis?
Score = penetration depth (>0) or minus the distance between the two triangles (<0), maximised over
octahedra by random-restart hill climbing; hypothesis violation is penalised.
usage: adv_opp.py HYP seed restarts steps      HYP in {H1, H2, H3}
  H1: κ_v ≥ κ_{u_{i+1}} and κ_v ≥ κ_{u_{i+2}} (the two vertices of the petal between, W side)
  H2: κ_v ≥ κ_u for all four equator vertices
  H3: v sharpest of all six vertices
"""
import numpy as np, sys, pickle
from octa import *

def seg_dist(p, a, b):
    d = b - a; t = np.clip(np.dot(p - a, d) / np.dot(d, d), 0, 1)
    return np.linalg.norm(p - (a + t * d))

def separation(T1, T2):
    pen = sat_pen(T1, T2)
    if pen > 0: return pen
    return -min(min(seg_dist(p, T2[a], T2[(a + 1) % 3]) for p in T1 for a in range(3)),
                min(seg_dist(p, T1[a], T1[(a + 1) % 3]) for p in T2 for a in range(3)))

def violation(o, i, hyp):
    j, jj = (i + 1) % 4, (i + 2) % 4
    if hyp == 'H1': return max(0.0, o.ku[j] - o.kv, o.ku[jj] - o.kv)
    if hyp == 'H2': return max(0.0, o.ku.max() - o.kv)
    if hyp == 'H3': return max(0.0, o.ku.max() - o.kv, o.kw - o.kv)
    if hyp == 'R': return max(0.0, o.ku.max() - o.ku[(i - 1) % 4])   # slit rule only
    if hyp == 'H3R': return max(0.0, o.ku.max() - o.kv, o.kw - o.kv, o.ku.max() - o.ku[(i - 1) % 4])   # (H) + slit rule: u_k (k=i-1) sharpest neighbour of w
    return 0.0   # 'none': no hypothesis

DELTA = 0.05   # degeneracy guard: every edge at least DELTA * diameter
def best_config(P, hyp):
    """max over apex v, slit k, pair of (separation/scale - 10*violation - 10*degeneracy); returns (score, v, k, name, sep, viol)."""
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for k in range(4):
            for nm in Octa.OPP:
                i = k if nm == 'V_k-V_k+2' else (k + 1) % 4
                vio = violation(o, i, hyp)
                A, B = o.pair_faces(k, nm)
                sep = separation(A, B) / o.scale
                sc = sep - 10 * vio - 10 * deg
                if best is None or sc > best[0]: best = (sc, o.v, k, nm, sep, vio)
    return best

if __name__ == '__main__':
    hyp = sys.argv[1]; rng = np.random.default_rng(int(sys.argv[2])); R = int(sys.argv[3]); S = int(sys.argv[4])
    results = []
    r = 0
    while r < R:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, hyp))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, hyp)
        results.append((b, P))
        print("restart %d: score %.5f  v=%d k=%d %s sep=%.5f viol=%.4f" % (r, b[0], b[1], b[2], b[3], b[4], b[5]), flush=True)
    results.sort(key=lambda t: -t[0][0])
    pickle.dump(results, open('adv_opp_%s_d.pkl' % hyp, 'wb'))
    print("BEST", hyp, results[0][0])
    b, P = results[0]
    o = Octa(P, b[1]); print("kv=%.3f kw=%.3f ku=%s nu=%s omega=%s F=%s B=%s" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3), np.round(o.omega, 3), np.round(o.F, 3), np.round(o.B, 3)))
