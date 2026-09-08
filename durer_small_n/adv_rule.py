"""Curvature counting for Case B under (H)+slit rule.  If both petals reach the wedge Omega (Case B, SigmaW<pi), how small can
F = k_u + k_u' + 2 max(k_u,k_u') + k_{u_i} + k_w - 4 pi   be?   (Under (H) + rule, k_v, k_{u_k} >= max(k_u,k_u'), so F <= 0 must hold
in any polytope; F > 0 in every both-reach configuration means Case B is impossible under (H)+rule.)  No hypothesis imposed.
score = -F (maximised) with area penalties as in caseB_sub.  usage: adv_rule.py seed restarts steps [seeded]"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import DELTA
from caseB_sub import geom, AMIN
def F_of(o, i):
    j, jj, m = (i + 1) % 4, (i + 2) % 4, (i - 1) % 4
    return o.ku[j] + o.ku[jj] + 2 * max(o.ku[j], o.ku[jj]) + o.ku[i] + o.kw - 4 * np.pi
def score(o, i):
    j, jj = (i + 1) % 4, (i + 2) % 4
    if o.ku[j] + o.ku[jj] < o.nu[j]: return None
    g = geom(o, i)
    if g is None: return None
    if g['SW'] >= np.pi: return -40.0 - (g['SW'] - np.pi)
    a2 = o.scale ** 2; Xi, Xjj = g['Xi'], g['Xjj']
    ai = poly_area(Xi) / a2 if len(Xi) >= 3 else 0.0; ajj = poly_area(Xjj) / a2 if len(Xjj) >= 3 else 0.0
    if ai < AMIN or ajj < AMIN: return -30.0 + min(ai, AMIN) + min(ajj, AMIN)
    return -F_of(o, i)
def best_config(P):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            v = score(o, i)
            if v is None: continue
            sc = v - 10 * deg
            if best is None or sc > best[0]: best = (sc, o.v, i, v, deg)
    return best
if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[1])); R_ = int(sys.argv[2]); S = int(sys.argv[3]); res = []; r = 0
    seeds = [t[0] for t in pickle.load(open('caseB_sub_stat_H3.pkl', 'rb'))] + [t[0] for t in pickle.load(open('caseB_sub_stat_none.pkl', 'rb'))] if len(sys.argv) > 4 else []
    while r < R_:
        P0 = seeds[r] if r < len(seeds) else rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f deg=%.3f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_rule.pkl', 'wb'))
    from caseB_sub import describe
    for b, P in res[:4]:
        o = Octa(P, b[1]); i = b[2]; print("BEST", b, "F=%.4f" % F_of(o, i)); describe(o, i)
