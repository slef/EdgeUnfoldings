"""Can the outer cut edges u_i v_i and u_k v_jj (V_i and V_jj across the slit, k = i-1) cross when nu_m > kappa_back
(the cut-edge lines converge on V_m's side)?  score = min(r_i - |u_i Y|, r_k - |u_k Y|)/scale, Y = crossing of the lines
(positive = both segments reach Y = crossing).  Configurations with nu_m <= kappa_back are invalid (score None).
usage: adv_crossA.py HYP seed restarts steps"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import violation, DELTA
def score(o, i):
    j, jj, m = (i + 1) % 4, (i + 2) % 4, (i - 1) % 4; k = m; net = o.Z(k)
    kb = o.ku[i] + o.ku[m] + o.kw
    if o.nu[m] <= kb: return None
    Vi, Vjj = net[('V', i)], net[('V', jj)]; ui, vi = Vi[2], Vi[0]; uk, vjj = Vjj[1], Vjj[0]
    d1 = vi - ui; d2 = vjj - uk; M = np.array([d1, -d2]).T
    if abs(np.linalg.det(M)) < 1e-14: return None
    t = np.linalg.solve(M, uk - ui)
    if t[0] < 0 or t[1] < 0: return -1.0          # lines meet behind the base points (should not happen if nu_m > kb)
    return min(1 - t[0], 1 - t[1]) * min(np.linalg.norm(d1), np.linalg.norm(d2)) / o.scale
def best_config(P, hyp):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            v = score(o, i)
            if v is None: continue
            sc = v - 10 * violation(o, i, hyp) - 10 * deg
            if best is None or sc > best[0]: best = (sc, o.v, i, v, deg)
    return best
if __name__ == '__main__':
    hyp = sys.argv[1]; rng = np.random.default_rng(int(sys.argv[2])); R_ = int(sys.argv[3]); S = int(sys.argv[4]); res = []; r = 0
    while r < R_:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0, hyp) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, hyp))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, hyp); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f deg=%.3f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_crossA_%s.pkl' % hyp, 'wb'))
    for b, P in res[:3]:
        o = Octa(P, b[1]); i = b[2]; m = (i - 1) % 4
        print("BEST", hyp, b); print("kv=%.3f kw=%.3f ku=%s nu=%s om=%s nu_m=%.3f kb=%.3f" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3), np.round(o.omega, 3), o.nu[m], o.ku[i] + o.ku[m] + o.kw))
