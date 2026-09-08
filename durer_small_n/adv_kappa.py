"""How small can kappa = k_u + k_u' be in an actual Case-B (below-base) overlap of opposite petals?  No hypothesis.
score = -kappa if the petals overlap by >= PEN*diam (penetration measured on V_i ∩ Omega, V_jj ∩ Omega), else -20 + sep.
usage: adv_kappa.py seed restarts steps"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import DELTA
from adv_caseB2 import sep_poly
from caseB_sub import geom, AMIN
PEN = 0.005
def score(o, i, detail=False):
    j, jj = (i + 1) % 4, (i + 2) % 4
    if o.ku[j] + o.ku[jj] < o.nu[j]: return None
    g = geom(o, i)
    if g is None: return None
    if g['SW'] >= np.pi: return -30.0 - (g['SW'] - np.pi)
    a2 = o.scale ** 2; Xi, Xjj = g['Xi'], g['Xjj']
    ai = poly_area(Xi) / a2 if len(Xi) >= 3 else 0.0; ajj = poly_area(Xjj) / a2 if len(Xjj) >= 3 else 0.0
    if ai < AMIN or ajj < AMIN: return -25.0 + min(ai, AMIN) + min(ajj, AMIN)
    sep = sep_poly(Xi, Xjj) / o.scale
    if sep < PEN: return -20.0 + sep
    return -(o.ku[j] + o.ku[jj])
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
    seeds = [d['P'] for d in pickle.load(open('cases_opp/cases.pkl', 'rb'))]
    while r < R_:
        P0 = seeds[r] if r < len(seeds) else rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f deg=%.3f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_kappa.pkl', 'wb'))
    from caseB_sub import describe
    for b, P in res[:4]:
        o = Octa(P, b[1]); i = b[2]; print("BEST", b, "kappa=%.4f (2pi=%.4f)" % (-b[3], 2 * np.pi)); describe(o, i)
