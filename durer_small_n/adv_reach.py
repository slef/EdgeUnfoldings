"""Under HYP (e.g. H3R = (H)+slit rule), in Case B with SigmaW < pi, how far can a single petal reach into Omega?
mode i_a : score = (v_i beyond C)/scale         mode i_f : score = (u_i past X)/scale
mode jj_a: score = (v_jj beyond A)/scale        mode jj_f: score = (u_k past X)/scale
usage: adv_reach.py HYP mode seed restarts steps [SWMAX]"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import violation, DELTA
from caseB_sub import geom
SWMAX = np.pi
KEY = {'i_a': 'vi_beyondC', 'i_f': 'ui_pastX', 'jj_a': 'vjj_beyondA', 'jj_f': 'ujj1_pastX'}
def score(o, i, mode):
    j, jj = (i + 1) % 4, (i + 2) % 4
    if o.ku[j] + o.ku[jj] < o.nu[j]: return None
    g = geom(o, i)
    if g is None: return None
    if g['SW'] >= SWMAX: return -1.0 - (g['SW'] - SWMAX)
    return g[KEY[mode]]
def best_config(P, hyp, mode):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            v = score(o, i, mode)
            if v is None: continue
            sc = v - 10 * violation(o, i, hyp) - 10 * deg
            if best is None or sc > best[0]: best = (sc, o.v, i, v, deg)
    return best
if __name__ == '__main__':
    hyp, mode = sys.argv[1], sys.argv[2]
    if len(sys.argv) > 6: SWMAX = float(sys.argv[6])
    rng = np.random.default_rng(int(sys.argv[3])); R_ = int(sys.argv[4]); S = int(sys.argv[5]); res = []; r = 0
    while r < R_:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0, hyp, mode) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, hyp, mode))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, hyp, mode); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f deg=%.3f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_reach_%s_%s%s.pkl' % (hyp, mode, '' if len(sys.argv) <= 6 else '_sw'), 'wb'))
    from caseB_sub import describe
    for b, P in res[:3]:
        o = Octa(P, b[1]); i = b[2]; print("BEST", hyp, mode, b); describe(o, i)
