"""Adversarial search on the exact angular criterion of the c*-argument: score = eps_i + eps_jj - kappa (must be < 0).
usage: adv_eps.py HYP seed restarts steps"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import violation, DELTA
from cstar import analyse
def best_config(P, hyp):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            r = analyse(o, i)
            if r is None: continue
            val = max(r['eps_i'], 0) + max(r['eps_jj'], 0) - r['kappa']
            sc = val - 10 * violation(o, i, hyp) - 10 * deg
            if best is None or sc > best[0]: best = (sc, o.v, i, val, r['eps_i'], r['eps_jj'], r['kappa'])
    return best
if __name__ == '__main__':
    hyp = sys.argv[1]; rng = np.random.default_rng(int(sys.argv[2])); R_ = int(sys.argv[3]); S = int(sys.argv[4]); res = []; r = 0
    while r < R_:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0, hyp) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, hyp))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, hyp); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f eps_i=%.4f eps_jj=%.4f kappa=%.4f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_eps_%s.pkl' % hyp, 'wb'))
    b, P = res[0]; o = Octa(P, b[1]); i = b[2]
    print("BEST", hyp, b); print("kv=%.3f kw=%.3f ku=%s nu=%s" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3)))
