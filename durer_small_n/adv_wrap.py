"""Case A under HYP: adversarial max of  max(nu_i, nu_jj) - (pi - nu_j + kappa)   ('no wrap' condition; must stay < 0).
usage: adv_wrap.py HYP seed restarts steps"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import violation, DELTA
def val(o, i):
    j, jj = (i + 1) % 4, (i + 2) % 4; kap = o.ku[j] + o.ku[jj]
    if kap >= o.nu[j]: return None
    return max(o.nu[i], o.nu[jj]) - (np.pi - o.nu[j] + kap)
def best_config(P, hyp):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            v = val(o, i)
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
        b = best_config(P, hyp); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f" % ((r,) + b[:4]), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_wrap_%s.pkl' % hyp, 'wb'))
    b, P = res[0]; o = Octa(P, b[1]); i = b[2]; j, jj = (i + 1) % 4, (i + 2) % 4
    print("BEST", hyp, b); print("kv=%.3f ku=%s nu=%s kappa=%.3f nu_j=%.3f" % (o.kv, np.round(o.ku, 3), np.round(o.nu, 3), o.ku[j] + o.ku[jj], o.nu[j]))
