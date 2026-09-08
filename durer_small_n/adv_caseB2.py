"""Case B (kappa_u + kappa_u' >= nu_j) under HYP: adversarial closeness of the parts of the outer petals INSIDE D
(the double-outward wedge of the cut-edge lines), each required to have area >= AMIN * diam^2.
usage: adv_caseB2.py HYP seed restarts steps [AMIN]"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import violation, DELTA
from adv_sep import clipped_parts
AMIN = 1e-3
def sep_poly(A, B):
    pen = np.inf
    for T in (A, B):
        e = np.roll(T, -1, axis=0) - T; nn = np.stack([-e[:, 1], e[:, 0]], -1); nn /= np.linalg.norm(nn, axis=-1, keepdims=True) + 1e-300
        p1 = nn @ A.T; p2 = nn @ B.T; pen = min(pen, (np.minimum(p1.max(1), p2.max(1)) - np.maximum(p1.min(1), p2.min(1))).min())
    return pen
def score(o, i):
    j, jj = (i + 1) % 4, (i + 2) % 4
    if o.ku[j] + o.ku[jj] < o.nu[j]: return None
    Xi, Xjj = clipped_parts(o, i); a2 = o.scale ** 2
    ai = poly_area(Xi) / a2 if len(Xi) >= 3 else 0.0; ajj = poly_area(Xjj) / a2 if len(Xjj) >= 3 else 0.0
    if ai < AMIN or ajj < AMIN: return -1.0 + min(ai, AMIN) + min(ajj, AMIN)     # reward growing the parts
    return sep_poly(Xi, Xjj) / o.scale
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
    hyp = sys.argv[1]; rng = np.random.default_rng(int(sys.argv[2])); R_ = int(sys.argv[3]); S = int(sys.argv[4])
    if len(sys.argv) > 5: AMIN = float(sys.argv[5])
    res = []; r = 0
    while r < R_:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0, hyp) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, hyp))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, hyp); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f deg=%.3f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_caseB2_%s.pkl' % hyp, 'wb'))
    b, P = res[0]; o = Octa(P, b[1]); i = b[2]; j, jj = (i + 1) % 4, (i + 2) % 4
    print("BEST", hyp, b); print("kv=%.3f kw=%.3f ku=%s nu=%s om=%s" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3), np.round(o.omega, 3)))
    SW = o.bW[j] + o.bWp[i] + o.bWp[j] + o.bW[jj]
    print("kappa=%.3f nu_j=%.3f SigmaW=%.3f phi=%.3f psi=%.3f aVp_i=%.3f aV_jj=%.3f" % (o.ku[j] + o.ku[jj], o.nu[j], SW, o.aV[j], o.aVp[j], o.aVp[i], o.aV[jj]))
