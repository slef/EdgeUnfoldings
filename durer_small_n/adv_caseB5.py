"""Case B sharpest region: the wedge at X = A ∩ C (A = line(u,u_i) of W_i, C = line(u',u_jj1) of W_jj) on the side
away from w, which exists only if SigmaW < pi.  score = separation of V_i ∩ wedge and V_jj ∩ wedge (both with area
>= AMIN diam^2), maximised under HYP and Case B.  Configurations with SigmaW >= pi get score -1 - (SigmaW - pi).
usage: adv_caseB5.py HYP seed restarts steps"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import violation, DELTA
from adv_sep import halfplane_poly
from adv_caseB2 import sep_poly
AMIN = 1e-3
def score(o, i, detail=False):
    j, jj = (i + 1) % 4, (i + 2) % 4
    if o.ku[j] + o.ku[jj] < o.nu[j]: return None
    SW = o.bW[j] + o.bWp[i] + o.bWp[j] + o.bW[jj]
    if SW >= np.pi: return -1.0 - (SW - np.pi)
    k = (i - 1) % 4; net = o.Z(k); Vi, Vj, Vjj, Wi, Wjj = net[('V', i)], net[('V', j)], net[('V', jj)], net[('W', i)], net[('W', jj)]
    u, up = Vj[2], Vj[1]; ui = Wi[1]; ujj1 = Wjj[2]; w = np.zeros(2); big = 10 * o.scale
    def far_side(P0, P1):
        d = (P1 - P0) / np.linalg.norm(P1 - P0); n = np.array([-d[1], d[0]]); n *= -np.sign(np.dot(w - P0, n)); return halfplane_poly(P0, n, big)
    HA, HC = far_side(u, ui), far_side(up, ujj1)
    Xi = clip_convex(clip_convex(Vi, HA), HC); Xjj = clip_convex(clip_convex(Vjj, HA), HC)
    a2 = o.scale ** 2; ai = poly_area(Xi) / a2 if len(Xi) >= 3 else 0.0; ajj = poly_area(Xjj) / a2 if len(Xjj) >= 3 else 0.0
    if ai < AMIN or ajj < AMIN: return -0.5 + min(ai, AMIN) + min(ajj, AMIN)
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
    hyp = sys.argv[1]; rng = np.random.default_rng(int(sys.argv[2])); R_ = int(sys.argv[3]); S = int(sys.argv[4]); res = []; r = 0
    while r < R_:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0, hyp) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, hyp))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, hyp); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f deg=%.3f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_caseB5_%s.pkl' % hyp, 'wb'))
    b, P = res[0]; o = Octa(P, b[1]); i = b[2]; j, jj = (i + 1) % 4, (i + 2) % 4
    SW = o.bW[j] + o.bWp[i] + o.bWp[j] + o.bW[jj]
    print("BEST", hyp, b); print("kv=%.3f kw=%.3f ku=%s nu=%s om=%s kappa=%.3f nu_j=%.3f SigmaW=%.3f" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3), np.round(o.omega, 3), o.ku[j] + o.ku[jj], o.nu[j], SW))
