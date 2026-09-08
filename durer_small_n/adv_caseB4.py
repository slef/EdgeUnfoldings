"""Case B separator test: does the line A = (u, u_i) [outer edge of W_i] separate V_i from V_jj, or C = (u', u_jj1)
[outer edge of W_jj] separate V_jj from V_i?  score = min over the two candidates of the max penetration of the
other petal across the line (in units of diam); <= 0 means one of them separates.  Maximised under HYP, Case B only.
usage: adv_caseB4.py HYP seed restarts steps"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import violation, DELTA
from cstar import signed_side
def score(o, i):
    j, jj = (i + 1) % 4, (i + 2) % 4
    if o.ku[j] + o.ku[jj] < o.nu[j]: return None
    k = (i - 1) % 4; net = o.Z(k)
    Vi, Vj, Vjj, Wi, Wjj = net[('V', i)], net[('V', j)], net[('V', jj)], net[('W', i)], net[('W', jj)]
    u, up = Vj[2], Vj[1]; ui = Wi[1]; ujj1 = Wjj[2]; w = np.zeros(2)
    def pen(P0, P1, T):   # penetration of triangle T across line (P0,P1) into the side NOT containing w
        d = (P1 - P0) / np.linalg.norm(P1 - P0); s = signed_side(P0, d, T); sw = signed_side(P0, d, w[None])[0]
        return (-np.sign(sw) * s).max() / o.scale
    return min(pen(u, ui, Vjj), pen(up, ujj1, Vi))
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
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_caseB4_%s.pkl' % hyp, 'wb'))
    b, P = res[0]; o = Octa(P, b[1]); i = b[2]; j, jj = (i + 1) % 4, (i + 2) % 4
    print("BEST", hyp, b); print("kv=%.3f kw=%.3f ku=%s nu=%s om=%s kappa=%.3f nu_j=%.3f" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3), np.round(o.omega, 3), o.ku[j] + o.ku[jj], o.nu[j]))
