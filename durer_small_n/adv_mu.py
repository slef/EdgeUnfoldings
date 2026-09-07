"""Adversarial: maximise nu_i + mu_j - pi (mu_j = angle(u_j, v, c*)) under HYP and Case A (kappa_j+kappa_jj < nu_j).
Positive value = the wedge of V_i at v reaches past the 'up' direction of M (necessary for (i') to fail near v).
usage: adv_mu.py HYP seed restarts steps"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import violation, DELTA
from cstar import rotate_about
def value(o, i):
    k = (i - 1) % 4; net = o.Z(k); j, jj = (i + 1) % 4, (i + 2) % 4
    Vi, Vj = net[('V', i)], net[('V', j)]; uj, ujj, vj = Vj[2], Vj[1], Vj[0]; kj, kjj = o.ku[j], o.ku[jj]; kap = kj + kjj
    if kap >= o.nu[j]: return None
    cand = [sg for sg in (1, -1) if np.linalg.norm(rotate_about(Vi[:1], uj, -sg * kj)[0] - vj) < 1e-7 * o.scale]
    if len(cand) != 1: return None
    sgn = cand[0]
    def R(X): return rotate_about(rotate_about(X, uj, sgn * kj), ujj, sgn * kjj)
    A = rot(sgn * kap); b = R(np.zeros((1, 2)))[0]; cs = np.linalg.solve(np.eye(2) - A, b)
    mu_j = angle_at(vj, uj, cs); mu_jj = angle_at(vj, ujj, cs)
    return max(o.nu[i] + mu_j, o.nu[jj] + mu_jj) - np.pi
def best_config(P, hyp):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            val = value(o, i)
            if val is None: continue
            sc = val - 10 * violation(o, i, hyp) - 10 * deg
            if best is None or sc > best[0]: best = (sc, o.v, i, val)
    return best
if __name__ == '__main__':
    hyp = sys.argv[1]; rng = np.random.default_rng(int(sys.argv[2])); R_ = int(sys.argv[3]); S = int(sys.argv[4]); res = []; r = 0
    while r < R_:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0, hyp) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, hyp))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, hyp); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_mu_%s.pkl' % hyp, 'wb'))
    b, P = res[0]; o = Octa(P, b[1]); i = b[2]
    print("BEST", hyp, b); print("kv=%.3f kw=%.3f ku=%s nu=%s" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3)))
