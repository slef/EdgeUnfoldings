"""Adversarial test of the side conditions (i'),(ii') of the c*-argument under hypothesis HYP.
score = max signed excursion (in units of diameter) of V_i^fan∩{above} into u_jj's side of M, or of V_jj^fan∩{above}
into u_j's side of M.  Positive = condition fails.   usage: adv_cstar.py HYP seed restarts steps"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import violation, DELTA
from cstar import rotate_about, signed_side

def excursion(o, i):
    k = (i - 1) % 4; net = o.Z(k); j, jj = (i + 1) % 4, (i + 2) % 4
    Vi, Vj, Vjj = net[('V', i)], net[('V', j)], net[('V', jj)]
    uj, ujj, vj = Vj[2], Vj[1], Vj[0]; kj, kjj = o.ku[j], o.ku[jj]; kap = kj + kjj
    if kap >= o.nu[j]: return None
    base = ujj - uj
    cand = [sg for sg in (1, -1) if np.linalg.norm(rotate_about(Vi[:1], uj, -sg * kj)[0] - vj) < 1e-7 * o.scale]
    if len(cand) != 1: return None
    sgn = cand[0]
    Vi_fan = rotate_about(Vi, uj, -sgn * kj); Vjj_fan = rotate_about(Vjj, ujj, sgn * kjj)
    def R(X): return rotate_about(rotate_about(X, uj, sgn * kj), ujj, sgn * kjj)
    A = rot(sgn * kap); b = R(np.zeros((1, 2)))[0]; cstar = np.linalg.solve(np.eye(2) - A, b)
    sv = np.sign(signed_side(uj, base, vj[None])[0])
    def part_above(T):
        big = 10 * o.scale; dd = base / np.linalg.norm(base); n = sv * np.array([-dd[1], dd[0]])
        hp = np.array([uj - big * dd, uj + big * dd, uj + big * dd + big * n, uj - big * dd + big * n])
        if sv < 0: hp = hp[::-1]
        return clip_convex(T, hp)
    Xi = part_above(Vi_fan); Xjj = part_above(Vjj_fan)
    d = vj - cstar; dn = d / np.linalg.norm(d)
    su = np.sign(signed_side(cstar, dn, uj[None])[0])
    ei = (-su * signed_side(cstar, dn, Xi)).max() if len(Xi) else -1.0
    ejj = (su * signed_side(cstar, dn, Xjj)).max() if len(Xjj) else -1.0
    return max(ei, ejj) / o.scale

def best_config(P, hyp):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            e = excursion(o, i)
            if e is None: continue
            sc = e - 10 * violation(o, i, hyp) - 10 * deg
            if best is None or sc > best[0]: best = (sc, o.v, i, e)
    return best

if __name__ == '__main__':
    hyp = sys.argv[1]; rng = np.random.default_rng(int(sys.argv[2])); R_ = int(sys.argv[3]); S = int(sys.argv[4]); res = []; r = 0
    while r < R_:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0, hyp) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, hyp))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, hyp); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d exc=%.5f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_cstar_%s.pkl' % hyp, 'wb'))
    b, P = res[0]; o = Octa(P, b[1]); i = b[2]; j, jj = (i + 1) % 4, (i + 2) % 4
    print("BEST", hyp, b); print("kv=%.3f kw=%.3f ku=%s nu=%s" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3)))
