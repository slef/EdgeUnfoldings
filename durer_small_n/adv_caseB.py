"""Case B (kappa_u + kappa_u' >= nu_j): adversarial closeness of the BELOW-BASE parts of the outer petals under HYP.
score = separation(V_i ∩ {w side of base}, V_jj ∩ {w side of base}) / diam  (-1 if a part is empty); guards as usual.
usage: adv_caseB.py HYP seed restarts steps"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import separation, violation, DELTA
from cstar import signed_side

def halfplane_poly(P0, n, big):
    d = np.array([n[1], -n[0]]); a = P0 - big * d; b = P0 + big * d
    return np.array([a, b, b + big * n, a + big * n])

def parts_below(o, i):
    k = (i - 1) % 4; net = o.Z(k); j, jj = (i + 1) % 4, (i + 2) % 4
    Vi, Vj, Vjj = net[('V', i)], net[('V', j)], net[('V', jj)]
    uj, ujj, vj = Vj[2], Vj[1], Vj[0]; base = ujj - uj; dd = base / np.linalg.norm(base)
    n = np.array([-dd[1], dd[0]]); n *= -np.sign(np.dot(vj - uj, n))          # normal pointing to w's side
    hp = halfplane_poly(uj, n, 10 * o.scale)
    return clip_convex(Vi, hp), clip_convex(Vjj, hp)

def caseB_score(o, i):
    j, jj = (i + 1) % 4, (i + 2) % 4; kap = o.ku[j] + o.ku[jj]
    if kap < o.nu[j]: return None
    Xi, Xjj = parts_below(o, i)
    tiny = 1e-6 * o.scale ** 2; ei = len(Xi) < 3 or poly_area(Xi) < tiny; ejj = len(Xjj) < 3 or poly_area(Xjj) < tiny
    if ei or ejj: return -1.0 - 0.1 * (int(ei) + int(ejj))
    # separation of two convex polygons (SAT on all edges)
    def sep(A, B):
        pen = np.inf
        for T in (A, B):
            e = np.roll(T, -1, axis=0) - T; nn = np.stack([-e[:, 1], e[:, 0]], -1); nn /= np.linalg.norm(nn, axis=-1, keepdims=True) + 1e-300
            p1 = nn @ A.T; p2 = nn @ B.T; pen = min(pen, (np.minimum(p1.max(1), p2.max(1)) - np.maximum(p1.min(1), p2.min(1))).min())
        return pen   # >0 overlap depth, <0 gap along the best axis
    return sep(Xi, Xjj) / o.scale

B1 = False
def best_config(P, hyp):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            v = caseB_score(o, i)
            if v is None: continue
            j_, jj_ = (i + 1) % 4, (i + 2) % 4; SW = o.bW[j_] + o.bWp[i] + o.bWp[j_] + o.bW[jj_]
            sc = v - 10 * violation(o, i, hyp) - 10 * deg - (10 * max(0.0, SW - np.pi + 0.02) if B1 else 0.0)
            if best is None or sc > best[0]: best = (sc, o.v, i, v, deg)
    return best

if __name__ == '__main__':
    hyp = sys.argv[1]; rng = np.random.default_rng(int(sys.argv[2])); R_ = int(sys.argv[3]); S = int(sys.argv[4]); res = []; r = 0
    B1 = len(sys.argv) > 5 and sys.argv[5] == "B1"; globals()["B1"] = B1
    while r < R_:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0, hyp) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, hyp))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, hyp); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f deg=%.3f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_caseB_%s%s.pkl' % (hyp, '_B1' if B1 else ''), 'wb'))
    b, P = res[0]; o = Octa(P, b[1]); i = b[2]; j, jj = (i + 1) % 4, (i + 2) % 4
    print("BEST", hyp, b); print("kv=%.3f kw=%.3f ku=%s nu=%s om=%s" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3), np.round(o.omega, 3)))
    SW = o.bW[j] + o.bWp[i] + o.bWp[j] + o.bW[jj]
    print("kappa=%.3f nu_j=%.3f SigmaW=%.3f  phi=%.3f psi=%.3f aVp_i=%.3f aV_jj=%.3f" % (o.ku[j] + o.ku[jj], o.nu[j], SW, o.aV[j], o.aVp[j], o.aVp[i], o.aV[jj]))
