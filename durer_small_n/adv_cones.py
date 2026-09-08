"""Apex-cone test: F = cone(v_i; u, u_i) ∩ cone(v_jj; u', u_m').  depth(F) = max t s.t. a point x has signed distance
>= t to all four boundary lines (LP), in units of diam; F nonempty (with interior) iff depth > 0.
Maximised adversarially in CASE (A: kappa < nu_j, B: kappa >= nu_j) under HYP.  usage: adv_cones.py A|B HYP seed restarts steps | check"""
import numpy as np, sys, pickle
from scipy.optimize import linprog
from octa import *
from adv_opp import violation, DELTA
def cone_lines(o, i):
    k = (i - 1) % 4; net = o.Z(k); j, jj = (i + 1) % 4, (i + 2) % 4
    Vi, Vjj = net[('V', i)], net[('V', jj)]
    L = []
    for T, a, b in ((Vi, 0, 1), (Vi, 0, 2), (Vjj, 0, 2), (Vjj, 0, 1)):
        c = ({0, 1, 2} - {a, b}).pop(); d = (T[b] - T[a]) / np.linalg.norm(T[b] - T[a]); n = np.array([-d[1], d[0]]); n *= np.sign(np.dot(T[c] - T[a], n))
        L.append((n, np.dot(n, T[a])))          # half-plane n.x >= c
    return L
def depth(o, i):
    L = cone_lines(o, i); big = 20 * o.scale
    # maximise t: n_k.x - c_k >= t  ->  -n_k.x + t <= -c_k ; bounds x in box, t free (<= big)
    A = np.array([[-n[0], -n[1], 1.0] for n, c in L]); bvec = np.array([-c for n, c in L])
    r = linprog([0, 0, -1], A_ub=A, b_ub=bvec, bounds=[(-big, big), (-big, big), (-big, big)], method='highs')
    return (r.x[2] / o.scale) if r.success else -1.0
def score(o, i, case):
    j, jj = (i + 1) % 4, (i + 2) % 4; kap = o.ku[j] + o.ku[jj]
    if (case == 'A' and kap >= o.nu[j]) or (case == 'B' and kap < o.nu[j]): return None
    return depth(o, i)
def best_config(P, case, hyp):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            v = score(o, i, case)
            if v is None: continue
            sc = v - 10 * violation(o, i, hyp) - 10 * deg
            if best is None or sc > best[0]: best = (sc, o.v, i, v, deg)
    return best
if __name__ == '__main__':
    if sys.argv[1] == 'check':
        from vwedge import side
        cases = pickle.load(open('cases_opp/cases.pkl', 'rb')); out = []
        for d in cases:
            o = Octa(d['P'], d['v']); k = d['k']; nm = d['pair']; i = k if nm == 'V_k-V_k+2' else (k + 1) % 4; j = (i + 1) % 4
            net = o.Z(k); Vj = net[('V', j)]; X = o.intersection(k, nm); above = all(side(Vj[1], Vj[2], q) > 0 for q in X)
            out.append(('above' if above else 'below', round(depth(o, i), 4)))
        print(sorted(out)); sys.exit()
    case, hyp = sys.argv[1], sys.argv[2]; rng = np.random.default_rng(int(sys.argv[3])); R_ = int(sys.argv[4]); S = int(sys.argv[5]); res = []; r = 0
    while r < R_:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0, case, hyp) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, case, hyp))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, case, hyp); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f deg=%.3f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_cones_%s_%s.pkl' % (case, hyp), 'wb'))
    b, P = res[0]; o = Octa(P, b[1]); i = b[2]; j, jj = (i + 1) % 4, (i + 2) % 4
    print("BEST", case, hyp, b); print("kv=%.3f kw=%.3f ku=%s nu=%s kappa=%.3f nu_j=%.3f" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3), o.ku[j] + o.ku[jj], o.nu[j]))
