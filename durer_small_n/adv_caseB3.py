"""Case B necessary condition (N): u_i beyond L' = line(u', v_{j+1}) AND u_{jj+1} beyond L = line(u, v_i), where
'beyond' = the open side not containing V_j.  score = min(dist_beyond(u_i, L'), dist_beyond(u_jj1, L)) / diam,
maximised under HYP and kappa_u + kappa_u' >= nu_j.   usage: adv_caseB3.py HYP seed restarts steps | check"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import violation, DELTA
from adv_sep import geometry
def cond(o, i):
    j, jj = (i + 1) % 4, (i + 2) % 4
    if o.ku[j] + o.ku[jj] < o.nu[j]: return None
    g = geometry(o, i)
    d_i = np.dot(g['ui'] - g['ujj'], g['n2']); d_jj = np.dot(g['ujj1'] - g['uj'], g['n1'])   # n1,n2 point outward
    return min(d_i, d_jj) / o.scale
def best_config(P, hyp):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            v = cond(o, i)
            if v is None: continue
            sc = v - 10 * violation(o, i, hyp) - 10 * deg
            if best is None or sc > best[0]: best = (sc, o.v, i, v, deg)
    return best
if __name__ == '__main__':
    if sys.argv[1] == 'check':
        from vwedge import side
        cases = pickle.load(open('cases_opp/cases.pkl', 'rb')); n = 0
        for d in cases:
            o = Octa(d['P'], d['v']); k = d['k']; nm = d['pair']; i = k if nm == 'V_k-V_k+2' else (k + 1) % 4; j = (i + 1) % 4
            net = o.Z(k); Vj = net[('V', j)]; X = o.intersection(k, nm)
            if all(side(Vj[1], Vj[2], q) > 0 for q in X): continue
            n += 1; print("below-base overlap: cond N = %.4f (must be > 0)" % cond(o, i))
        sys.exit()
    hyp = sys.argv[1]; rng = np.random.default_rng(int(sys.argv[2])); R_ = int(sys.argv[3]); S = int(sys.argv[4]); res = []; r = 0
    while r < R_:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0, hyp) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, hyp))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, hyp); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f deg=%.3f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_caseB3_%s.pkl' % hyp, 'wb'))
    b, P = res[0]; o = Octa(P, b[1]); i = b[2]; j, jj = (i + 1) % 4, (i + 2) % 4
    print("BEST", hyp, b); print("kv=%.3f kw=%.3f ku=%s nu=%s om=%s kappa=%.3f nu_j=%.3f" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3), np.round(o.omega, 3), o.ku[j] + o.ku[jj], o.nu[j]))
