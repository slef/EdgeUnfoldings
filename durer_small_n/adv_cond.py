"""Adversarial search on the necessary conditions for an opposite-petal meeting, under a hypothesis.
usage: adv_cond.py COND HYP seed restarts steps
COND:  Ri   = max_tau [sin nu_i sin(nu_j-k_j-tau) - sin nu_j sin(nu_i+tau)]   (V_i reaches vertical wedge of V_j)
       ang  = nu_j - k_j - k_jj                                              (rays from u_j,u_jj converge above)
       SW   = pi - SigmaW                                                    (below-base meeting possible)
       Ri2  = min(margin Ri, margin Rjj)                                     (both petals reach)
HYP as in adv_opp.py (H1,H2,H3).  Guards: edges >= 0.05 diam, curvatures >= 0.05.
"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import violation, DELTA

def margin_R(nu_i, nu_j, kj, amax):
    if kj >= nu_j: return -(kj - nu_j) - 1.0
    taus = np.linspace(0, max(min(amax, nu_j - kj), 1e-9), 200)
    return float((np.sin(nu_i) * np.sin(nu_j - kj - taus) - np.sin(nu_j) * np.sin(nu_i + taus)).max())

def cond_value(o, i, cond):
    j, jj = (i + 1) % 4, (i + 2) % 4
    if cond == 'Ri': return margin_R(o.nu[i], o.nu[j], o.ku[j], o.aVp[i])
    if cond == 'Ri2': return min(margin_R(o.nu[i], o.nu[j], o.ku[j], o.aVp[i]), margin_R(o.nu[jj], o.nu[j], o.ku[jj], o.aV[jj]))
    if cond == 'ang': return o.nu[j] - o.ku[j] - o.ku[jj]
    if cond == 'SW': return np.pi - (o.bW[j] + o.bWp[i] + o.bWp[j] + o.bW[jj])

def best_config(P, cond, hyp):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            vio = violation(o, i, hyp); val = cond_value(o, i, cond)
            sc = val - 10 * vio - 10 * deg
            if best is None or sc > best[0]: best = (sc, o.v, i, val, vio, deg)
    return best

if __name__ == '__main__':
    cond, hyp = sys.argv[1], sys.argv[2]; rng = np.random.default_rng(int(sys.argv[3])); R = int(sys.argv[4]); S = int(sys.argv[5])
    results = []; r = 0
    while r < R:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, cond, hyp))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, cond, hyp); results.append((b, P))
        print("restart %d: score %.5f v=%d i=%d val=%.5f viol=%.4f deg=%.4f" % ((r,) + b), flush=True)
    results.sort(key=lambda t: -t[0][0])
    pickle.dump(results, open('adv_cond_%s_%s.pkl' % (cond, hyp), 'wb'))
    b, P = results[0]; o = Octa(P, b[1]); i = b[2]; j, jj = (i + 1) % 4, (i + 2) % 4
    print("BEST", cond, hyp, b)
    print("kv=%.3f kw=%.3f ku=%s nu=%s omega=%s" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3), np.round(o.omega, 3)))
    print("i=%d: nu_i=%.3f nu_j=%.3f nu_jj=%.3f k_j=%.3f k_jj=%.3f aVp_i=%.3f aV_jj=%.3f 2nu_j-k_j=%.3f" % (i, o.nu[i], o.nu[j], o.nu[jj], o.ku[j], o.ku[jj], o.aVp[i], o.aV[jj], 2 * o.nu[j] - o.ku[j]))
