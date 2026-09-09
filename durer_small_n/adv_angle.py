"""Maximise (angle of V_jj at u_k) - SigmaW  [mode jj]  or (angle of V_i at u_i) - SigmaW [mode i] under HYP, Case B or not (CASEB=1/0).
The apex v_jj can only be in Omega if angle_{u_k} V_jj > SigmaW.   usage: adv_angle.py HYP mode CASEB seed restarts steps"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import violation, DELTA
def score(o, i, mode, caseB):
    j, jj, m = (i + 1) % 4, (i + 2) % 4, (i - 1) % 4
    if caseB and o.ku[j] + o.ku[jj] < o.nu[j]: return None
    SW = o.bW[j] + o.bWp[i] + o.bWp[j] + o.bW[jj]
    if SW >= np.pi: return -1.0 - (SW - np.pi)
    k = m; net = o.Z(k); ang = lambda P0, A, B: np.arccos(np.clip(np.dot(A - P0, B - P0) / np.linalg.norm(A - P0) / np.linalg.norm(B - P0), -1, 1))
    if mode == 'jj':
        Vjj = net[('V', jj)]; return ang(Vjj[1], Vjj[2], Vjj[0]) - SW      # angle at u_k = Vjj[1]
    if mode == 'jjb':
        Vjj = net[('V', jj)]; return ang(Vjj[1], Vjj[2], Vjj[0]) - (o.bWp[j] + o.bW[jj])   # f - beta
    if mode == 'jjh':
        return o.aVp[jj] - (o.bWp[j] + o.bW[jj]) / 2 - (o.bWp[i] + o.bW[j])   # f - beta/2 - alpha
    if mode != 'i': raise ValueError('unknown angle mode: ' + mode)
    # Z stores V_i as [v_i, u_{i+1}, u_i].  Historical *_i_* results
    # measured the other base angle and must not be reused for this claim.
    Vi = net[('V', i)]; return ang(Vi[2], Vi[1], Vi[0]) - SW
def best_config(P, hyp, mode, caseB):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            v = score(o, i, mode, caseB)
            if v is None: continue
            sc = v - 10 * violation(o, i, hyp) - 10 * deg
            if best is None or sc > best[0]: best = (sc, o.v, i, v, deg)
    return best
if __name__ == '__main__':
    hyp, mode, caseB = sys.argv[1], sys.argv[2], int(sys.argv[3]); rng = np.random.default_rng(int(sys.argv[4])); R_ = int(sys.argv[5]); S = int(sys.argv[6]); res = []; r = 0
    while r < R_:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0, hyp, mode, caseB) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, hyp, mode, caseB))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, hyp, mode, caseB); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f deg=%.3f" % ((r,) + b), flush=True)
    suffix = '_far_vertex_v2' if mode == 'i' else ''
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_angle_%s_%s_%d%s.pkl' % (hyp, mode, caseB, suffix), 'wb'))
    for b, P in res[:3]:
        o = Octa(P, b[1]); i = b[2]; j, jj, m = (i + 1) % 4, (i + 2) % 4, (i - 1) % 4
        print("BEST", hyp, mode, caseB, b); print("kv=%.3f kw=%.3f ku=%s nu=%s om=%s SW=%.3f" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3), np.round(o.omega, 3), o.bW[j] + o.bWp[i] + o.bWp[j] + o.bW[jj]))
