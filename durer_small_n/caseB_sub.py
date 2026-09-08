"""Case B sub-cases.  A = line(u,u_i) (outer edge of W_i), C = line(u',u_k) (outer edge of W_jj, u_k = slit copy); V_i lies beyond A
and V_jj beyond C (away from w), so a meeting lies in the wedge Omega = H_A ∩ H_C.  A Case-B meeting needs SigmaW < pi (the four fan
angles at u, u'); then Omega is the wedge at X = A ∩ C opposite the triangle u u' X.  V_i reaches Omega iff u_i is past X on A ('f')
or v_i is in Omega ('a'); same for V_jj.  (Old versions tested "X on w's side" with the sign of a point ON the line: vacuous.)
  stat HYP seed N                            -> counts of sub-cases; seeds saved to caseB_sub_stat_HYP.pkl
  adv HYP SUB seed restarts steps [seeded]   -> adversarial closeness of V_i∩Omega and V_jj∩Omega inside sub-case SUB = ri_rjj,
                                                ri, rjj in {a, f, fa} (exactly that mechanism); 'seeded' starts from the stat seeds."""
import numpy as np, sys, pickle, collections
from octa import *
from adv_opp import violation, DELTA
from adv_sep import halfplane_poly
from adv_caseB2 import sep_poly
AMIN = 1e-3
def geom(o, i):
    j, jj = (i + 1) % 4, (i + 2) % 4; k = (i - 1) % 4; net = o.Z(k)
    Vi, Vj, Vjj, Wi, Wjj = net[('V', i)], net[('V', j)], net[('V', jj)], net[('W', i)], net[('W', jj)]
    u, up = Vj[2], Vj[1]; ui = Wi[1]; ujj1 = Wjj[2]; vi, vjj = Vi[0], Vjj[0]; w = np.zeros(2)
    SW = o.bW[j] + o.bWp[i] + o.bWp[j] + o.bW[jj]
    dA = ui - u; dC = ujj1 - up; M = np.array([dA, -dC]).T
    if abs(np.linalg.det(M)) < 1e-14: return None
    t = np.linalg.solve(M, up - u); X = u + t[0] * dA
    def sdist(P0, d, q):                      # signed distance from line (P0,d), positive away from w
        n = np.array([-d[1], d[0]]) / np.linalg.norm(d); s = -np.sign(np.dot(w - P0, n)); return s * np.dot(q - P0, n)
    big = 10 * o.scale
    def far_side(P0, P1):
        d = (P1 - P0) / np.linalg.norm(P1 - P0); n = np.array([-d[1], d[0]]); n *= -np.sign(np.dot(w - P0, n)); return halfplane_poly(P0, n, big)
    HA, HC = far_side(u, ui), far_side(up, ujj1)
    Xi = clip_convex(clip_convex(Vi, HA), HC); Xjj = clip_convex(clip_convex(Vjj, HA), HC)
    return dict(X=X, SW=SW, vi_beyondC=sdist(up, dC, vi) / o.scale, vjj_beyondA=sdist(u, dA, vjj) / o.scale,
                ui_pastX=(1 - t[0]) * np.linalg.norm(dA) / o.scale, ujj1_pastX=(1 - t[1]) * np.linalg.norm(dC) / o.scale,
                Vi=Vi, Vjj=Vjj, Xi=Xi, Xjj=Xjj, u=u, up=up, ui=ui, ujj1=ujj1, w=w, dA=dA, dC=dC)
def sub_of(g):
    ri = ('f' if g['ui_pastX'] > 0 else '') + ('a' if g['vi_beyondC'] > 0 else '')
    rjj = ('f' if g['ujj1_pastX'] > 0 else '') + ('a' if g['vjj_beyondA'] > 0 else '')
    return ri, rjj
def score(o, i, sub):
    """closeness of V_i∩Ω, V_jj∩Ω (positive = overlap) minus penalties for leaving the sub-case."""
    j, jj = (i + 1) % 4, (i + 2) % 4
    if o.ku[j] + o.ku[jj] < o.nu[j]: return None
    g = geom(o, i)
    if g is None: return None
    if g['SW'] >= np.pi: return -1.0 - (g['SW'] - np.pi)
    ri, rjj = sub.split('_'); pen = 0.0
    for r, fkey, akey in ((ri, 'ui_pastX', 'vi_beyondC'), (rjj, 'ujj1_pastX', 'vjj_beyondA')):
        for letter, key in (('f', fkey), ('a', akey)):
            pen += max(0.0, -g[key]) if letter in r else max(0.0, g[key])      # want key>0 iff letter in r
    a2 = o.scale ** 2; Xi, Xjj = g['Xi'], g['Xjj']
    ai = poly_area(Xi) / a2 if len(Xi) >= 3 else 0.0; ajj = poly_area(Xjj) / a2 if len(Xjj) >= 3 else 0.0
    if ai < AMIN or ajj < AMIN: return -0.5 + min(ai, AMIN) + min(ajj, AMIN) - 10 * pen
    return sep_poly(Xi, Xjj) / o.scale - 10 * pen
def best_config(P, hyp, sub):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            v = score(o, i, sub)
            if v is None: continue
            sc = v - 10 * violation(o, i, hyp) - 10 * deg
            if best is None or sc > best[0]: best = (sc, o.v, i, v, deg)
    return best
def describe(o, i):
    j, jj = (i + 1) % 4, (i + 2) % 4; g = geom(o, i)
    print("kv=%.3f kw=%.3f ku=%s nu=%s om=%s kappa=%.3f nu_j=%.3f SigmaW=%.3f sub=%s  vi>C=%.3f vjj>A=%.3f ui>X=%.3f ujj1>X=%.3f" % (
        o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3), np.round(o.omega, 3), o.ku[j] + o.ku[jj], o.nu[j], g['SW'], sub_of(g),
        g['vi_beyondC'], g['vjj_beyondA'], g['ui_pastX'], g['ujj1_pastX']))
if __name__ == '__main__':
    mode, hyp = sys.argv[1], sys.argv[2]
    if mode == 'stat':
        rng = np.random.default_rng(int(sys.argv[3])); N = int(sys.argv[4]); st = collections.Counter(); seeds = []
        for P, faces, adj in random_octahedra(rng, N):
            for o in all_apexes(P, faces, adj):
                deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
                for i in range(4):
                    j, jj = (i + 1) % 4, (i + 2) % 4
                    if o.ku[j] + o.ku[jj] < o.nu[j] or violation(o, i, hyp) > 0: continue
                    g = geom(o, i)
                    if g is None: continue
                    st['caseB'] += 1
                    if g['SW'] >= np.pi: st['SigmaW >= pi (no meeting possible)'] += 1; continue
                    ri, rjj = sub_of(g); both = bool(ri) and bool(rjj)
                    st['SigmaW < pi'] += 1; st['both reach'] += both
                    if both: st['both reach: V_i via %s, V_jj via %s' % (ri, rjj)] += 1; st['both reach & nondeg'] += (deg == 0); seeds.append((P, o.v, i, ri + '_' + rjj))
        for a, b in sorted(st.items()): print("%-48s %d" % (a, b))
        pickle.dump(seeds, open('caseB_sub_stat_%s.pkl' % hyp, 'wb'))
    elif mode == 'adv':
        sub = sys.argv[3]; rng = np.random.default_rng(int(sys.argv[4])); R_ = int(sys.argv[5]); S = int(sys.argv[6]); res = []; r = 0
        seeds = [t[0] for t in pickle.load(open('caseB_sub_stat_%s.pkl' % hyp, 'rb')) if t[3] == sub] if len(sys.argv) > 7 else []
        while r < R_:
            P0 = seeds[r] if r < len(seeds) else rand_points(6, rng)
            if octa_structure(P0) is None or best_config(P0, hyp, sub) is None: continue
            r += 1
            f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, hyp, sub))
            P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
            b = best_config(P, hyp, sub); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f deg=%.3f" % ((r,) + b), flush=True)
        res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('caseB_sub_%s_%s.pkl' % (hyp, sub), 'wb'))
        for b, P in res[:3]:
            o = Octa(P, b[1]); print("BEST", hyp, sub, b); describe(o, b[2])
