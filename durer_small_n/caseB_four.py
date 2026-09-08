"""Four-cut-edge region for the pair (V_i, V_jj) in Z_k (k = i-1): V_i lies on its side of BOTH cut-edge lines
(u v_i) and (u_i v_i); V_jj on its side of (u' v_jj) and (u_m' v_jj).  Any meeting lies in F = intersection of the
four half-planes.  Statistics under HYP for Case B triples: F empty?  V_i ∩ F and V_jj ∩ F both of positive area?
And adversarial closeness of V_i ∩ F, V_jj ∩ F.   usage: caseB_four.py stat HYP seed N   |   caseB_four.py adv HYP seed restarts steps"""
import numpy as np, sys, pickle, collections
from octa import *
from adv_opp import violation, DELTA
from adv_sep import halfplane_poly
from adv_caseB2 import sep_poly
AMIN = 1e-3
def four_region_parts(o, i):
    k = (i - 1) % 4; net = o.Z(k); j, jj = (i + 1) % 4, (i + 2) % 4
    Vi, Vj, Vjj = net[('V', i)], net[('V', j)], net[('V', jj)]     # V = [v, u_{x+1}, u_x]
    big = 10 * o.scale
    def hp_of(T, a, b):       # half-plane bounded by line through T[a], T[b] containing the third vertex of T
        c = ({0, 1, 2} - {a, b}).pop(); d = (T[b] - T[a]) / np.linalg.norm(T[b] - T[a]); n = np.array([-d[1], d[0]]); n *= np.sign(np.dot(T[c] - T[a], n)); return halfplane_poly(T[a], n, big)
    # Vi = [v_i, u (=u_{i+1}), u_i]; cut edges: v_i-u (idx 0,1) and v_i-u_i (idx 0,2)
    # Vjj = [v_jj, u_m' (=u_{jj+1}), u' (=u_jj)]; cut edges v_jj-u' (0,2) and v_jj-u_m' (0,1)
    H = [hp_of(Vi, 0, 1), hp_of(Vi, 0, 2), hp_of(Vjj, 0, 2), hp_of(Vjj, 0, 1)]
    Xi = Vi; Xjj = Vjj
    for h in H: Xi = clip_convex(Xi, h) if len(Xi) >= 3 else Xi; Xjj = clip_convex(Xjj, h) if len(Xjj) >= 3 else Xjj
    F = np.array([[-big, -big], [big, -big], [big, big], [-big, big]])
    for h in H: F = clip_convex(F, h) if len(F) >= 3 else F
    return Xi, Xjj, F
def score(o, i):
    j, jj = (i + 1) % 4, (i + 2) % 4
    if o.ku[j] + o.ku[jj] < o.nu[j]: return None
    Xi, Xjj, F = four_region_parts(o, i); a2 = o.scale ** 2
    ai = poly_area(Xi) / a2 if len(Xi) >= 3 else 0.0; ajj = poly_area(Xjj) / a2 if len(Xjj) >= 3 else 0.0
    if ai < AMIN or ajj < AMIN: return -0.5 + min(ai, AMIN) + min(ajj, AMIN)
    return sep_poly(Xi, Xjj) / o.scale
if __name__ == '__main__':
    mode, hyp = sys.argv[1], sys.argv[2]; rng = np.random.default_rng(int(sys.argv[3]))
    if mode == 'stat':
        N = int(sys.argv[4]); st = collections.Counter()
        for P, faces, adj in random_octahedra(rng, N):
            for o in all_apexes(P, faces, adj):
                deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
                for i in range(4):
                    j, jj = (i + 1) % 4, (i + 2) % 4
                    caseB = o.ku[j] + o.ku[jj] >= o.nu[j]
                    if violation(o, i, hyp) > 0: continue
                    Xi, Xjj, F = four_region_parts(o, i); a2 = o.scale ** 2
                    Fempty = len(F) < 3 or poly_area(F) < 1e-9 * a2
                    both = (len(Xi) >= 3 and poly_area(Xi) > AMIN * a2) and (len(Xjj) >= 3 and poly_area(Xjj) > AMIN * a2)
                    for tag in (['caseB'] if caseB else ['caseA']) + (['caseB nondeg'] if caseB and deg == 0 else []):
                        st[tag + ' triples'] += 1; st[tag + ' F empty'] += Fempty; st[tag + ' both petals reach F'] += both
        for a, b in sorted(st.items()): print("%-34s %d" % (a, b))
        sys.exit()
    R_, S = int(sys.argv[4]), int(sys.argv[5]); res = []; r = 0
    def best_config(P):
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
    while r < R_:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P); res.append((b, P)); print("restart %d: score %.5f v=%d i=%d val=%.5f deg=%.3f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('caseB_four_%s.pkl' % hyp, 'wb'))
    b, P = res[0]; o = Octa(P, b[1]); i = b[2]; j, jj = (i + 1) % 4, (i + 2) % 4
    print("BEST", hyp, b); print("kv=%.3f kw=%.3f ku=%s nu=%s om=%s kappa_front=%.3f nu_j=%.3f kappa_back=%.3f nu_m=%.3f" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3), np.round(o.omega, 3), o.ku[j] + o.ku[jj], o.nu[j], o.ku[i] + o.ku[(i - 1) % 4] + o.kw, o.nu[(i - 1) % 4]))
