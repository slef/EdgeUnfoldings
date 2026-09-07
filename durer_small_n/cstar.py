"""Numerical check of the c*-rotation proof strategy for the above-base case of the Triple Lemma.

v-fan frame: V_j fixed as in the net; V_i^fan = Rot(u_j, -kappa_j) V_i ; V_jj^fan = Rot(u_jj, +kappa_jj) V_jj
(so that the three petals are glued flat around v).  R = Rot(u_jj, kappa_jj) o Rot(u_j, kappa_j) = Rot(c*, kappa).
Checks:
  C1: R is a rotation by kappa about c* with base angles kappa_j/2, kappa_jj/2 on w's side of the base.
  C2: V_i^fan and V_jj^fan are disjoint (touch only at v).
  C3: net meeting  <=>  R(V_i^fan) ∩ V_jj^fan  (sanity)
  (i') V_i^fan ∩ {above base} ⊂ closed ccw side of M = line(c*, v)  [i.e. u_j's side]
  (ii') V_jj^fan ∩ {above base} ⊂ closed cw side of M
  both fail never under H3;  when one fails, angular excess eps beyond M (seen from c*) versus kappa.
usage: cstar.py seed N
"""
import numpy as np, sys, collections
from octa import *
from adv_opp import violation, DELTA

def rotate_about(T, c, th): return (T - c) @ rot(th).T + c

def signed_side(P0, d, X):  # >0 left of directed line (P0, d)
    return d[0] * (X[:, 1] - P0[1]) - d[1] * (X[:, 0] - P0[0])

def analyse(o, i):
    """returns dict of checks for triple i (needs kappa_j+kappa_jj < nu_j)."""
    k = (i - 1) % 4; net = o.Z(k); j, jj = (i + 1) % 4, (i + 2) % 4
    Vi, Vj, Vjj = net[('V', i)], net[('V', j)], net[('V', jj)]
    uj, ujj, vj = Vj[2], Vj[1], Vj[0]
    kj, kjj = o.ku[j], o.ku[jj]; kap = kj + kjj
    if kap >= o.nu[j]: return None
    # rotation sense: sgn such that Rot(u_j, -sgn*kj) sends v_i back onto v_j (undoing the gap at u_j)
    base = ujj - uj
    cand = [sg for sg in (1, -1) if np.linalg.norm(rotate_about(Vi[:1], uj, -sg * kj)[0] - vj) < 1e-7 * o.scale]
    if len(cand) != 1: return None
    sgn = cand[0]
    assert np.linalg.norm(rotate_about(Vjj[:1], ujj, sgn * kjj)[0] - vj) < 1e-7 * o.scale, "gap at u_jj has unexpected sense"
    left = sgn > 0
    Vi_fan = rotate_about(Vi, uj, -sgn * kj)
    Vjj_fan = rotate_about(Vjj, ujj, +sgn * kjj)
    res = {}
    res['C2 fan apexes coincide'] = np.linalg.norm(Vi_fan[0] - vj) < 1e-7 * o.scale and np.linalg.norm(Vjj_fan[0] - vj) < 1e-7 * o.scale
    # c*: composition of Rot(uj, sgn*kj) then Rot(ujj, sgn*kjj)
    # find fixed point: R(x) = x
    A = rot(sgn * kap); # R(x) = A(x - uj) + uj  then Rot about ujj: A2((.) - ujj) + ujj
    def R(X): return rotate_about(rotate_about(X, uj, sgn * kj), ujj, sgn * kjj)
    # fixed point solve: R(x) = A x + b  =>  x = (I - A)^{-1} b
    b = R(np.zeros((1, 2)))[0]
    cstar = np.linalg.solve(np.eye(2) - A, b)
    # base angles at uj, ujj
    ang_uj = angle_at(uj, ujj, cstar); ang_ujj = angle_at(ujj, uj, cstar)
    res['C1 base angles kj/2,kjj/2'] = abs(ang_uj - kj / 2) < 1e-6 and abs(ang_ujj - kjj / 2) < 1e-6
    sv = np.sign(signed_side(uj, base, vj[None])[0])              # sign of v_j's side of the base
    res['C1 c* on w side'] = signed_side(uj, base, cstar[None])[0] * sv < 0
    # C3 sanity: net overlap of Vi,Vjj  vs  R(Vi_fan) ∩ Vjj_fan
    net_ov = sat_pen(Vi, Vjj) > o.eps
    fan_ov = sat_pen(R(Vi_fan), Vjj_fan) > o.eps
    res['C3 consistent'] = (net_ov == fan_ov)
    # M = line(c*, v).  su = sign of u_j's side of M.  R must move points from u_jj's side to u_j's side.
    d = vj - cstar
    su = np.sign(signed_side(cstar, d, uj[None])[0])
    res['R(v) on u_j side of M'] = signed_side(cstar, d, R(vj[None]))[0] * su > 0
    def part_above(T):
        big = 10 * o.scale; dd = base / np.linalg.norm(base); n = sv * np.array([-dd[1], dd[0]])
        hp = np.array([uj - big * dd, uj + big * dd, uj + big * dd + big * n, uj - big * dd + big * n])
        if sv < 0: hp = hp[::-1]
        return clip_convex(T, hp)
    Xi = part_above(Vi_fan); Xjj = part_above(Vjj_fan)
    tol = 1e-9 * o.scale
    si = su * signed_side(cstar, d, Xi) if len(Xi) else np.array([0.0])      # >0 : u_j's side
    sjj = su * signed_side(cstar, d, Xjj) if len(Xjj) else np.array([0.0])
    res["(i') holds"] = bool((si >= -tol).all()); res["(ii') holds"] = bool((sjj <= tol).all())
    # angular excess beyond M seen from c*: for V_jj toward u_j's side, for V_i toward u_jj's side
    def ang(X): return np.arctan2(*(X - cstar)[:, ::-1].T)
    mu = np.arctan2(d[1], d[0]); s_ang = su * np.sign(signed_side(cstar, d, (cstar + rot(1e-3) @ d)[None])[0])  # sense giving + toward u_j side
    ex_jj = (s_ang * (ang(Xjj) - mu) + np.pi) % (2 * np.pi) - np.pi if len(Xjj) else np.array([0.0])
    ex_i = (-s_ang * (ang(Xi) - mu) + np.pi) % (2 * np.pi) - np.pi if len(Xi) else np.array([0.0])
    res['eps_jj'] = float(ex_jj.max()); res['eps_i'] = float(ex_i.max()); res['kappa'] = kap
    res['nu_i+mu_j>pi'] = o.nu[i] + angle_at(vj, uj, cstar) > np.pi
    res['nu_jj+mu_jj>pi'] = o.nu[jj] + angle_at(vj, ujj, cstar) > np.pi
    return res

if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[1])); N = int(sys.argv[2]); st = collections.Counter(); worst = {}
    for P, faces, adj in random_octahedra(rng, N):
        for o in all_apexes(P, faces, adj):
            deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
            for i in range(4):
                r = analyse(o, i)
                if r is None: continue
                st['caseA triples'] += 1
                for key in ('C2 fan apexes coincide', 'C1 base angles kj/2,kjj/2', 'C1 c* on w side', 'C3 consistent', 'R(v) on u_j side of M'):
                    st[key] += r[key]
                for H in ('H1', 'H2', 'H3'):
                    if violation(o, i, H) > 0: continue
                    tag = H + (' nondeg' if deg == 0 else ' deg')
                    st[tag + ' triples'] += 1
                    fi, fjj = not r["(i') holds"], not r["(ii') holds"]
                    st[tag + " (i') fails"] += fi; st[tag + " (ii') fails"] += fjj; st[tag + ' both fail'] += (fi and fjj)
                    if fi or fjj:
                        ex = max(r['eps_i'] if fi else -9, r['eps_jj'] if fjj else -9)
                        st[tag + ' one fails & eps>=kappa'] += (ex >= r['kappa'])
                        worst[tag] = max(worst.get(tag, -9), ex - r['kappa'])
    for a, b in sorted(st.items()): print("%-36s %d" % (a, b))
    for a, b in sorted(worst.items()): print("worst (eps - kappa) %-16s %.4f" % (a, b))
