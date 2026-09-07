"""Candidate separating lines for opposite petals V_i, V_jj (between petal V_j), above-base case.
For each triple (i, j=i+1, jj=i+2) in the v-fan-consistent frame (net with W_i W_j W_jj contiguous), let
  L1' = line(u_j, v_i), L2' = line(u_jj, v_jj), p* their intersection (if kappa_j + kappa_jj < nu_j).
Candidates:
  S1: line through p* with direction d1+d2 (bisector of the wedge D)
  S2: line through v_j with direction d1+d2
  S3: line through v_j and p*
Score for a candidate = max penetration of V_i into the V_jj side or V_jj into the V_i side (signed; <0 = separated
with margin), maximised adversarially under hypothesis HYP.  Also usable for statistics (mode 'stat').
usage: adv_sep.py S1|S2|S3 HYP seed restarts steps      or   adv_sep.py stat HYP seed N
"""
import numpy as np, sys, pickle, collections
from octa import *
from adv_opp import violation, DELTA

def triple_frame(o, i):
    """positions of V_i, V_j, V_jj in a net where W_i W_j W_jj are contiguous: use Z_k with k = i-1."""
    k = (i - 1) % 4; net = o.Z(k); j, jj = (i + 1) % 4, (i + 2) % 4
    return net[('V', i)], net[('V', j)], net[('V', jj)]

def unit(v): return v / np.linalg.norm(v)

def geometry(o, i):
    """inner lines with outward sides determined from the triangles themselves.
    Returns dict with uj, ujj, vj, vi, vjj, d1, d2 (unit directions of the cut edges), n1, n2 (unit normals pointing
    to the outward side, i.e. into V_i resp. V_jj), pstar (or None)."""
    Vi, Vj, Vjj = triple_frame(o, i)
    uj, ujj, vj = Vj[2], Vj[1], Vj[0]; vi = Vi[0]; vjj = Vjj[0]
    ui = Vi[2] if np.allclose(Vi[1], uj) else Vi[1]          # third vertex of V_i (not v_i, not u_j)
    ujj1 = Vjj[2] if np.allclose(Vjj[1], ujj) else Vjj[1]
    d1 = unit(vi - uj); d2 = unit(vjj - ujj)
    n1 = np.array([-d1[1], d1[0]]); n1 *= np.sign(np.dot(ui - uj, n1))
    n2 = np.array([-d2[1], d2[0]]); n2 *= np.sign(np.dot(ujj1 - ujj, n2))
    M = np.array([d1, -d2]).T
    pstar = None
    if abs(np.linalg.det(M)) > 1e-12:
        t = np.linalg.solve(M, ujj - uj)
        if t[0] > 0 and t[1] > 0: pstar = uj + t[0] * d1     # cut-edge rays converge (above-base case)
    return dict(Vi=Vi, Vj=Vj, Vjj=Vjj, uj=uj, ujj=ujj, vj=vj, vi=vi, vjj=vjj, ui=ui, ujj1=ujj1, d1=d1, d2=d2, n1=n1, n2=n2, pstar=pstar)

def candidate_line(o, i, which):
    g = geometry(o, i)
    if g['pstar'] is None: return None
    bis = unit(g['d1'] + g['d2'])
    # orient the line so that V_i's side is the +normal side: normal = n1-ish component
    if which == 'S1': P0, d = g['pstar'], bis
    elif which == 'S2': P0, d = g['vj'], bis
    else:
        w = g['pstar'] - g['vj']; P0, d = g['vj'], (unit(w) if np.linalg.norm(w) > 1e-12 else bis)
    n = np.array([-d[1], d[0]])
    if np.dot(n, g['n1']) > 0: n = -n            # V_i's side of the bisector is toward ray r1, i.e. the -n1 side
    return P0, n

def halfplane_poly(P0, n, big):
    """CCW quadrilateral covering the half-plane {x : (x-P0).n >= 0}."""
    d = np.array([n[1], -n[0]])                 # n is the left normal of d
    a = P0 - big * d; b = P0 + big * d
    return np.array([a, b, b + big * n, a + big * n])

def clipped_parts(o, i):
    """V_i ∩ D and V_jj ∩ D, where D = (outward of L1') ∩ (outward of L2')."""
    g = geometry(o, i); big = 10 * o.scale
    Xi = clip_convex(g['Vi'], halfplane_poly(g['ujj'], g['n2'], big))
    Xjj = clip_convex(g['Vjj'], halfplane_poly(g['uj'], g['n1'], big))
    return Xi, Xjj

def penetration(o, i, which):
    """signed: max over vertices of V_i∩D of (distance into the V_jj side) and vice versa; negative = separated."""
    L = candidate_line(o, i, which)
    if L is None: return None
    P0, n = L
    Xi, Xjj = clipped_parts(o, i)
    if len(Xi) < 3 or len(Xjj) < 3: return -1.0   # one petal does not even reach D
    si = (Xi - P0) @ n; sjj = (Xjj - P0) @ n
    return max((-si).max(), sjj.max()) / o.scale

def best_config(P, which, hyp):
    st = octa_structure(P)
    if st is None: return None
    best = None
    for o in all_apexes(P, st[0], st[1]):
        deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, DELTA - min(o.kappa.values()))
        for i in range(4):
            pen = penetration(o, i, which)
            if pen is None: continue
            vio = violation(o, i, hyp)
            sc = pen - 10 * vio - 10 * deg
            if best is None or sc > best[0]: best = (sc, o.v, i, pen, vio, deg)
    return best

if __name__ == '__main__':
    which, hyp = sys.argv[1], sys.argv[2]; rng = np.random.default_rng(int(sys.argv[3]))
    if which == 'stat':
        N = int(sys.argv[4]); st = collections.Counter()
        for P, faces, adj in random_octahedra(rng, N):
            for o in all_apexes(P, faces, adj):
                for i in range(4):
                    vio = violation(o, i, hyp)
                    if vio > 0: continue
                    for c in ('S1', 'S2', 'S3'):
                        pen = penetration(o, i, c)
                        if pen is None: st[c + ' n/a'] += 1; continue
                        st[c + ' cases'] += 1; st[c + ' FAILS'] += (pen > 1e-9)
        for a, b in sorted(st.items()): print("%-12s %d" % (a, b))
        sys.exit()
    R, S = int(sys.argv[4]), int(sys.argv[5]); results = []; r = 0
    while r < R:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or best_config(P0, which, hyp) is None: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P, which, hyp))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P, which, hyp); results.append((b, P))
        print("restart %d: score %.5f v=%d i=%d pen=%.5f viol=%.4f deg=%.4f" % ((r,) + b), flush=True)
    results.sort(key=lambda t: -t[0][0])
    pickle.dump(results, open('adv_sep_%s_%s.pkl' % (which, hyp), 'wb'))
    b, P = results[0]; o = Octa(P, b[1]); i = b[2]; j, jj = (i + 1) % 4, (i + 2) % 4
    print("BEST", which, hyp, b)
    print("kv=%.3f kw=%.3f ku=%s nu=%s" % (o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3)))
    print("i=%d nu_i=%.3f nu_j=%.3f nu_jj=%.3f k_j=%.3f k_jj=%.3f aV_j=%.3f aVp_j=%.3f aVp_i=%.3f aV_jj=%.3f l_i/s_j=%.3f l_jj/s_jj=%.3f" % (
        i, o.nu[i], o.nu[j], o.nu[jj], o.ku[j], o.ku[jj], o.aV[j], o.aVp[j], o.aVp[i], o.aV[jj], o.l[i] / o.s[j], o.l[jj] / o.s[jj]))
