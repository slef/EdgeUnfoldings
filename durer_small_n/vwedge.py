"""Baseline check of the vertical-wedge step (HANDOFF.md) on observed opposite-petal overlaps.

For every random octahedron, apex v, slit k: find overlaps of the two opposite-petal pairs
V_i–V_{i+2} (i = k: W side through W_{k+1}; i = k+1: W side through W_{k+2}).  For each overlap
classify where the intersection region lies (vertical wedge of the petal between them on the W side,
vertical wedge of the petal on the gap side, other), and test the claimed necessary conditions
    κ_{u_{i+1}} < ν_{i+1},  κ_{u_{i+2}} < ν_{i+1}     (W-side meeting)
plus the non-crossing conditions κ_{u_{i+1}} + ∠V_i(u_{i+1}) ≤ π,  κ_{u_{i+2}} + ∠V_{i+2}(u_{i+2}) ≤ π.
usage: vwedge.py seed N
"""
import numpy as np, sys, collections
from octa import *

def side(A, B, p):  # >0 left of A→B
    return (B[0]-A[0])*(p[1]-A[1]) - (B[1]-A[1])*(p[0]-A[0])

def in_vertical_wedge(T, p):
    """T = CCW triangle [apex, x, y]; p in the wedge at apex opposite to the triangle."""
    apex, x, y = T
    return side(apex, x, p) < 0 and side(apex, y, p) > 0   # opposite sides from the triangle (which is left of apex→x, right of apex→y)

def in_wedge(T, p):
    apex, x, y = T
    return side(apex, x, p) > 0 and side(apex, y, p) < 0

if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[1])); N = int(sys.argv[2])
    st = collections.Counter(); rows = []
    for P, faces, adj in random_octahedra(rng, N):
        for o in all_apexes(P, faces, adj):
            hyp = o.kv >= o.ku.max()
            for k in range(4):
                ov = o.overlaps(k, Octa.OPP)
                for nm in ov:
                    i = k if nm == 'V_k-V_k+2' else (k + 1) % 4
                    j = (i + 1) % 4; jj = (i + 2) % 4; m = (i - 1) % 4   # between-petal on W side: V_j; on gap side: V_m
                    net = o.Z(k)
                    Vi, Vjj, Vj, Vm = net[('V', i)], net[('V', jj)], net[('V', j)], net[('V', m)]
                    X = o.intersection(k, nm)
                    c = X.mean(0)
                    vw_W = all(in_vertical_wedge(Vj, q) for q in X)
                    vw_W_any = any(in_vertical_wedge(Vj, q) for q in X)
                    vw_G = all(in_vertical_wedge(Vm, q) for q in X)
                    vw_G_any = any(in_vertical_wedge(Vm, q) for q in X)
                    arc = o.arc_of(k, c)
                    # W side means: the between-petal V_j separates; simplest classifier: centroid polar angle
                    # lies in arcs of W_i, W_j, W_jj (the W side) vs W_m or gap.
                    a = o.polar(c); th = net['theta']
                    # angular position of c relative to the arc of W_j (the W-side fan face between the petals)
                    Wside = th[j] - 1.0 < a < th[j] + o.omega[j] + 1.0 or arc in (('W', i), ('W', j), ('W', jj))
                    cls = ('VW(W)' if vw_W else 'partVW(W)' if vw_W_any else '') + ('VW(G)' if vw_G else 'partVW(G)' if vw_G_any else '')
                    st['overlaps'] += 1; st['hyp holds AND overlap'] += hyp
                    st['class ' + (cls or 'neither') + ' arc=' + str(arc if arc == 'gap' else 'W_' + str((arc[1] - k) % 4) + '+k')] += 1
                    if vw_W_any:
                        st['W-side: kappa_{u_j} < nu_j'] += (o.ku[j] < o.nu[j])
                        st['W-side: kappa_{u_jj} < nu_j'] += (o.ku[jj] < o.nu[j])
                        st['W-side: both claimed ineqs hold'] += (o.ku[j] < o.nu[j] and o.ku[jj] < o.nu[j])
                        st['W-side: noncross V_i at u_j (k+a<=pi)'] += (o.ku[j] + o.aVp[i] <= np.pi)
                        st['W-side: noncross V_jj at u_jj'] += (o.ku[jj] + o.aV[jj] <= np.pi)
                        st['W-side: nu_j <= pi/2'] += (o.nu[j] <= np.pi / 2)
                        if o.nu[j] <= np.pi/2:
                            st['W-side, nu_j<=pi/2: base V_i longer than v-edge |v u_j|'] += (o.l[i] > o.s[j])
                            st['W-side, nu_j<=pi/2: base V_jj longer than |v u_jj|'] += (o.l[jj] > o.s[jj])
                        st['W-side total'] += 1
                        rows.append((o.kv, o.kw, o.ku[i], o.ku[j], o.ku[jj], o.ku[m], o.nu[j], o.nu[i], o.nu[jj]))
                    if vw_G_any:
                        st['G-side total'] += 1
                        st['G-side: kappa_{u_m} < nu_m'] += (o.ku[m] < o.nu[m])
                        st['G-side: kappa_{u_i} < nu_m'] += (o.ku[i] < o.nu[m])
                        st['G-side: kappa_{u_m}+kappa_w < nu_m'] += (o.ku[m] + o.kw < o.nu[m])
                        st['G-side: kappa_{u_i}+kappa_w < nu_m'] += (o.ku[i] + o.kw < o.nu[m])
                    if not (vw_W_any or vw_G_any):
                        st['neither-side examples'] += 1
                        if st['neither-side examples'] <= 3:
                            print("neither example: k=%d pair=%s arc=%s kv=%.3f kw=%.3f ku=%s nu=%s aVp_i=%.3f aV_jj=%.3f" % (
                                k, nm, arc, o.kv, o.kw, np.round(o.ku, 3), np.round(o.nu, 3), o.aVp[i], o.aV[jj]))
                            np.save('vwedge_neither_%d.npy' % st['neither-side examples'], P)
    print("nets:", 24 * N)
    for key, c in sorted(st.items()): print("  %-58s %d" % (key, c))
    if rows:
        R = np.array(rows)
        print("W-side rows: max kv %.3f, max (kv - max ku) %.3f" % (R[:, 0].max(), (R[:, 0] - R[:, 2:6].max(1)).max()))
