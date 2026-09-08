"""LP over the 24 face angles of an octahedron-type polytope: face sums = pi, positivity, cone inequalities at each vertex
(each face angle <= sum of the other three), curvature bounds, and the slit rule / (H) as linear constraints.
Maximise a linear objective numerically. A nonpositive floating optimum is only a
candidate bound: an exact dual certificate must be extracted and checked before
claiming an implication from these linear facts. This script does not do that."""
import numpy as np, sys
from scipy.optimize import linprog
# variables: nu[t], aV[t], aVp[t], om[t], bW[t], bWp[t] for t=0..3  -> 24 vars
idx = {}
for nm in ('nu', 'aV', 'aVp', 'om', 'bW', 'bWp'):
    for t in range(4): idx[(nm, t)] = len(idx)
N = len(idx)
def vec(terms):
    v = np.zeros(N)
    for coef, key in terms: v[idx[key]] += coef
    return v
def vertex_angles(x):     # list of (coef,key) for the 4 face angles at vertex x
    if x == 'v': return [(1, ('nu', t)) for t in range(4)]
    if x == 'w': return [(1, ('om', t)) for t in range(4)]
    t = x                 # equator vertex u_t
    return [(1, ('aV', t)), (1, ('aVp', (t - 1) % 4)), (1, ('bW', t)), (1, ('bWp', (t - 1) % 4))]
def curvature(x): return [(-c, k) for c, k in vertex_angles(x)]   # kappa_x = 2pi - sum  ->  represented as (2pi + vec)
def solve(objective, hyps, i=0, extra=()):
    """maximise objective (list of (coef,key)) plus constant; hyps subset of {'R','H'}; returns max value."""
    j, jj, m = (i + 1) % 4, (i + 2) % 4, (i - 1) % 4; k = m
    A_eq, b_eq = [], []
    for t in range(4):
        A_eq.append(vec([(1, ('nu', t)), (1, ('aV', t)), (1, ('aVp', t))])); b_eq.append(np.pi)
        A_eq.append(vec([(1, ('om', t)), (1, ('bW', t)), (1, ('bWp', t))])); b_eq.append(np.pi)
    A_ub, b_ub = [], []
    verts = ['v', 'w', 0, 1, 2, 3]
    for x in verts:
        ang = vertex_angles(x)
        A_ub.append(vec(ang)); b_ub.append(2 * np.pi)                     # kappa >= 0
        for c, key in ang:                                                 # cone inequality: key <= sum of others
            A_ub.append(vec([(2, key)] + [(-1, kk) for _, kk in ang])); b_ub.append(0.0)
    def kappa_le(x, y):     # kappa_x <= kappa_y  <=>  sum_y <= sum_x
        A_ub.append(vec(vertex_angles(y)) - vec(vertex_angles(x))); b_ub.append(0.0)
    if 'R' in hyps:
        for t in range(4):
            if t != k: kappa_le(t, k)
    if 'H' in hyps:
        for x in verts:
            if x != 'v': kappa_le(x, 'v')
    for row, rhs in extra: A_ub.append(vec(row)); b_ub.append(rhs)
    c = -vec(objective)
    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub), A_eq=np.array(A_eq), b_eq=np.array(b_eq), bounds=[(0, np.pi)] * N, method='highs')
    return res
if __name__ == '__main__':
    i = 0; j, jj, m = 1, 2, 3; k = m
    SW = [(1, ('bWp', i)), (1, ('bW', j)), (1, ('bWp', j)), (1, ('bW', jj))]
    f_minus_SW = [(1, ('aVp', jj))] + [(-c, kk) for c, kk in SW]
    bui_minus_SW = [(1, ('aV', i))] + [(-c, kk) for c, kk in SW]
    for hyps in ((), ('R',), ('R', 'H'), ('H',)):
        r1 = solve(f_minus_SW, hyps); r2 = solve(bui_minus_SW, hyps)
        print("hyps=%-10s max(f - SW) = %.4f   max(angle_{u_i}V_i - SW) = %.4f" % (hyps, -r1.fun, -r2.fun))
    # the tight solution for R
    r = solve(f_minus_SW, ('R',)); x = r.x
    print("R-optimum angles:"); 
    for nm in ('nu', 'aV', 'aVp', 'om', 'bW', 'bWp'): print("  %-4s" % nm, np.round([x[idx[(nm, t)]] for t in range(4)], 3))
    print("  kappa:", {str(v): round(2*np.pi - sum(x[idx[kk]] for _, kk in vertex_angles(v)), 3) for v in ['v', 'w', 0, 1, 2, 3]})
