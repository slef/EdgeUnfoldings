"""Collect all opposite-petal overlaps, classify in detail, save cases and draw them.
usage: oppcases.py seed N [outdir]
Classification of the intersection region X of V_i and V_{i+2} in Z_k (i = k or k+1):
  W side between-petal V_j (j = i+1), gap side between-petal V_m (m = i-1).
  For apex a of a petal T = [a, x, y]: region of a point p ∈ {tri, vert, sideX, sideY} by the two lines a x, a y.
  Also: polar arc of X's centroid; whether X is on w's side of the base of V_j / V_m; crossing flags.
"""
import numpy as np, sys, os, collections, pickle
from octa import *
from vwedge import side, in_vertical_wedge, in_wedge
from draw import draw_net

def region(T, p):
    a, x, y = T
    sx = side(a, x, p) > 0; sy = side(a, y, p) < 0     # inside the triangle wedge: left of a→x and right of a→y
    return {(True, True): 'tri', (False, False): 'vert', (False, True): 'side_x', (True, False): 'side_y'}[(sx, sy)]

def describe(o, k, nm):
    i = k if nm == 'V_k-V_k+2' else (k + 1) % 4
    j, jj, m = (i + 1) % 4, (i + 2) % 4, (i - 1) % 4
    net = o.Z(k); Vi, Vjj, Vj, Vm, Wj, Wm = net[('V', i)], net[('V', jj)], net[('V', j)], net[('V', m)], net[('W', j)], net[('W', m)]
    X = o.intersection(k, nm); c = X.mean(0)
    d = dict(k=k, pair=nm, i=(i - k) % 4, area=poly_area(X) / o.scale**2,
             regW=collections.Counter(region(Vj, q) for q in X), regG=collections.Counter(region(Vm, q) for q in X),
             arc=o.arc_of(k, c), polar=o.polar(c), theta=net['theta'],
             # base of V_j is u_j u_jj (= Vj[2], Vj[1]); w side is left of Vj[1]→Vj[2]
             wside_of_baseW=side(Vj[1], Vj[2], c) > 0, wside_of_baseG=side(Vm[1], Vm[2], c) > 0,
             cross_i_at_uj=o.ku[j] + o.aVp[i] > np.pi, cross_jj_at_ujj=o.ku[jj] + o.aV[jj] > np.pi,
             kv=o.kv, kw=o.kw, ku=o.ku, nu=o.nu, omega=o.omega, F=o.F, B=o.B, e=o.e, f=o.f,
             r=o.r, s=o.s, l=o.l, aV=o.aV, aVp=o.aVp, bW=o.bW, bWp=o.bWp)
    return d

if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[1])); N = int(sys.argv[2])
    out = sys.argv[3] if len(sys.argv) > 3 else 'cases_opp'
    os.makedirs(out, exist_ok=True)
    cases = []
    for P, faces, adj in random_octahedra(rng, N):
        for o in all_apexes(P, faces, adj):
            for k in range(4):
                for nm in o.overlaps(k, Octa.OPP):
                    d = describe(o, k, nm); d['P'] = P; d['v'] = o.v
                    cases.append(d)
    pickle.dump(cases, open(os.path.join(out, 'cases.pkl'), 'wb'))
    print(len(cases), "opposite-petal overlaps")
    for n, d in enumerate(cases):
        vw = 'VW' if d['regW'] == collections.Counter({'vert': sum(d['regW'].values())}) else 'other'
        print("#%d k=%d %s i=%d area=%.2e  regW=%s regG=%s arc=%s wsideW=%s wsideG=%s crossI=%s crossJJ=%s | kv=%.3f kw=%.3f ku=%s nu=%s" % (
            n, d['k'], d['pair'], d['i'], d['area'], dict(d['regW']), dict(d['regG']), d['arc'], d['wside_of_baseW'], d['wside_of_baseG'],
            d['cross_i_at_uj'], d['cross_jj_at_ujj'], d['kv'], d['kw'], np.round(d['ku'], 3), np.round(d['nu'], 3)))
        if vw == 'other':
            o = Octa(d['P'], d['v'])
            draw_net(o, d['k'], os.path.join(out, 'case%02d.png' % n), highlight=[d['pair']])
            X = o.intersection(d['k'], d['pair']); c = X.mean(0); r = max(np.ptp(X, 0).max() * 3, o.scale * 0.02)
            draw_net(o, d['k'], os.path.join(out, 'case%02d_zoom.png' % n), highlight=[d['pair']], zoom=(c[0], c[1], r), labels=True)
