"""Additional SVG figures for the status page (one per case).  Merges into notes/status_figs.json."""
import numpy as np, json, pickle, itertools
from octa import *
from cstar import rotate_about
from svg_figs import svg_net, triple_extras
from unfold2 import Polytope as PolyP, unfold as unfold2, sat_pen as sat2

figs = json.load(open('notes/status_figs.json'))

# ---------------------------------------------------------------- generic net renderer for any small polytope
def svg_poly(p, cut, W=520, H=380, pad=22, labels=None, hl=(), title_face=None, key=None):
    if key: MODELS[key] = mk_model(p.P, p.faces, cut, VN)
    hinge_index = {(a, b): ei for ei, (f, g, a, b) in enumerate(p.E)}
    cut = {tuple(sorted(e)) for e in cut}
    tree = [hinge_index[q] for q in p.edges if q not in cut]
    assert len(tree) == len(p.faces) - 1, (len(tree), len(p.faces))
    pos = unfold2(p.faces, p.L, p.E, tree)
    pts = np.vstack([np.array([pos[f][v] for v in p.faces[f]]) for f in range(len(p.faces))])
    lo, hi = pts.min(0), pts.max(0)
    sc = min((W - 2 * pad) / (hi[0] - lo[0] + 1e-12), (H - 2 * pad) / (hi[1] - lo[1] + 1e-12)); cx, cy = (lo + hi) / 2
    P = lambda q: (W / 2 + (q[0] - cx) * sc, H / 2 - (q[1] - cy) * sc)
    fmt = lambda q: "%.1f,%.1f" % P(q)
    out = ['<svg viewBox="0 0 %d %d" xmlns="http://www.w3.org/2000/svg" class="net">' % (W, H)]
    # overlap check
    bad = set()
    for f, g in itertools.combinations(range(len(p.faces)), 2):
        sh = set(p.faces[f]) & set(p.faces[g])
        if any(np.linalg.norm(pos[f][x] - pos[g][x]) < p.eps for x in sh): continue
        if sat2(np.array([pos[f][x] for x in p.faces[f]]), np.array([pos[g][x] for x in p.faces[g]])) > p.eps: bad |= {f, g}
    for f in range(len(p.faces)):
        T = [pos[f][v] for v in p.faces[f]]
        cls = 'petal' if len(p.faces[f]) == 3 else 'fan'
        if f in hl: cls += ' hl'
        out.append('<polygon class="%s" points="%s"/>' % (cls, " ".join(fmt(q) for q in T)))
    if labels:
        for f in range(len(p.faces)):
            c = np.mean([pos[f][v] for v in p.faces[f]], axis=0); x, y = P(c)
            out.append('<text class="face" x="%.1f" y="%.1f" text-anchor="middle" dominant-baseline="middle">%s</text>' % (x, y, labels(f)))
    # label vertices once per net copy
    seen = []
    for f in range(len(p.faces)):
        for v in p.faces[f]:
            q = pos[f][v]
            if any(np.linalg.norm(q - s) < p.eps for s, _ in seen): continue
            seen.append((q, v)); x, y = P(q)
            out.append('<text class="lbl vtx" x="%.1f" y="%.1f">%s</text>' % (x + 3, y - 3, VN.get(v, str(v))))
    out.append('</svg>')
    return "\n".join(out), bool(bad)

MODELS = {}
def mk_model(P, faces, cut, names):
    return dict(P=[[round(float(x), 5) for x in q] for q in P], faces=[list(map(int, f)) for f in faces],
                cut=[list(map(int, sorted(e))) for e in cut], names={int(k): v for k, v in names.items()})
def octa_model(o, k):
    st = octa_structure(o.P); cut = [(o.v, u) for u in o.u] + [(o.w, o.u[k])]
    names = {o.v: 'v', o.w: 'w'}; names.update({o.u[i]: 'u' + '₀₁₂₃'[i] for i in range(4)})
    return mk_model(o.P, st[0], cut, names)
VN = {}
def with_names(names):
    global VN; VN = names

def apex_star(p, v): return [e for e in p.edges if v in e]

# ---------------------------------------------------------------- sample polytopes for each type
rng = np.random.default_rng(7)
def reg(n, r, z=0.0, rot=0.0): return [(r * np.cos(rot + 2 * np.pi * i / n), r * np.sin(rot + 2 * np.pi * i / n), z) for i in range(n)]

# tetrahedron
P = np.array([(0, 0, 1.1), (1, 0, 0), (-0.4, 0.9, 0), (-0.5, -0.8, -0.1)], float); p = PolyP(P)
with_names({0: 'v'}); figs['n4'], _ = svg_poly(p, apex_star(p, 0), key='n4', labels=lambda f: '')
# square pyramid and triangular bipyramid
P = np.array([(0, 0, 1.0)] + reg(4, 1.0, 0, 0.3), float); P[1:, 0] *= 1.3; p = PolyP(P)
with_names({0: 'v'}); figs['n5_pyr'], _ = svg_poly(p, apex_star(p, 0), key='n5_pyr', labels=lambda f: '')
P = np.array([(0, 0, 1.2), (0, 0, -0.9)] + reg(3, 1.0, 0, 0.2), float); p = PolyP(P)
deg = {v: sum(v in e for e in p.edges) for v in range(5)}; v4 = [v for v in range(5) if deg[v] == 4][0]
with_names({v4: 'v'}); figs['n5_bipyr'], _ = svg_poly(p, apex_star(p, v4), key='n5_bipyr', labels=lambda f: '')
# pentagonal pyramid
P = np.array([(0.1, 0, 1.0)] + reg(5, 1.0, 0, 0.1), float); P[1:, 1] *= 0.8; p = PolyP(P)
with_names({0: 'v'}); figs['t_pyr5'], _ = svg_poly(p, apex_star(p, 0), key='t_pyr5', labels=lambda f: '')
figs['lemmaA'] = figs['t_pyr5']
# hexagonal pyramid (n=7 illustration)
P = np.array([(0.05, 0.1, 1.0)] + reg(6, 1.0, 0, 0.05), float); P[1:, 0] *= 1.2; p = PolyP(P)
with_names({0: 'v'}); figs['n7'], _ = svg_poly(p, apex_star(p, 0), key='n7', labels=lambda f: '')
# simplicial 5,5,4,4,3,3 : tetrahedron 0,1,2,3 + bumps 4 (over face 0,1,3) and 5 (over face 0,2,3)
T = np.array([(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)], float)
b4 = (T[0] + T[1] + T[3]) / 3; n4 = np.cross(T[1] - T[0], T[3] - T[0]); n4 /= np.linalg.norm(n4)
if np.dot(n4, b4 - T.mean(0)) < 0: n4 = -n4
b5 = (T[0] + T[2] + T[3]) / 3; n5 = np.cross(T[2] - T[0], T[3] - T[0]); n5 /= np.linalg.norm(n5)
if np.dot(n5, b5 - T.mean(0)) < 0: n5 = -n5
P = np.vstack([T, b4 + 0.45 * n4, b5 + 0.45 * n5]); p = PolyP(P)
deg = {v: sum(v in e for e in p.edges) for v in range(6)}; assert sorted(deg.values()) == [3, 3, 4, 4, 5, 5], deg
v5 = [v for v in range(6) if deg[v] == 5][0]
with_names({v5: 'v'}); figs['t_simp55'], _ = svg_poly(p, apex_star(p, v5), key='t_simp55', labels=lambda f: '')
# type 5,4,4,3,3,3: apex over a base made of a planar quad + a lower triangle
B = [(1, 0, 0), (0.3, 1, 0), (-0.8, 0.6, 0), (-0.8, -0.6, 0), (0.3, -1, 0)]   # b0..b4 ; quad b1 b2 b3 b4 planar, b0 lowered
P = np.array([(0, 0.1, 1.2)] + B, float); P[1, 2] = 0.15; P[1, 0] = 1.3; p = PolyP(P)
fs = sorted(len(f) for f in p.faces); deg = {v: sum(v in e for e in p.edges) for v in range(6)}
assert fs == [3, 3, 3, 3, 3, 3, 4] and sorted(deg.values()) == [3, 3, 3, 4, 4, 5], (fs, deg)
with_names({0: 'v'}); figs['t_54'], _ = svg_poly(p, apex_star(p, 0), key='t_54', labels=lambda f: '')
# prism: strip of quads, triangles on the middle quad
A, Bq, C = np.array([(0, 0, 0), (1.3, 0, 0), (0.4, 1.0, 0)], float); up = np.array([0.15, 0.1, 1.1])
P = np.vstack([A, Bq, C, A + up, Bq + up, C + up]); p = PolyP(P)
with_names({0: 'A', 1: 'B', 2: 'C', 3: "A′", 4: "B′", 5: "C′"})
figs['t_prism'], bad = svg_poly(p, [(0, 3), (0, 1), (0, 2), (3, 4), (3, 5)], key='t_prism', labels=lambda f: ''); assert not bad
# prism with one diagonal (nonsimp6 construction) : cut tree containing the star of a degree-4 vertex, chosen simple
def prism_diag():
    A_, B_, C_ = np.array([(0, 0, 0), (1.3, 0.1, 0), (0.5, 1.1, 0)], float); Cp = np.array([0.6, 0.9, 1.2])
    Bp = C_ + 0.9 * (B_ - C_) + 0.95 * (Cp - C_); Ap = C_ + 1.0 * (A_ - C_) + 1.05 * (Cp - C_)
    return np.array([A_, B_, C_, Ap, Bp, Cp])
P = prism_diag(); p = PolyP(P); fs = sorted(len(f) for f in p.faces); assert fs == [3, 3, 3, 3, 4, 4], fs
deg = {v: sum(v in e for e in p.edges) for v in range(6)}; v4 = [v for v in range(6) if deg[v] == 4][0]
star = set(tuple(sorted(e)) for e in apex_star(p, v4))
pen = p.penetrations(); good = [t for t, pe in zip(p.trees(), pen) if pe <= 0 and star <= set(p.cut_set(t))]
with_names({0: 'A', 1: 'B', 2: 'C', 3: "A′", 4: "B′", 5: "C′"})
figs['t_prismd'], bad = svg_poly(p, p.cut_set(good[0]), key='t_prismd', labels=lambda f: ''); assert not bad
# octahedron minus an edge: octahedron with v, u_i, w, u_{i+1} coplanar (quad v u_i w u_{i+1})
def octa_minus():
    # quad = V_0 ∪ W_0 merged: v, u_0, w, u_1 coplanar (y = 0), the other two equator vertices on the y > 0 side
    Q = np.array([(0, 0, 1.0), (0.05, 0, -1.1), (1.0, 0, 0.1), (-1.0, 0, -0.1), (0.35, 0.95, 0.0), (-0.3, 1.0, 0.05)])
    p = PolyP(Q); fs = sorted(len(f) for f in p.faces); assert fs == [3, 3, 3, 3, 3, 3, 4] and len(p.P) == 6, fs
    return Q, p
P, p = octa_minus()
with_names({0: 'v', 1: 'w', 2: 'u₀', 3: 'u₁', 4: 'u₂', 5: 'u₃'})
star = set(tuple(sorted(e)) for e in apex_star(p, 0))
pen = p.penetrations(); good = [t for t, pe in zip(p.trees(), pen) if pe <= 0 and star <= set(p.cut_set(t))]
figs['t_octa_minus'], bad = svg_poly(p, p.cut_set(good[0]), key='t_octa_minus', labels=lambda f: ''); assert not bad

# ---------------------------------------------------------------- octahedron figures
Pn = np.load('notes/figs/net_typical.npy'); o = Octa(Pn, 0); k = int(np.argmax(o.ku))
# far pairs highlighted: outline the six far pairs' faces? Simpler: two nets: opposite petals (V_k, V_k+2) and (V_k+1, V_k-1')
def svg_net_hl(o, k, faces, **kw):
    s = svg_net(o, k, **kw)
    # add outlines for highlighted faces
    net = o.Z(k); pts = np.vstack([T for key, T in net.items() if isinstance(key, tuple)])
    lo, hi = pts.min(0), pts.max(0); W, H, pad = 520, 420, 22
    sc = min((W - 2 * pad) / (hi[0] - lo[0] + 1e-12), (H - 2 * pad) / (hi[1] - lo[1] + 1e-12)); cx, cy = (lo + hi) / 2
    P = lambda q: "%.1f,%.1f" % (W / 2 + (q[0] - cx) * sc, H / 2 - (q[1] - cy) * sc)
    extra = "".join('<polygon class="outline %s" points="%s %s %s"/>' % (cls, P(T[0]), P(T[1]), P(T[2])) for T, cls in faces)
    return s.replace('</svg>', extra + '</svg>')
net = o.Z(k)
far = [(net[('V', k)], 'o1'), (net[('V', (k + 2) % 4)], 'o1'), (net[('V', (k + 1) % 4)], 'o2'), (net[('V', (k + 3) % 4)], 'o2'),
       (net[('W', (k + 2) % 4)], 'o3'), (net[('W', (k + 3) % 4)], 'o3'), (net[('W', (k + 1) % 4)], 'o3'), (net[('W', k)], 'o3')]
MODELS['net_typical'] = octa_model(o, k)
figs['lemmaF'] = svg_net_hl(o, k, far)
loc = [(net[('V', k)], 'o1'), (net[('V', (k + 3) % 4)], 'o1'), (net[('W', k)], 'o3'), (net[('W', (k + 3) % 4)], 'o3')]
figs['lemmaL'] = svg_net_hl(o, k, loc)
figs['octa_shared'] = svg_net_hl(o, k, [(net[('W', (k + 1) % 4)], 'o1'), (net[('W', (k + 2) % 4)], 'o1'), (net[('V', (k + 1) % 4)], 'o1'), (net[('V', (k + 2) % 4)], 'o1')])
# a fixed tree failing: same octahedron as the typical net but another apex/slit that overlaps, if any; else a case from cases.pkl
cases = pickle.load(open('cases_opp/cases.pkl', 'rb'))
found = None
st = octa_structure(Pn)
for oo in all_apexes(Pn, st[0], st[1]):
    for kk in range(4):
        if oo.overlaps(kk): found = (oo, kk); break
    if found: break
if found is None:
    d = cases[8]; oo = Octa(d['P'], d['v']); kk = d['k']; found = (oo, kk)
oo, kk = found; hits = list(oo.overlaps(kk))
figs['octa_false'] = svg_net(oo, kk, highlight=hits); MODELS['octa_false'] = octa_model(oo, kk)
figs['octa_false_meta'] = dict(v=oo.v, k=kk, kv=round(float(oo.kv), 3), pairs=hits, sharpest=int(max(range(6), key=lambda x: oo.kappa[x])))
# closest approach under (H) (evidence figure)
res = pickle.load(open('adv_opp_H3_d.pkl', 'rb')); b, Pb = res[0]; ob = Octa(Pb, b[1])
figs['evidence'] = svg_net(ob, b[2], highlight=[b[3]]); MODELS['evidence'] = octa_model(ob, b[2])
figs['evidence_meta'] = dict(sep=round(float(b[4]), 4), kv=round(float(ob.kv), 3), ku=[round(float(x), 3) for x in ob.ku])
# triple without extras (F_triple) and rotation overlay (F_rot), angular (F_angular), notboth (F_notboth)
Pt = np.load('notes/figs/triple_H3.npy'); ot = Octa(Pt, 0); i = 1; kt = (i - 1) % 4
MODELS['triple_H3'] = octa_model(ot, kt)
figs['F_triple'] = svg_net_hl(ot, kt, [(ot.Z(kt)[('V', i)], 'o1'), (ot.Z(kt)[('V', (i + 2) % 4)], 'o1'), (ot.Z(kt)[('V', (i + 1) % 4)], 'o2')])
def flat_overlay(o, i):
    k = (i - 1) % 4; net = o.Z(k); j, jj = (i + 1) % 4, (i + 2) % 4
    Vi, Vj, Vjj = net[('V', i)], net[('V', j)], net[('V', jj)]; uj, ujj, vj = Vj[2], Vj[1], Vj[0]; kj, kjj = o.ku[j], o.ku[jj]
    sgn = [sg for sg in (1, -1) if np.linalg.norm(rotate_about(Vi[:1], uj, -sg * kj)[0] - vj) < 1e-7 * o.scale][0]
    Vi_f = rotate_about(Vi, uj, -sgn * kj); Vjj_f = rotate_about(Vjj, ujj, sgn * kjj)
    ex = triple_extras(o, i)
    ex += [dict(kind='poly', cls='flat', pts=list(Vi_f)), dict(kind='poly', cls='flat', pts=list(Vjj_f))]
    return ex
figs['F_rot'] = svg_net(ot, kt, extras=flat_overlay(ot, i))
figs['F_angular'] = figs['F_rot']
figs['F_notboth'] = figs['F_rot']
figs['F_side'] = figs['overlap_above']
figs['F_nocross'] = figs['overlap_above']
figs['F_hinge'] = svg_net_hl(o, k, [(net[('W', (k + 1) % 4)], 'o3'), (net[('W', (k + 2) % 4)], 'o3')])
figs['F_sharp'] = ''   # drawn inline in the page (axis diagram)
figs['root'] = figs['net_typical']; figs['n6'] = ''
for idx, key in ((0, 'overlap_above'), (4, 'overlap_below')):
    d = cases[idx]; oc = Octa(d['P'], d['v']); kc = d['k']; nmc = d['pair']; ic = kc if nmc == 'V_k-V_k+2' else (kc + 1) % 4
    MODELS[key] = octa_model(oc, (ic - 1) % 4)
figs['models'] = MODELS
json.dump(figs, open('notes/status_figs.json', 'w'))
print(sorted(k for k in figs if not k.endswith('_meta')))

# ---------------------------------------------------------------- widget presets (cylindrical parameters)
def params(P, v):
    o = Octa(P, v); w = o.w; ring = o.u
    c = (P[v] + P[w]) / 2; ez = P[v] - c; ez /= np.linalg.norm(ez)
    x0 = P[ring[0]] - c; ex = x0 - np.dot(x0, ez) * ez; ex /= np.linalg.norm(ex); ey = np.cross(ez, ex)
    Q = lambda q: np.array([np.dot(q - c, ex), np.dot(q - c, ey), np.dot(q - c, ez)])
    scale = max(np.linalg.norm(P[v] - c), np.linalg.norm(P[w] - c), *[np.linalg.norm(Q(P[u])[:2]) for u in ring])
    pr = dict(zv=float(np.linalg.norm(P[v] - c) / scale), zw=float(np.linalg.norm(P[w] - c) / scale), u=[])
    for u in ring:
        q = Q(P[u]) / scale; r = float(np.hypot(q[0], q[1])); phi = float(np.degrees(np.arctan2(q[1], q[0])) % 360)
        pr['u'].append(dict(r=round(r, 4), phi=round(phi, 2), z=round(float(q[2]), 4)))
    order = sorted(range(4), key=lambda i: pr['u'][i]['phi'])
    if order in ([3, 2, 1, 0], [0, 3, 2, 1], [1, 0, 3, 2], [2, 1, 0, 3]):
        pr['u'] = [dict(d, phi=(360 - d['phi']) % 360) for d in pr['u']]; order = sorted(range(4), key=lambda i: pr['u'][i]['phi'])
    assert order in ([0, 1, 2, 3], [1, 2, 3, 0], [2, 3, 0, 1], [3, 0, 1, 2]), order
    pts = [np.array([0, 0, pr['zv']]), np.array([0, 0, -pr['zw']])] + [np.array([d['r'] * np.cos(np.radians(d['phi'])), d['r'] * np.sin(np.radians(d['phi'])), d['z']]) for d in pr['u']]
    assert octa_structure(np.array(pts)) is not None; o2 = Octa(np.array(pts), 0); assert abs(o2.kv - o.kv) < 1e-4
    return pr
presets = {}
Pn = np.load('notes/figs/net_typical.npy'); stn = octa_structure(Pn); presets['Typical (v sharpest)'] = params(Pn, sharpest_apex(Pn, stn[0], stn[1]).v)
presets['Above-base overlap (no hypothesis)'] = params(cases[0]['P'], cases[0]['v'])
presets['Below-base overlap (no hypothesis)'] = params(cases[4]['P'], cases[4]['v'])
presets['Triple under (H)'] = params(np.load('notes/figs/triple_H3.npy'), 0)
presets['Regular octahedron'] = params(np.array([(0, 0, 1), (0, 0, -1), (1, 0, 0), (0, 1, 0), (-1, 0, 0), (0, -1, 0)], float), 0)
presets['Needle'] = params(np.array([(0, 0, 3.0), (0, 0, -3.0), (0.5, 0, 0.1), (0, 0.4, -0.1), (-0.45, 0, 0.05), (0, -0.5, 0)], float), 0)
presets['Flat'] = params(np.array([(0, 0, 0.25), (0.1, 0, -0.2), (1.2, 0, 0), (0, 1, 0.05), (-1, 0.1, 0), (0.1, -1.1, 0)], float), 0)
figs['presets'] = presets
json.dump(figs, open('notes/status_figs.json', 'w'))
print("presets:", list(presets))

# ---------------------------------------------------------------- figures for the Definitions page
def sector(c, a0, a1, rad, n=24):
    ang = np.linspace(a0, a1, n); return [c] + [c + rad * np.array([np.cos(t), np.sin(t)]) for t in ang]
def ang_of(p, c): return np.arctan2(p[1] - c[1], p[0] - c[0])
def ccw_span(a0, a1):  # angles from a0 ccw to a1
    d = (a1 - a0) % (2 * np.pi); return a0, a0 + d
def svg_net_ex(o, k, extras, **kw):
    return svg_net(o, k, extras=extras, **kw)

Pn = np.load('notes/figs/net_typical.npy'); stn = octa_structure(Pn); on = sharpest_apex(Pn, stn[0], stn[1]); kn = int(np.argmax(on.ku)); netn = on.Z(kn)
# Definition 2: the gap at the equator vertex u_{k+2} (shared copy) and at w
j = (kn + 2) % 4; Wj, Wjm, Vj, Vjm = netn[('W', j)], netn[('W', (j - 1) % 4)], netn[('V', j)], netn[('V', (j - 1) % 4)]
uj = Wj[1]; rad = 0.09 * on.scale
a_vj = ang_of(Vj[0], uj); a_vjm = ang_of(Vjm[0], uj)
# the gap is the sector at u_j not covered by the four faces: between the two v copies, on the side away from w
a0, a1 = ccw_span(a_vj, a_vjm)
if (a1 - a0) > np.pi: a0, a1 = ccw_span(a_vjm, a_vj)
ex = [dict(kind='poly', cls='gapwedge', pts=sector(uj, a0, a1, rad)), dict(kind='point', cls='pstar', pts=uj, label='κ at u' + '₀₁₂₃'[(j - kn) % 4])]
# gap at w between ray w u_k and ray w u_k'
uk = netn[('W', kn)][1]; ukp = netn[('W', (kn + 3) % 4)][2]; w0 = np.zeros(2)
b0, b1 = ccw_span(ang_of(ukp, w0), ang_of(uk, w0))
if (b1 - b0) > np.pi: b0, b1 = ccw_span(ang_of(uk, w0), ang_of(ukp, w0))
ex += [dict(kind='poly', cls='gapwedge', pts=sector(w0, b0, b1, 0.12 * on.scale)), dict(kind='point', cls='pstar', pts=w0 + 0.13 * on.scale * np.array([np.cos((b0 + b1) / 2), np.sin((b0 + b1) / 2)]), label='κ_w')]
figs['def_gap'] = svg_net(on, kn, extras=ex)
figs['def_Zk'] = svg_net(on, kn, extras=[dict(kind='poly', cls='gapwedge', pts=sector(w0, b0, b1, 0.5 * on.scale)), dict(kind='line', cls='cutline', pts=(w0, uk)), dict(kind='line', cls='cutline', pts=(w0, ukp))])
# Definition 6: annotated triple (triple_H3, i=1)
Pt = np.load('notes/figs/triple_H3.npy'); ot = Octa(Pt, 0); i = 1; kt = (i - 1) % 4; nt = ot.Z(kt); jj = (i + 2) % 4; j = (i + 1) % 4
Vi, Vj, Vjj = nt[('V', i)], nt[('V', j)], nt[('V', jj)]; u, up, vj = Vj[2], Vj[1], Vj[0]; vi, vjj = Vi[0], Vjj[0]
r0 = 0.07 * ot.scale
phi0, phi1 = ccw_span(ang_of(up, u), ang_of(vj, u)); psi0, psi1 = ccw_span(ang_of(vj, up), ang_of(u, up)); nu0, nu1 = ccw_span(ang_of(u, vj), ang_of(up, vj))
for (a, b), c in (((phi0, phi1), u), ((psi0, psi1), up), ((nu0, nu1), vj)):
    pass
def fix(span, c, other):  # choose the span containing the interior of V_j (the direction to the third vertex)
    a0, a1 = span; m = ang_of(other, c); d = (m - a0) % (2 * np.pi); return span if d < (a1 - a0) else ccw_span(a1, a0)
phi = fix((phi0, phi1), u, (up + vj) / 2); psi = fix((psi0, psi1), up, (u + vj) / 2); nu = fix((nu0, nu1), vj, (u + up) / 2)
d1 = (vi - u) / np.linalg.norm(vi - u); d2 = (vjj - up) / np.linalg.norm(vjj - up); L = 0.9 * ot.scale
ex = [dict(kind='poly', cls='anglearc', pts=sector(u, *phi, r0)), dict(kind='poly', cls='anglearc', pts=sector(up, *psi, r0)), dict(kind='poly', cls='anglearc', pts=sector(vj, *nu, r0)),
      dict(kind='line', cls='cutline', pts=(u - L * d1, u + L * d1)), dict(kind='line', cls='cutline', pts=(up - L * d2, up + L * d2)),
      dict(kind='point', cls='pstar', pts=u, label='u'), dict(kind='point', cls='pstar', pts=up, label='u′'),
      dict(kind='point', cls='cstar', pts=vj, label='v_j'), dict(kind='point', cls='cstar', pts=vi, label='v_i'), dict(kind='point', cls='cstar', pts=vjj, label='v_j+1'),
      dict(kind='point', cls='none', pts=u + 1.6 * r0 * np.array([np.cos(np.mean(phi)), np.sin(np.mean(phi))]), label='φ'),
      dict(kind='point', cls='none', pts=up + 1.6 * r0 * np.array([np.cos(np.mean(psi)), np.sin(np.mean(psi))]), label='ψ'),
      dict(kind='point', cls='none', pts=vj + 1.6 * r0 * np.array([np.cos(np.mean(nu)), np.sin(np.mean(nu))]), label='ν_j')]
figs['def_triple'] = svg_net(ot, kt, extras=ex, labels=False)
# 3D models for definitions: the typical octahedron (already 'net_typical'), the flat and the regular preset shapes
def preset_model(name):
    p = figs['presets'][name]; pts = [[0, 0, p['zv']], [0, 0, -p['zw']]] + [[d['r'] * np.cos(np.radians(d['phi'])), d['r'] * np.sin(np.radians(d['phi'])), d['z']] for d in p['u']]
    P = np.array(pts); o = Octa(P, 0); return octa_model(o, int(np.argmax(o.ku)))
MODELS['def_flat'] = preset_model('Flat'); MODELS['def_regular'] = preset_model('Regular octahedron')
figs['models'] = MODELS
json.dump(figs, open('notes/status_figs.json', 'w'))
print("definition figures added")

# ---------------------------------------------------------------- fat near-misses (adv_fat.py results)
def add_nearmiss(key, pkl):
    if not os.path.exists(pkl): return
    res = pickle.load(open(pkl, 'rb')); b, P = res[0]; o = Octa(P, b[1]); k = b[2]
    figs[key] = svg_net(o, k, highlight=[b[3]]); MODELS[key] = octa_model(o, k)
    figs[key + '_meta'] = dict(sep=round(float(b[4]), 4), thick=round(float(b[5]), 3), kv=round(float(o.kv), 3), kw=round(float(o.kw), 3), ku=[round(float(x), 3) for x in o.ku], pair=b[3])
import os
add_nearmiss('fat_nearmiss', 'adv_fat_0.30.pkl'); add_nearmiss('fat_round_nearmiss', 'adv_fat_0.30_k0.30.pkl')
figs['models'] = MODELS
json.dump(figs, open('notes/status_figs.json', 'w'))
print("near-miss figures:", [k for k in ('fat_nearmiss', 'fat_round_nearmiss') if k in figs])
