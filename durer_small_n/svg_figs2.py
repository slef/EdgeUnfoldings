"""Additional SVG figures for the status page (one per case).  Merges into notes/status_figs.json."""
import numpy as np, json, pickle, itertools
from octa import *
from cstar import rotate_about
from svg_figs import svg_net, triple_extras
from unfold2 import Polytope as PolyP, unfold as unfold2, sat_pen as sat2

figs = json.load(open('notes/status_figs.json'))

# ---------------------------------------------------------------- generic net renderer for any small polytope
def svg_poly(p, cut, W=520, H=380, pad=22, labels=None, hl=(), title_face=None):
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

VN = {}
def with_names(names):
    global VN; VN = names

def apex_star(p, v): return [e for e in p.edges if v in e]

# ---------------------------------------------------------------- sample polytopes for each type
rng = np.random.default_rng(7)
def reg(n, r, z=0.0, rot=0.0): return [(r * np.cos(rot + 2 * np.pi * i / n), r * np.sin(rot + 2 * np.pi * i / n), z) for i in range(n)]

# tetrahedron
P = np.array([(0, 0, 1.1), (1, 0, 0), (-0.4, 0.9, 0), (-0.5, -0.8, -0.1)], float); p = PolyP(P)
with_names({0: 'v'}); figs['n4'], _ = svg_poly(p, apex_star(p, 0), labels=lambda f: '')
# square pyramid and triangular bipyramid
P = np.array([(0, 0, 1.0)] + reg(4, 1.0, 0, 0.3), float); P[1:, 0] *= 1.3; p = PolyP(P)
with_names({0: 'v'}); figs['n5_pyr'], _ = svg_poly(p, apex_star(p, 0), labels=lambda f: '')
P = np.array([(0, 0, 1.2), (0, 0, -0.9)] + reg(3, 1.0, 0, 0.2), float); p = PolyP(P)
deg = {v: sum(v in e for e in p.edges) for v in range(5)}; v4 = [v for v in range(5) if deg[v] == 4][0]
with_names({v4: 'v'}); figs['n5_bipyr'], _ = svg_poly(p, apex_star(p, v4), labels=lambda f: '')
# pentagonal pyramid
P = np.array([(0.1, 0, 1.0)] + reg(5, 1.0, 0, 0.1), float); P[1:, 1] *= 0.8; p = PolyP(P)
with_names({0: 'v'}); figs['t_pyr5'], _ = svg_poly(p, apex_star(p, 0), labels=lambda f: '')
figs['lemmaA'] = figs['t_pyr5']
# hexagonal pyramid (n=7 illustration)
P = np.array([(0.05, 0.1, 1.0)] + reg(6, 1.0, 0, 0.05), float); P[1:, 0] *= 1.2; p = PolyP(P)
with_names({0: 'v'}); figs['n7'], _ = svg_poly(p, apex_star(p, 0), labels=lambda f: '')
# simplicial 5,5,4,4,3,3 : tetrahedron 0,1,2,3 + bumps 4 (over face 0,1,3) and 5 (over face 0,2,3)
T = np.array([(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)], float)
b4 = (T[0] + T[1] + T[3]) / 3; n4 = np.cross(T[1] - T[0], T[3] - T[0]); n4 /= np.linalg.norm(n4)
if np.dot(n4, b4 - T.mean(0)) < 0: n4 = -n4
b5 = (T[0] + T[2] + T[3]) / 3; n5 = np.cross(T[2] - T[0], T[3] - T[0]); n5 /= np.linalg.norm(n5)
if np.dot(n5, b5 - T.mean(0)) < 0: n5 = -n5
P = np.vstack([T, b4 + 0.45 * n4, b5 + 0.45 * n5]); p = PolyP(P)
deg = {v: sum(v in e for e in p.edges) for v in range(6)}; assert sorted(deg.values()) == [3, 3, 4, 4, 5, 5], deg
v5 = [v for v in range(6) if deg[v] == 5][0]
with_names({v5: 'v'}); figs['t_simp55'], _ = svg_poly(p, apex_star(p, v5), labels=lambda f: '')
# type 5,4,4,3,3,3: apex over a base made of a planar quad + a lower triangle
B = [(1, 0, 0), (0.3, 1, 0), (-0.8, 0.6, 0), (-0.8, -0.6, 0), (0.3, -1, 0)]   # b0..b4 ; quad b1 b2 b3 b4 planar, b0 lowered
P = np.array([(0, 0.1, 1.2)] + B, float); P[1, 2] = 0.15; P[1, 0] = 1.3; p = PolyP(P)
fs = sorted(len(f) for f in p.faces); deg = {v: sum(v in e for e in p.edges) for v in range(6)}
assert fs == [3, 3, 3, 3, 3, 3, 4] and sorted(deg.values()) == [3, 3, 3, 4, 4, 5], (fs, deg)
with_names({0: 'v'}); figs['t_54'], _ = svg_poly(p, apex_star(p, 0), labels=lambda f: '')
# prism: strip of quads, triangles on the middle quad
A, Bq, C = np.array([(0, 0, 0), (1.3, 0, 0), (0.4, 1.0, 0)], float); up = np.array([0.15, 0.1, 1.1])
P = np.vstack([A, Bq, C, A + up, Bq + up, C + up]); p = PolyP(P)
with_names({0: 'A', 1: 'B', 2: 'C', 3: "A′", 4: "B′", 5: "C′"})
figs['t_prism'], bad = svg_poly(p, [(0, 3), (0, 1), (0, 2), (3, 4), (3, 5)], labels=lambda f: ''); assert not bad
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
figs['t_prismd'], bad = svg_poly(p, p.cut_set(good[0]), labels=lambda f: ''); assert not bad
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
figs['t_octa_minus'], bad = svg_poly(p, p.cut_set(good[0]), labels=lambda f: ''); assert not bad

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
figs['octa_false'] = svg_net(oo, kk, highlight=hits)
figs['octa_false_meta'] = dict(v=oo.v, k=kk, kv=round(float(oo.kv), 3), pairs=hits, sharpest=int(max(range(6), key=lambda x: oo.kappa[x])))
# closest approach under (H) (evidence figure)
res = pickle.load(open('adv_opp_H3_d.pkl', 'rb')); b, Pb = res[0]; ob = Octa(Pb, b[1])
figs['evidence'] = svg_net(ob, b[2], highlight=[b[3]])
figs['evidence_meta'] = dict(sep=round(float(b[4]), 4), kv=round(float(ob.kv), 3), ku=[round(float(x), 3) for x in ob.ku])
# triple without extras (F_triple) and rotation overlay (F_rot), angular (F_angular), notboth (F_notboth)
Pt = np.load('notes/figs/triple_H3.npy'); ot = Octa(Pt, 0); i = 1; kt = (i - 1) % 4
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
json.dump(figs, open('notes/status_figs.json', 'w'))
print(sorted(k for k in figs if not k.endswith('_meta')))
