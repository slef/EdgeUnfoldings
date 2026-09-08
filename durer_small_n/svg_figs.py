"""Generate SVG figures for the status page (notes/status_figs.json): real nets from octa.py and schematic
planar maps of the seven 6-vertex types.  Colors are CSS variables so the page can theme them."""
import numpy as np, json, pickle
from octa import *
from cstar import rotate_about, signed_side
from adv_opp import DELTA, violation

def svg_net(o, k, highlight=(), extras=None, labels=True, W=520, H=420, pad=22):
    net = o.Z(k)
    pts = np.vstack([T for key, T in net.items() if isinstance(key, tuple)])
    if extras: pts = np.vstack([pts] + [np.atleast_2d(e['pts']) for e in extras if 'pts' in e])
    lo, hi = pts.min(0), pts.max(0); span = (hi - lo).max()
    sc = min((W - 2 * pad) / (hi[0] - lo[0] + 1e-12), (H - 2 * pad) / (hi[1] - lo[1] + 1e-12))
    cx, cy = (lo + hi) / 2
    def P(q): return (W / 2 + (q[0] - cx) * sc, H / 2 - (q[1] - cy) * sc)
    def fmt(q): x, y = P(q); return "%.1f,%.1f" % (x, y)
    out = ['<svg viewBox="0 0 %d %d" xmlns="http://www.w3.org/2000/svg" class="net">' % (W, H)]
    for key, T in net.items():
        if not isinstance(key, tuple): continue
        typ, j = key; t = (j - k) % 4; prime = "′" if t == 3 else ""
        cls = 'fan' if typ == 'W' else 'petal'
        out.append('<polygon class="%s" points="%s %s %s"/>' % (cls, fmt(T[0]), fmt(T[1]), fmt(T[2])))
    for nm in highlight:
        X = o.intersection(k, nm)
        if len(X) >= 3: out.append('<polygon class="hit" points="%s"/>' % " ".join(fmt(q) for q in X))
    for e in (extras or []):
        if e['kind'] == 'line':
            a, b = e['pts']; out.append('<line class="%s" x1="%s" y1="%s" x2="%s" y2="%s"/>' % ((e['cls'],) + P(a) + P(b)))
        elif e['kind'] == 'point':
            x, y = P(e['pts']); out.append('<circle class="%s" cx="%.1f" cy="%.1f" r="3.2"/>' % (e['cls'], x, y))
            if e.get('label'): out.append('<text class="lbl %s" x="%.1f" y="%.1f">%s</text>' % (e['cls'], x + 5, y - 5, e['label']))
        elif e['kind'] == 'poly':
            out.append('<polygon class="%s" points="%s"/>' % (e['cls'], " ".join(fmt(q) for q in e['pts'])))
    if labels:
        for key, T in net.items():
            if not isinstance(key, tuple): continue
            typ, j = key; t = (j - k) % 4; prime = "′" if t == 3 else ""
            c = T.mean(0); x, y = P(c)
            out.append('<text class="face" x="%.1f" y="%.1f" text-anchor="middle" dominant-baseline="middle">%s<tspan class="sub">%d%s</tspan></text>' % (x, y, typ, t, prime))
        for t in range(4):
            j = (k + t) % 4; Wf = net[('W', j)]; V = net[('V', j)]
            x, y = P(Wf[1]); out.append('<text class="lbl vtx" x="%.1f" y="%.1f">u<tspan class="sub">%d</tspan></text>' % (x + 3, y - 3, t))
            x, y = P(V[0]); out.append('<text class="lbl apex" x="%.1f" y="%.1f">v</text>' % (x + 3, y - 3))
        Wf = net[('W', (k + 3) % 4)]; x, y = P(Wf[2])
        out.append('<text class="lbl vtx" x="%.1f" y="%.1f">u<tspan class="sub">0</tspan>′</text>' % (x - 16, y - 3))
        x, y = P(np.zeros(2)); out.append('<circle class="w" cx="%.1f" cy="%.1f" r="3"/><text class="lbl" x="%.1f" y="%.1f">w</text>' % (x, y, x + 5, y + 12))
    out.append('</svg>')
    return "\n".join(out)

def triple_extras(o, i, with_D=True):
    """cut-edge lines, p*, D (clipped), c*, M for the triple (i, i+1, i+2) in the net with slit k=i-1."""
    k = (i - 1) % 4; net = o.Z(k); j, jj = (i + 1) % 4, (i + 2) % 4
    Vi, Vj, Vjj = net[('V', i)], net[('V', j)], net[('V', jj)]
    uj, ujj, vj = Vj[2], Vj[1], Vj[0]; kj, kjj = o.ku[j], o.ku[jj]; kap = kj + kjj
    d1 = (Vi[0] - uj) / np.linalg.norm(Vi[0] - uj); d2 = (Vjj[0] - ujj) / np.linalg.norm(Vjj[0] - ujj)
    L = 0.9 * o.scale
    ex = [dict(kind='line', cls='cutline', pts=(uj - L * d1, uj + L * d1)), dict(kind='line', cls='cutline', pts=(ujj - L * d2, ujj + L * d2))]
    M = np.array([d1, -d2]).T
    if abs(np.linalg.det(M)) > 1e-12:
        t = np.linalg.solve(M, ujj - uj); ps = uj + t[0] * d1
        ex.append(dict(kind='point', cls='pstar', pts=ps, label='p*'))
        if with_D:
            s = 1 if t[0] > 0 else -1; Lw = 0.5 * o.scale
            ex.append(dict(kind='poly', cls='Dwedge', pts=[ps, ps + s * Lw * d1, ps + s * Lw * d2]))
    cand = [sg for sg in (1, -1) if np.linalg.norm(rotate_about(Vi[:1], uj, -sg * kj)[0] - vj) < 1e-7 * o.scale]
    if cand and kap < o.nu[j]:
        sgn = cand[0]
        def R(X): return rotate_about(rotate_about(X, uj, sgn * kj), ujj, sgn * kjj)
        A = rot(sgn * kap); b = R(np.zeros((1, 2)))[0]; cs = np.linalg.solve(np.eye(2) - A, b)
        m = (vj - cs) / np.linalg.norm(vj - cs)
        ex.append(dict(kind='line', cls='Mline', pts=(cs - 0.15 * o.scale * m, cs + 0.7 * o.scale * m)))
        ex.append(dict(kind='point', cls='cstar', pts=cs, label='c*'))
    return ex

# ---- schematic planar maps (Schlegel-like) of the seven 6-vertex types --------------------------------------
def icon(nodes, edges, quad_faces=(), W=120, H=110):
    out = ['<svg viewBox="0 0 %d %d" xmlns="http://www.w3.org/2000/svg" class="icon">' % (W, H)]
    for f in quad_faces:
        out.append('<polygon class="quad" points="%s"/>' % " ".join("%.1f,%.1f" % nodes[i] for i in f))
    for a, b in edges:
        out.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f"/>' % (nodes[a] + nodes[b]))
    for i, (x, y) in enumerate(nodes):
        out.append('<circle cx="%.1f" cy="%.1f" r="3.4"/>' % (x, y))
    out.append('</svg>'); return "\n".join(out)

def reg(n, r, cx=60, cy=57, rot=-np.pi / 2):
    return [(cx + r * np.cos(rot + 2 * np.pi * i / n), cy + r * np.sin(rot + 2 * np.pi * i / n)) for i in range(n)]

icons = {}
# 1 pentagonal pyramid
nd = reg(5, 46) + [(60, 60)]; icons['pyr5'] = icon(nd, [(i, (i + 1) % 5) for i in range(5)] + [(i, 5) for i in range(5)])
# 2 prism
nd = reg(3, 50, cy=62) + reg(3, 22, cy=62); icons['prism'] = icon(nd, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5)], quad_faces=[(0, 1, 4, 3), (1, 2, 5, 4), (2, 0, 3, 5)])
# 3 prism + diagonal
icons['prismd'] = icon(nd, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5), (0, 4)], quad_faces=[(1, 2, 5, 4), (2, 0, 3, 5)])
# simplicial (5,5,4,4,3,3): outer 0,1,2; center 3; 4 in face (0,1,3); 5 in face (0,2,3)
o3 = reg(3, 50, cy=62); c = (60, 62)
nd = o3 + [c, ((o3[0][0] + o3[1][0] + c[0]) / 3, (o3[0][1] + o3[1][1] + c[1]) / 3), ((o3[0][0] + o3[2][0] + c[0]) / 3, (o3[0][1] + o3[2][1] + c[1]) / 3)]
E6 = [(0, 1), (1, 2), (2, 0), (0, 3), (1, 3), (2, 3), (4, 0), (4, 1), (4, 3), (5, 0), (5, 2), (5, 3)]
icons['simp55'] = icon(nd, E6)
# (5,4,4,3,3,3): remove edge 1-3 -> quad 1,4,3,2
icons['t54'] = icon(nd, [e for e in E6 if e != (1, 3)], quad_faces=[(1, 4, 3, 2)])
# octahedron minus an edge (4,4,4,4,3,3): remove edge 0-3 -> quad 0,4,3,5
icons['octa_minus'] = icon(nd, [e for e in E6 if e != (0, 3)], quad_faces=[(0, 4, 3, 5)])
# octahedron
nd = reg(3, 50, cy=62) + reg(3, 16, cy=62, rot=np.pi / 2)   # inner triangle small enough that the side triangles are visible
icons['octa'] = icon(nd, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 4), (0, 5), (1, 5), (1, 3), (2, 4), (2, 3)])   # planar: each outer vertex joins the two nearest inner ones

figs = {'icons': icons}
# ---- nets ---------------------------------------------------------------------------------------------------
P = np.load('notes/figs/net_typical.npy'); o = Octa(P, 0); k = int(np.argmax(o.ku))
figs['net_typical'] = svg_net(o, k)
figs['net_typical_meta'] = dict(kv=round(float(o.kv), 3), kw=round(float(o.kw), 3), ku=[round(float(x), 3) for x in o.ku], k=k)
cases = pickle.load(open('cases_opp/cases.pkl', 'rb'))
d = cases[0]; o = Octa(d['P'], d['v']); k = d['k']; nm = d['pair']; i = k if nm == 'V_k-V_k+2' else (k + 1) % 4
figs['overlap_above'] = svg_net(o, (i - 1) % 4, highlight=["V_k+1-V_k-1'"], extras=triple_extras(o, i))
figs['overlap_above_meta'] = dict(kv=round(float(o.kv), 3), ku=[round(float(x), 3) for x in o.ku], nu=[round(float(x), 3) for x in o.nu], i=i)
d = cases[4]; o = Octa(d['P'], d['v']); k = d['k']; nm = d['pair']; i = k if nm == 'V_k-V_k+2' else (k + 1) % 4
figs['overlap_below'] = svg_net(o, (i - 1) % 4, highlight=["V_k+1-V_k-1'"], extras=triple_extras(o, i, with_D=False))
figs['overlap_below_meta'] = dict(kv=round(float(o.kv), 3), ku=[round(float(x), 3) for x in o.ku], nu=[round(float(x), 3) for x in o.nu], i=i)
P = np.load('notes/figs/triple_H3.npy'); o = Octa(P, 0); i = 1
figs['triple_H3'] = svg_net(o, (i - 1) % 4, extras=triple_extras(o, i))
figs['triple_H3_meta'] = dict(kv=round(float(o.kv), 3), kw=round(float(o.kw), 3), ku=[round(float(x), 3) for x in o.ku], nu=[round(float(x), 3) for x in o.nu], i=i)
json.dump(figs, open('notes/status_figs.json', 'w'))
print({k: len(v) if isinstance(v, str) else v for k, v in figs.items() if k != 'icons'}, "icons:", list(icons))
