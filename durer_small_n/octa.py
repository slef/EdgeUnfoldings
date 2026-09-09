"""Octahedron-type polytopes: named quantities of HANDOFF.md, the nets Z_k, the nine face pairs.

Conventions (HANDOFF.md): antipodal pair (v, w), equator u_0..u_3 = neighbours of w, cyclic and CCW
around w seen from outside.  W_i = w u_i u_{i+1},  V_i = v u_i u_{i+1},  Q_i = W_i ∪ V_i.
Z_k = net of cut tree star(v) ∪ {w u_k}: fan W_k, W_{k+1}, W_{k+2}, W_{k-1}' around w, opened along w u_k,
petal V_i glued to W_i.  In Z_k, w is at the origin and the ray w u_k (first copy) is the +x axis; the fan
runs counter-clockwise, the gap of angle κ_w comes last.

All indices i are ring indices mod 4.  Angles in radians.
"""
import numpy as np, itertools, collections
from scipy.spatial import ConvexHull

TWO_PI = 2 * np.pi

# ----------------------------------------------------------------------------------------------------
# small planar helpers
def angle_at(b, a, c):
    """angle a-b-c at b, in [0, π]."""
    x = a - b; y = c - b
    return np.arccos(np.clip(np.dot(x, y) / (np.linalg.norm(x) * np.linalg.norm(y)), -1, 1))

def rot(th):
    c, s = np.cos(th), np.sin(th); return np.array([[c, -s], [s, c]])

def third_point(A, B, la, lb, left=True):
    """Point C with |CA| = la, |CB| = lb, to the left (or right) of the directed segment A→B."""
    d = B - A; L = np.linalg.norm(d); d = d / L
    x = (la**2 - lb**2 + L**2) / (2 * L)
    h = np.sqrt(max(la**2 - x**2, 0.0))
    n = np.array([-d[1], d[0]]) * (1 if left else -1)
    return A + x * d + h * n

def clip_convex(subject, clipper):
    """Sutherland–Hodgman: subject ∩ clipper, both CCW convex polygons (arrays k×2)."""
    out = list(subject)
    m = len(clipper)
    for i in range(m):
        A, B = clipper[i], clipper[(i + 1) % m]
        inp = out; out = []
        if not inp: break
        def inside(p): return (B[0]-A[0])*(p[1]-A[1]) - (B[1]-A[1])*(p[0]-A[0]) >= 0
        def inter(p, q):
            d1 = (B[0]-A[0])*(p[1]-A[1]) - (B[1]-A[1])*(p[0]-A[0])
            d2 = (B[0]-A[0])*(q[1]-A[1]) - (B[1]-A[1])*(q[0]-A[0])
            t = d1 / (d1 - d2); return p + t * (q - p)
        S = inp[-1]
        for E in inp:
            if inside(E):
                if not inside(S): out.append(inter(S, E))
                out.append(E)
            elif inside(S): out.append(inter(S, E))
            S = E
    return np.array(out) if out else np.zeros((0, 2))

def poly_area(p):
    if len(p) < 3: return 0.0
    x, y = p[:, 0], p[:, 1]
    return 0.5 * abs(np.dot(x, np.roll(y, -1)) - np.dot(y, np.roll(x, -1)))

def sat_pen(T1, T2):
    """Penetration depth of two convex CCW polygons (0 if separated / touching)."""
    best = np.inf
    for T in (T1, T2):
        e = np.roll(T, -1, axis=0) - T
        n = np.stack([-e[:, 1], e[:, 0]], axis=-1)
        n /= np.linalg.norm(n, axis=-1, keepdims=True) + 1e-300
        p1 = n @ T1.T; p2 = n @ T2.T
        ov = np.minimum(p1.max(1), p2.max(1)) - np.maximum(p1.min(1), p2.min(1))
        best = min(best, ov.min())
    return max(0.0, float(best))

def ccw(T):
    x, y = T[:, 0], T[:, 1]
    return 0.5 * (np.dot(x, np.roll(y, -1)) - np.dot(y, np.roll(x, -1))) > 0

# ----------------------------------------------------------------------------------------------------
def octa_structure(P):
    """Return (faces, adj) if P is a simplicial 6-vertex polytope with all degrees 4, else None."""
    P = np.asarray(P, float)
    if len(P) != 6: return None
    try: h = ConvexHull(P)
    except Exception: return None
    if len(h.vertices) != 6 or len(h.simplices) != 8: return None
    # Qhull triangulates flat polygonal facets. Degree four in that
    # triangulation does not establish the octahedral combinatorial type.
    # Reject coplanar facet mergers (and numerically unresolved near-mergers).
    scale = np.max(np.linalg.norm(P[:, None] - P[None], axis=-1))
    tol = 64 * np.finfo(float).eps * scale
    for s, eq in zip(h.simplices, h.equations):
        other = [v for v in range(6) if v not in s]
        if np.any((P[other] - P[s[0]]) @ eq[:3] >= -tol): return None
    faces = []
    for s, eq in zip(h.simplices, h.equations):
        a, b, c = P[s]
        if np.dot(np.cross(b - a, c - a), eq[:3]) < 0: s = s[[0, 2, 1]]
        faces.append(tuple(int(x) for x in s))
    adj = collections.defaultdict(set)
    for f in faces:
        for a, b in ((f[0], f[1]), (f[1], f[2]), (f[2], f[0])): adj[a].add(b); adj[b].add(a)
    if any(len(adj[x]) != 4 for x in range(6)): return None
    return faces, adj

class Octa:
    """One octahedron with a chosen apex v (w = antipode)."""
    PAIRS = {  # the nine pairs of Z_k that share no net vertex, as (face, face) with faces ('V'|'W', offset from k, primed?)
        'V_k-V_k-1\'':  (('V', 0), ('V', 3)),
        'V_k-W_k-1\'':  (('V', 0), ('W', 3)),
        'V_k-1\'-W_k':  (('V', 3), ('W', 0)),
        'V_k-V_k+2':    (('V', 0), ('V', 2)),
        'V_k+1-V_k-1\'':(('V', 1), ('V', 3)),
        'V_k-W_k+2':    (('V', 0), ('W', 2)),
        'V_k+2-W_k':    (('V', 2), ('W', 0)),
        'V_k+1-W_k-1\'':(('V', 1), ('W', 3)),
        'V_k-1\'-W_k+1':(('V', 3), ('W', 1)),
    }
    LOCAL = ['V_k-V_k-1\'', 'V_k-W_k-1\'', 'V_k-1\'-W_k']
    OPP = ['V_k-V_k+2', 'V_k+1-V_k-1\'']
    FARFAN = ['V_k-W_k+2', 'V_k+2-W_k', 'V_k+1-W_k-1\'', 'V_k-1\'-W_k+1']

    def __init__(self, P, v, faces=None, adj=None):
        P = np.asarray(P, float)
        if faces is None:
            st = octa_structure(P)
            if st is None: raise ValueError("not an octahedron type")
            faces, adj = st
        self.P = P; self.faces = faces; self.adj = adj; self.v = v
        self.w = w = [x for x in range(6) if x != v and x not in adj[v]][0]
        # ring CCW around w seen from outside: faces (w, a, b) CCW  ⇒  b follows a
        nxt = {}
        for f in faces:
            if w in f:
                i = f.index(w); nxt[f[(i + 1) % 3]] = f[(i + 2) % 3]
        u0 = min(adj[w]); ring = [u0]
        while len(ring) < 4: ring.append(nxt[ring[-1]])
        self.u = ring
        self.scale = np.max(np.linalg.norm(P[:, None] - P[None], axis=-1))
        self.eps = 1e-9 * self.scale
        d = lambda a, b: np.linalg.norm(P[a] - P[b])
        A = lambda b, a, c: angle_at(P[b], P[a], P[c])
        u = ring; I = lambda i: u[i % 4]
        self.r = np.array([d(w, I(i)) for i in range(4)])            # |w u_i|
        self.s = np.array([d(v, I(i)) for i in range(4)])            # |v u_i|
        self.l = np.array([d(I(i), I(i + 1)) for i in range(4)])     # |u_i u_{i+1}|
        self.omega = np.array([A(w, I(i), I(i + 1)) for i in range(4)])
        self.nu = np.array([A(v, I(i), I(i + 1)) for i in range(4)])
        self.bW = np.array([A(I(i), w, I(i + 1)) for i in range(4)])       # W_i at u_i
        self.bWp = np.array([A(I(i + 1), w, I(i)) for i in range(4)])      # W_i at u_{i+1}
        self.aV = np.array([A(I(i), v, I(i + 1)) for i in range(4)])       # V_i at u_i
        self.aVp = np.array([A(I(i + 1), v, I(i)) for i in range(4)])      # V_i at u_{i+1}
        self.e = self.aV + self.bW                                       # Q_i at u_i
        self.f = self.aVp + self.bWp                                     # Q_i at u_{i+1}  (= f_{i+1} of HANDOFF)
        self.kw = TWO_PI - self.omega.sum()
        self.kv = TWO_PI - self.nu.sum()
        self.ku = np.array([TWO_PI - (self.bW[i] + self.bWp[i - 1] + self.aV[i] + self.aVp[i - 1]) for i in range(4)])
        self.kappa = {w: self.kw, v: self.kv, **{u[i]: self.ku[i] for i in range(4)}}
        # quads Q_i developed: w at origin, u_i on +x, u_{i+1} CCW, v to the right of u_i→u_{i+1}
        self.Q = []
        F = np.zeros(4); B = np.zeros(4)
        for i in range(4):
            wq = np.zeros(2); ui = np.array([self.r[i], 0.0])
            un = self.r[(i + 1) % 4] * np.array([np.cos(self.omega[i]), np.sin(self.omega[i])])
            vq = third_point(ui, un, self.s[i], self.s[(i + 1) % 4], left=False)
            self.Q.append({'w': wq, 'u': ui, 'un': un, 'v': vq})
            psi1 = angle_at(wq, ui, vq); psi2 = angle_at(wq, vq, un)
            if self.f[i] > np.pi: F[i] = max(0.0, psi1 - self.omega[i])   # reflex at u_{i+1}: lean over ray w u_{i+1}
            if self.e[i] > np.pi: B[i] = max(0.0, psi2 - self.omega[i])   # reflex at u_i: lean over ray w u_i
        self.F = F; self.B = B
        self._Z = {}

    # ------------------------------------------------------------------------------------------------
    def Z(self, k):
        """Net Z_k. Returns dict: ('W', j) / ('V', j) → 3×2 CCW array [w, u_j, u_{j+1}] / [v, u_{j+1}, u_j] in the
        net frame (w at origin, ray w u_k = +x, CCW fan), plus 'theta' = fan start angles of each W_j."""
        if k in self._Z: return self._Z[k]
        net = {}; th = 0.0; theta = {}
        for t in range(4):
            j = (k + t) % 4
            R = rot(th); q = self.Q[j]
            W = np.array([R @ q['w'], R @ q['u'], R @ q['un']]); V = np.array([R @ q['v'], R @ q['un'], R @ q['u']])
            net[('W', j)] = W; net[('V', j)] = V; theta[j] = th
            th += self.omega[j]
        net['theta'] = theta; net['k'] = k
        self._Z[k] = net
        return net

    def pair_faces(self, k, name):
        (ta, oa), (tb, ob) = self.PAIRS[name]
        net = self.Z(k)
        return net[(ta, (k + oa) % 4)], net[(tb, (k + ob) % 4)]

    def overlaps(self, k, names=None):
        """{pair name: penetration depth} for the pairs that overlap in Z_k (touching excluded)."""
        res = {}
        for nm in (names or self.PAIRS):
            A, Bf = self.pair_faces(k, nm)
            pen = sat_pen(A, Bf)
            if pen > self.eps: res[nm] = pen
        return res

    def simple(self, k):
        return not self.overlaps(k)

    def intersection(self, k, name):
        A, Bf = self.pair_faces(k, name)
        return clip_convex(A, Bf)

    def polar(self, p):
        """angle of net point p around w, in [0, 2π), measured from the ray w u_k."""
        return np.arctan2(p[1], p[0]) % TWO_PI

    def arc_of(self, k, p):
        """which arc of Z_k contains direction of p: ('W', j) or 'gap'."""
        a = self.polar(p); net = self.Z(k)
        for t in range(4):
            j = (k + t) % 4
            if net['theta'][j] <= a < net['theta'][j] + self.omega[j]: return ('W', j)
        return 'gap'

# ----------------------------------------------------------------------------------------------------
def rand_points(n, rng):
    """gen.rand_points, copied so octa.py is self-contained."""
    kind = rng.integers(4)
    if kind == 0: P = rng.normal(size=(n, 3))
    elif kind == 1: P = rng.normal(size=(n, 3)); P /= np.linalg.norm(P, axis=1, keepdims=True)
    elif kind == 2: P = rng.uniform(size=(n, 3))
    else: P = rng.normal(size=(n, 3)); P[0] *= np.exp(rng.uniform(0, 5))
    S = np.exp(rng.uniform(-4, 4, size=3)); S[0] = 1
    Qm = np.linalg.qr(rng.normal(size=(3, 3)))[0]
    return (P * S) @ Qm

def random_octahedra(rng, N):
    """yield (P, faces, adj) for N random octahedron-type polytopes."""
    cnt = 0
    while cnt < N:
        P = rand_points(6, rng)
        st = octa_structure(P)
        if st is None: continue
        cnt += 1
        yield P, st[0], st[1]

def all_apexes(P, faces, adj):
    for v in range(6): yield Octa(P, v, faces, adj)

def sharpest_apex(P, faces, adj):
    o = Octa(P, 0, faces, adj)
    v = max(range(6), key=lambda x: o.kappa[x])
    return Octa(P, v, faces, adj)

def hill_climb(score, P0, rng, steps=2000, step=0.3, keep_type=True):
    """Maximise score(P) (None = invalid) by random perturbation with adaptive step."""
    P = np.array(P0, float); best = score(P)
    if best is None: return P, None
    for t in range(steps):
        Q = P + rng.normal(size=P.shape) * step * np.linalg.norm(P, axis=1, keepdims=True).mean()
        if keep_type and octa_structure(Q) is None: continue
        sc = score(Q)
        if sc is not None and sc > best: P, best = Q, sc; step *= 1.2
        else: step *= 0.97
        if step < 1e-9: step = 0.3
    return P, best
