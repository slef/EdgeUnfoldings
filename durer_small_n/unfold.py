import numpy as np, itertools
from scipy.spatial import ConvexHull

def hull_faces(P):
    """Faces of the (assumed simplicial) convex hull, each CCW seen from outside."""
    h = ConvexHull(P)
    faces = []
    for s, eq in zip(h.simplices, h.equations):
        a, b, c = P[s]
        if np.dot(np.cross(b - a, c - a), eq[:3]) < 0:
            s = s[[0, 2, 1]]
        faces.append(tuple(int(x) for x in s))
    return faces

def local_coords(P, faces):
    """2D isometric copy of each face, CCW."""
    L = []
    for (i, j, k) in faces:
        a, b, c = P[i], P[j], P[k]
        ex = b - a; lx = np.linalg.norm(ex); ex /= lx
        n = np.cross(b - a, c - a); n /= np.linalg.norm(n)
        ey = np.cross(n, ex)
        L.append({i: np.array([0.0, 0.0]),
                  j: np.array([lx, 0.0]),
                  k: np.array([np.dot(c - a, ex), np.dot(c - a, ey)])})
    return L

def dual_edges(faces):
    """(f, g, u, v): faces f,g share edge {u,v}."""
    E = []
    for f, g in itertools.combinations(range(len(faces)), 2):
        s = set(faces[f]) & set(faces[g])
        if len(s) == 2:
            u, v = sorted(s)
            E.append((f, g, u, v))
    return E

def spanning_trees(m, E):
    """All spanning trees of the dual graph (m nodes, edge list E) as tuples of edge indices."""
    trees = []
    for comb in itertools.combinations(range(len(E)), m - 1):
        parent = list(range(m))
        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]; x = parent[x]
            return x
        ok = True
        for ei in comb:
            a, b = find(E[ei][0]), find(E[ei][1])
            if a == b: ok = False; break
            parent[a] = b
        if ok: trees.append(comb)
    return trees

def unfold(faces, L, E, tree):
    """Place faces in the plane along the dual tree. Returns pos[f] = {vertex: xy}."""
    m = len(faces)
    adj = [[] for _ in range(m)]
    for ei in tree:
        f, g, u, v = E[ei]
        adj[f].append((g, u, v)); adj[g].append((f, u, v))
    pos = [None] * m
    pos[0] = dict(L[0])
    stack = [0]
    while stack:
        f = stack.pop()
        for g, u, v in adj[f]:
            if pos[g] is not None: continue
            A, B = pos[f][u], pos[f][v]
            a, b = L[g][u], L[g][v]
            th = np.arctan2(*(B - A)[::-1]) - np.arctan2(*(b - a)[::-1])
            c, s = np.cos(th), np.sin(th)
            R = np.array([[c, -s], [s, c]])
            pos[g] = {w: R @ (L[g][w] - a) + A for w in L[g]}
            stack.append(g)
    return pos

def overlaps(faces, pos, eps):
    """Max penetration depth over all pairs of faces that do not share a net vertex.
    Returns 0.0 if the net is simple (touching allowed)."""
    m = len(faces)
    tri = np.array([[pos[f][w] for w in faces[f]] for f in range(m)])  # m x 3 x 2
    pairs = []
    for f, g in itertools.combinations(range(m), 2):
        shared = set(faces[f]) & set(faces[g])
        # faces sharing a net-vertex copy lie in disjoint wedges at it -> cannot overlap
        if any(np.linalg.norm(pos[f][w] - pos[g][w]) < eps for w in shared):
            continue
        pairs.append((f, g))
    if not pairs: return 0.0
    pairs = np.array(pairs)
    T1, T2 = tri[pairs[:, 0]], tri[pairs[:, 1]]          # k x 3 x 2
    def axes(T):
        e = np.roll(T, -1, axis=1) - T                    # k x 3 x 2
        n = np.stack([-e[..., 1], e[..., 0]], axis=-1)
        return n / (np.linalg.norm(n, axis=-1, keepdims=True) + 1e-300)
    N = np.concatenate([axes(T1), axes(T2)], axis=1)      # k x 6 x 2
    p1 = np.einsum('kai,kvi->kav', N, T1)                 # k x 6 x 3
    p2 = np.einsum('kai,kvi->kav', N, T2)
    ov = np.minimum(p1.max(-1), p2.max(-1)) - np.maximum(p1.min(-1), p2.min(-1))  # k x 6
    pen = ov.min(-1)                                      # separating axis => <= 0
    return float(max(0.0, pen.max()))

class Polytope:
    def __init__(self, P):
        self.P = np.asarray(P, float)
        self.faces = hull_faces(self.P)
        self.L = local_coords(self.P, self.faces)
        self.E = dual_edges(self.faces)
        self.scale = np.max(np.linalg.norm(self.P[:, None] - self.P[None], axis=-1))
        self.eps = 1e-9 * self.scale
        self.edges = sorted({(u, v) for _, _, u, v in self.E})
        self.deg = {}
        for u, v in self.edges:
            self.deg[u] = self.deg.get(u, 0) + 1; self.deg[v] = self.deg.get(v, 0) + 1

    def trees(self):
        if not hasattr(self, '_trees'):
            self._trees = spanning_trees(len(self.faces), self.E)
        return self._trees

    def cut_set(self, tree):
        hinges = {(self.E[ei][2], self.E[ei][3]) for ei in tree}
        return [e for e in self.edges if e not in hinges]

    def penetrations(self):
        """penetration depth of every unfolding (0 = simple net)."""
        return np.array([overlaps(self.faces, unfold(self.faces, self.L, self.E, t), self.eps)
                         for t in self.trees()])

    def good_trees(self):
        pen = self.penetrations()
        return [t for t, p in zip(self.trees(), pen) if p <= 0.0]
