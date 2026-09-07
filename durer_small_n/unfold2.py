"""Edge unfoldings of convex polytopes with (possibly) non-triangular faces."""
import numpy as np, itertools
from scipy.spatial import ConvexHull

def poly_faces(P, tol=1e-7):
    h = ConvexHull(P)
    groups = []
    for s, eq in zip(h.simplices, h.equations):
        for g in groups:
            if np.linalg.norm(g['eq'] - eq) < tol: g['verts'] |= set(int(x) for x in s); break
        else:
            groups.append({'eq': eq.copy(), 'verts': set(int(x) for x in s)})
    faces = []
    for g in groups:
        nrm = g['eq'][:3]; vs = list(g['verts']); c = P[vs].mean(0)
        ex = P[vs[0]] - c; ex -= np.dot(ex, nrm) * nrm; ex /= np.linalg.norm(ex); ey = np.cross(nrm, ex)
        ang = [np.arctan2(np.dot(P[v] - c, ey), np.dot(P[v] - c, ex)) for v in vs]
        faces.append(tuple(v for _, v in sorted(zip(ang, vs))))  # CCW seen from outside
    return faces

def local_coords(P, faces):
    L = []
    for f in faces:
        a, b = P[f[0]], P[f[1]]; ex = b - a; ex /= np.linalg.norm(ex)
        n = np.cross(b - a, P[f[2]] - a); n /= np.linalg.norm(n); ey = np.cross(n, ex)
        L.append({v: np.array([np.dot(P[v] - a, ex), np.dot(P[v] - a, ey)]) for v in f})
    return L

def face_edges(f): return [tuple(sorted((f[i], f[(i + 1) % len(f)]))) for i in range(len(f))]

def dual_edges(faces):
    E = []
    for f, g in itertools.combinations(range(len(faces)), 2):
        s = set(face_edges(faces[f])) & set(face_edges(faces[g]))
        if len(s) == 1:
            (u, v), = s; E.append((f, g, u, v))
    return E

def spanning_trees(m, E):
    trees = []
    for comb in itertools.combinations(range(len(E)), m - 1):
        parent = list(range(m))
        def find(x):
            while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
            return x
        ok = True
        for ei in comb:
            a, b = find(E[ei][0]), find(E[ei][1])
            if a == b: ok = False; break
            parent[a] = b
        if ok: trees.append(comb)
    return trees

def unfold(faces, L, E, tree):
    m = len(faces); adj = [[] for _ in range(m)]
    for ei in tree:
        f, g, u, v = E[ei]; adj[f].append((g, u, v)); adj[g].append((f, u, v))
    pos = [None] * m; pos[0] = dict(L[0]); stack = [0]
    while stack:
        f = stack.pop()
        for g, u, v in adj[f]:
            if pos[g] is not None: continue
            A, B = pos[f][u], pos[f][v]; a, b = L[g][u], L[g][v]
            th = np.arctan2(*(B - A)[::-1]) - np.arctan2(*(b - a)[::-1]); c, s = np.cos(th), np.sin(th)
            R = np.array([[c, -s], [s, c]]); pos[g] = {w: R @ (L[g][w] - a) + A for w in L[g]}
            stack.append(g)
    return pos

def sat_pen(Q1, Q2):
    """penetration depth (<=0 means separated/touching) of two convex CCW polygons"""
    best = np.inf
    for Q in (Q1, Q2):
        for i in range(len(Q)):
            e = Q[(i + 1) % len(Q)] - Q[i]; nrm = np.array([-e[1], e[0]]) / np.linalg.norm(e)
            p1 = Q1 @ nrm; p2 = Q2 @ nrm
            best = min(best, min(p1.max(), p2.max()) - max(p1.min(), p2.min()))
    return best

def overlaps(faces, pos, eps):
    worst = 0.0
    for f, g in itertools.combinations(range(len(faces)), 2):
        shared = set(faces[f]) & set(faces[g])
        if any(np.linalg.norm(pos[f][w] - pos[g][w]) < eps for w in shared): continue
        Q1 = np.array([pos[f][w] for w in faces[f]]); Q2 = np.array([pos[g][w] for w in faces[g]])
        worst = max(worst, sat_pen(Q1, Q2))
    return worst

class Polytope:
    def __init__(self, P):
        self.P = np.asarray(P, float); self.faces = poly_faces(self.P)
        self.L = local_coords(self.P, self.faces); self.E = dual_edges(self.faces)
        self.scale = np.max(np.linalg.norm(self.P[:, None] - self.P[None], axis=-1)); self.eps = 1e-9 * self.scale
        self.edges = sorted({(u, v) for _, _, u, v in self.E}); self.deg = {}
        for u, v in self.edges: self.deg[u] = self.deg.get(u, 0) + 1; self.deg[v] = self.deg.get(v, 0) + 1
    def trees(self):
        if not hasattr(self, '_trees'): self._trees = spanning_trees(len(self.faces), self.E)
        return self._trees
    def cut_set(self, tree):
        hinges = {(self.E[ei][2], self.E[ei][3]) for ei in tree}
        return [e for e in self.edges if e not in hinges]
    def penetrations(self):
        return np.array([overlaps(self.faces, unfold(self.faces, self.L, self.E, t), self.eps) for t in self.trees()])
