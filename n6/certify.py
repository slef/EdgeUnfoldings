"""Generate/check rational interval certificates for boxes of convex octahedra.

The checker uses the standard library only, and does not trust the generator,
NumPy, Qhull, Z3, or reported margins. It verifies all original facets and all
28 face pairs. A box is partial coverage of metric space, never the n=6 theorem.
"""
import argparse
import itertools
import json
from pathlib import Path
from n6.intervals import I, sub, dot, norm2, cross, det


def require(ok, message):
    if not ok:
        raise ValueError(message)


def edge(a, b):
    return tuple(sorted((a, b)))


def tree_path(adj, a, b):
    todo = [(a, [a])]
    seen = {a}
    for v, path in todo:
        if v == b:
            return path
        for w in adj[v]:
            if w not in seen:
                seen.add(w)
                todo.append((w, path + [w]))
    raise ValueError('Disconnected hinge graph')


class Geometry:
    def __init__(self, spec):
        require(spec.get('schema') == 'n6-octahedron-box-v1', 'Unknown schema')
        self.faces = fs = [tuple(f) for f in spec['faces']]
        raw = spec['coordinate_box']
        require(len(raw) == 6 and all(len(p) == 3 for p in raw), 'Expected six 3D points')
        self.p = p = [tuple(I(*q) for q in pt) for pt in raw]
        require(len(fs) == 8 and len(set(map(frozenset, fs))) == 8, 'Expected eight distinct faces')
        require(all(len(f) == 3 and len(set(f)) == 3 and set(f) <= set(range(6)) for f in fs), 'Invalid triangle')
        inc = {}
        directed = set()
        for i, f in enumerate(fs):
            for a, b in zip(f, f[1:] + f[:1]):
                require((a,b) not in directed, 'Inconsistent facet orientation')
                directed.add((a,b))
                inc.setdefault(edge(a,b), []).append(i)
        require(len(inc) == 12 and all(len(v) == 2 for v in inc.values()), 'Not a closed octahedral surface')
        require(all((b,a) in directed for a,b in directed), 'Unpaired oriented edge')
        require(all(sum(v in e for e in inc) == 4 for v in range(6)), 'Not the octahedral graph')
        self.h = []
        self.support_bounds = []
        for f in fs:
            a, b, c = f
            normal = cross(sub(p[b],p[a]), sub(p[c],p[a]))
            h2 = norm2(normal)
            require(h2.lo > 0, 'Cannot certify positive facet area')
            self.h.append(h2.sqrt())
            for v in set(range(6)) - set(f):
                support = dot(normal, sub(p[v], p[a]))
                require(support.hi < 0, 'Cannot certify strict convexity throughout box')
                self.support_bounds.append(support)
        cuts_raw = spec['cut_edges']
        cuts = {edge(*e) for e in cuts_raw}
        require(len(cuts) == len(cuts_raw) == 5 and cuts <= set(inc), 'Invalid cut set')
        cadj = {v: [] for v in range(6)}
        for a,b in cuts:
            cadj[a].append(b); cadj[b].append(a)
        for v in range(6):
            tree_path(cadj, 0, v)  # Connected + 5 edges => spanning tree.
        self.adj = adj = {i: [] for i in range(8)}
        for e, (a,b) in inc.items():
            if e not in cuts:
                adj[a].append(b); adj[b].append(a)
        require(sum(map(len, adj.values())) == 14, 'Wrong number of hinges')
        for f in range(8):
            tree_path(adj, 0, f)
        self.cache = {}

    def develop(self, path):
        """True planar coordinates; independent interval implementation of isometry."""
        path = tuple(path)
        if path in self.cache:
            return self.cache[path]
        f = self.faces[path[-1]]
        if len(path) == 1:
            a, b, c = f
            e = sub(self.p[b], self.p[a]); ell = norm2(e).sqrt()
            q = {a: (I(0), I(0)), b: (ell, I(0)),
                 c: (dot(e, sub(self.p[c], self.p[a])) / ell, self.h[path[-1]] / ell)}
        else:
            require(path[-1] in self.adj[path[-2]], 'Path uses a cut edge')
            old = self.develop(path[:-1])
            shared = set(f) & set(self.faces[path[-2]])
            a,b = next((a,b) for a,b in zip(f,f[1:]+f[:1]) if {a,b} == shared)
            c = next(v for v in f if v not in shared)
            e = sub(self.p[b], self.p[a]); s = norm2(e)
            U = sub(old[b],old[a]); JU = (-U[1],U[0])
            d = dot(e,sub(self.p[c],self.p[a]))
            q = {a: old[a], b: old[b], c: tuple(old[a][j] + (d*U[j] + self.h[path[-1]]*JU[j])/s for j in range(2))}
        self.cache[path] = q
        return q

    def pair_geometry(self, a, b):
        path = tree_path(self.adj, a, b)
        return path, self.develop(path[:1]), self.develop(path)

    def separating_bounds(self, a, b, owner, e):
        _, A, B = self.pair_geometry(a,b)
        require(owner in (a,b), 'Separator owner is not a pair face')
        X, Y = (A,B) if owner == a else (B,A)
        f = self.faces[owner]
        require(tuple(e) in list(zip(f,f[1:]+f[:1])), 'Separator is not an oriented face edge')
        u,v = e
        return [det(sub(X[v],X[u]),sub(q,X[u])) for q in Y.values()]


def make_certificate(spec):
    g = Geometry(spec)
    witnesses = []
    for a,b in itertools.combinations(range(8),2):
        path = tree_path(g.adj,a,b)
        common = set.intersection(*(set(g.faces[f]) for f in path))
        if common:
            witnesses.append({'faces':[a,b], 'kind':'vertex_fan', 'vertex':min(common)})
            continue
        found = None
        for owner in (a,b):
            f = g.faces[owner]
            for e in zip(f,f[1:]+f[:1]):
                bounds = g.separating_bounds(a,b,owner,e)
                if all(q.hi <= 0 for q in bounds):
                    found = {'faces':[a,b], 'kind':'separating_edge', 'owner':owner, 'edge':list(e)}
                    break
            if found:
                break
        require(found is not None, f'Pair {a,b} unresolved; no certificate produced')
        witnesses.append(found)
    return {**spec, 'pair_witnesses':witnesses}


def verify(cert):
    from n6.intervals import BITS
    g = Geometry(cert)
    remaining = set(itertools.combinations(range(8),2))
    counts = {'vertex_fan':0, 'separating_edge':0}
    for w in cert['pair_witnesses']:
        pair = tuple(w['faces'])
        require(pair in remaining, 'Repeated or invalid face pair')
        remaining.remove(pair)
        a,b = pair
        if w['kind'] == 'vertex_fan':
            path = tree_path(g.adj,a,b)
            require(all(w['vertex'] in g.faces[f] for f in path), 'Not the same uncut vertex copy')
        elif w['kind'] == 'separating_edge':
            bounds = g.separating_bounds(a,b,w['owner'],w['edge'])
            require(all(q.hi <= 0 for q in bounds), f'Separator does not certify pair {pair}')
        else:
            raise ValueError('Unknown witness kind')
        counts[w['kind']] += 1
    require(not remaining, 'Missing face pairs')
    return {'result':'verified', 'scope':'Every coordinate tuple in the explicit box; not all octahedra',
            'arithmetic':f'outward dyadic rational intervals, {BITS} fractional bits', 'pairs':counts,
            'strict_facet_supports':len(g.support_bounds)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action', choices=['generate','verify'])
    ap.add_argument('input', type=Path)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    spec = json.loads(args.input.read_text())
    if args.action == 'generate':
        ap.error('--output is required') if args.output is None else None
        spec = make_certificate(spec)
        report = verify(spec)
        args.output.write_text(json.dumps(spec,indent=2)+'\n')
    else:
        report = verify(spec)
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
