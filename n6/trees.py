"""Finite cut-tree families on a surface with its original polygonal facets."""
from itertools import combinations,product
from n6.certify import edge,tree_path


def incidence(faces):
    result={}
    for i,f in enumerate(faces):
        for a,b in zip(f,f[1:]+f[:1]):result.setdefault(edge(a,b),[]).append(i)
    if any(len(x)!=2 for x in result.values()):raise ValueError('Nonclosed surface')
    return result


def connected(edges,n):
    seen={0}
    while True:
        new=seen|{b for a,b in edges if a in seen}|{a for a,b in edges if b in seen}
        if new==seen:return len(seen)==n
        seen=new


def tree_data(faces,cuts):
    inc=incidence(faces);cuts=set(map(tuple,cuts))
    hinges=[tuple(fs) for e,fs in inc.items() if e not in cuts]
    adj={i:[] for i in range(len(faces))}
    for a,b in hinges:adj[a].append(b);adj[b].append(a)
    pairs=[]
    for a,b in combinations(adj,2):
        path=tree_path(adj,a,b)
        if not set.intersection(*(set(faces[f]) for f in path)):pairs.append((a,b))
    return dict(cuts=sorted(cuts),hinges=hinges,pairs=pairs)


def all_trees(faces):
    inc=incidence(faces)
    return sorted((tree_data(faces,cuts) for cuts in combinations(sorted(inc),5) if connected(cuts,6)),
                  key=lambda t:(len(t['pairs']),t['cuts']))


def thesis_family(faces):
    """All cyclic three-arm cores, with the last triangle on any of its sides.

    For the octahedron there are eight roots, two assignments of the next
    three faces to distinct arms, and three placements of the last face: 48
    distinct trees. This is a candidate family, not a coverage theorem.
    """
    if len(faces)!=8 or any(len(f)!=3 for f in faces):
        raise ValueError('Thesis family requires triangular octahedral facets')
    inc=incidence(faces);adj={f:set() for f in range(8)}
    for a,b in inc.values():adj[a].add(b);adj[b].add(a)
    result={}
    for root in adj:
        first=adj[root]
        second=set().union(*(adj[a] for a in first))-{root}
        last=set(adj)-first-second-{root}
        if len(first)!=3 or len(second)!=3 or len(last)!=1:
            raise ValueError('Dual graph is not cubical')
        final=next(iter(last));middle=sorted(second)
        for parents in product(*(sorted(adj[b]&first) for b in middle)):
            if len(set(parents))!=3:continue
            core=[(root,a) for a in first]+list(zip(parents,middle))
            for parent in sorted(adj[final]):
                hinge_set={frozenset(e) for e in core+[(parent,final)]}
                cuts=tuple(sorted(e for e,fs in inc.items() if frozenset(fs) not in hinge_set))
                result[cuts]=tree_data(faces,cuts)
    return [result[k] for k in sorted(result)]


def degree_four_stars(faces):
    """Cut a degree-four star and one original edge to the remaining vertex."""
    inc=incidence(faces);adj={v:set() for v in range(6)};result=[]
    for a,b in inc:adj[a].add(b);adj[b].add(a)
    for v in adj:
        if len(adj[v])!=4:continue
        w=next(x for x in adj if x!=v and x not in adj[v])
        for u in sorted(adj[w]):
            data=tree_data(faces,{edge(v,x) for x in adj[v]}|{edge(w,u)})
            result.append({**data,'apex':v,'antipode':w,'slit_vertex':u})
    return result
