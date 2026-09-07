import networkx as nx, itertools
n=6
allE=list(itertools.combinations(range(n),2))
reps=[]
for mask in range(1<<len(allE)):
    E=[allE[i] for i in range(len(allE)) if mask>>i&1]
    if not (3*n-6>=len(E)>=3*n//2): continue
    G=nx.Graph(E); G.add_nodes_from(range(n))
    if min(dict(G.degree()).values())<3: continue
    if not nx.is_planar(G) or nx.node_connectivity(G)<3: continue
    if any(nx.is_isomorphic(G,H) for H in reps): continue
    reps.append(G)
print(len(reps),"combinatorial types with",n,"vertices")
for G in reps:
    deg=sorted(dict(G.degree()).values(),reverse=True)
    F=2-n+G.number_of_edges()
    # faces via planar embedding
    _,emb=nx.check_planarity(G); faces=[]; seen=set()
    for u,v in emb.edges():
        if (u,v) in seen: continue
        f=emb.traverse_face(u,v,mark_half_edges=seen); faces.append(tuple(f))
    fs=sorted(len(f) for f in faces)
    dome=any(all(len(set(f)&set(g))==2 or f==g for g in faces) for f in faces)
    print(" E=%d F=%d degrees=%s face sizes=%s maxdeg=%d dome=%s"%(G.number_of_edges(),F,deg,fs,deg[0],dome))
