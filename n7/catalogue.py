"""Seven-vertex graph census and geometry-independent pair reductions.

Only n7 files are written. No n6 proof implementation is imported.
"""
from __future__ import annotations
import argparse
import itertools as it
import json
from collections import Counter
from pathlib import Path
import networkx as nx

ROOT = Path(__file__).resolve().parent

def edge(a, b):
    return tuple(sorted((a, b)))

def face_edges(f):
    return {edge(f[i], f[(i+1) % len(f)]) for i in range(len(f))}

def canonical_cycle(f):
    f = tuple(f)
    choices = []
    for seq in (f, tuple(reversed(f))):
        choices.extend(seq[k:]+seq[:k] for k in range(len(seq)))
    return min(choices)

def facets(g):
    planar, embedding = nx.check_planarity(g)
    if not planar:
        raise ValueError('Nonplanar graph')
    seen, fs = set(), []
    for u, v in embedding.edges():
        if (u, v) not in seen:
            fs.append(canonical_cycle(embedding.traverse_face(u, v, seen)))
    return sorted(fs)

def dual_data(g, fs):
    ef = {edge(*e): [] for e in g.edges()}
    for i, f in enumerate(fs):
        for e in face_edges(f):
            ef[e].append(i)
    if any(len(ids) != 2 for ids in ef.values()):
        raise ValueError('Every original edge must bound exactly two facets')
    return ef

def is_tree_edges(n, edges):
    if len(edges) != n-1:
        return False
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    for a,b in edges:
        a,b = find(a),find(b)
        if a == b:
            return False
        parent[a] = b
    return True

def original_cut_trees(g):
    for cut in it.combinations(sorted(edge(*e) for e in g.edges()), len(g)-1):
        if is_tree_edges(len(g), cut):
            yield cut

def cofacial_sources(g, fs):
    return [v for v in g if set().union(*(set(f) for f in fs if v in f)) == set(g)]

def cofacial_candidates(g, fs):
    """Keep each incident polygon on exactly one boundary hinge away from v."""
    candidates = []
    for v in cofacial_sources(g, fs):
        incident = [i for i, f in enumerate(fs) if v in f]
        chains = [sorted(e for e in face_edges(fs[i]) if v not in e) for i in incident]
        radial = {edge(v,u) for u in g[v]}
        changed = [i for i in incident if len(fs[i])>3]
        for hinges in it.product(*chains):
            cut = set(radial)
            for chain, hinge in zip(chains, hinges):
                cut.update(e for e in chain if e != hinge)
            if not is_tree_edges(len(g), sorted(cut)):
                raise AssertionError('Proposed cofacial replacement is not a tree')
            candidates.append({'source': v, 'changed_faces': changed,
                               'cut': sorted(cut), 'retained_hinges': list(hinges)})
    return candidates

def pair_audit(g, fs, cut, core=None):
    cut = {edge(*e) for e in cut}
    if not cut <= {edge(*e) for e in g.edges()} or not is_tree_edges(len(g), sorted(cut)):
        raise ValueError('Invalid original cut tree')
    if core:
        v = core.get('source')
        expected = [i for i, f in enumerate(fs) if v in f and len(f)>3]
        if v not in cofacial_sources(g, fs) or core.get('changed_faces') != expected:
            raise ValueError('Invalid cofacial source or changed-face list')
        permitted = {tuple(c['cut']) for c in cofacial_candidates(g, fs) if c['source']==v}
        if tuple(sorted(cut)) not in permitted:
            raise ValueError('Cut is not a cofacial replacement at this source')
    ef = dual_data(g, fs)
    adj = [[] for _ in fs]
    for e, (a,b) in ef.items():
        if e not in cut:
            adj[a].append(b); adj[b].append(a)
    if sum(map(len,adj))//2 != len(fs)-1:
        raise AssertionError('Dual edge count')
    safe, unresolved = [], []
    fsets = list(map(set,fs))
    changed = set(core['changed_faces']) if core else None
    for start in range(len(fs)):
        paths = {start: [start]}; todo=[start]
        for cur in todo:
            for nxt in adj[cur]:
                if nxt not in paths:
                    paths[nxt]=paths[cur]+[nxt]; todo.append(nxt)
        if len(paths) != len(fs):
            raise AssertionError('Disconnected uncut dual')
        for end in range(start+1,len(fs)):
            p=paths[end]; common=set.intersection(*(fsets[i] for i in p))
            proof=None
            if common:
                proof={'lemma':'vertex_fan', 'vertex':min(common)}
            elif len(p)<=3:
                proof={'lemma':'face_neighborhood', 'base':p[1]}
            elif core and start not in changed and end not in changed:
                proof={'lemma':'cofacial_core', 'source':core['source']}
            row={'faces':[start,end], 'path':p}
            if proof:
                safe.append(dict(row,**proof))
            else:
                unresolved.append(row)
    return {'safe_count':len(safe), 'total_pairs':len(fs)*(len(fs)-1)//2,
            'safe':safe, 'unresolved':unresolved}

def census(scan_trees=False):
    rows=[]
    for aid,g in enumerate(nx.graph_atlas_g()):
        if len(g)!=7 or min(dict(g.degree()).values())<3:
            continue
        planar,_=nx.check_planarity(g)
        if not planar or nx.node_connectivity(g)<3:
            continue
        fs=facets(g); ef=dual_data(g,fs)
        dome=[i for i in range(len(fs)) if all(i==j or any(set(ids)=={i,j} for ids in ef.values()) for j in range(len(fs)))]
        universal=[v for v,d in g.degree() if d==6]
        row={'id':f'N7-A{aid}', 'atlas_index':aid,
             'graph6':nx.to_graph6_bytes(g,header=False).decode().strip(),
             'edges':sorted(edge(*e) for e in g.edges()),'facets':fs,
             'edge_count':g.number_of_edges(),'face_count':len(fs),
             'degrees':sorted((d for _,d in g.degree()),reverse=True),
             'face_sizes':sorted(map(len,fs)), 'universal_vertices':universal,'dome_bases':dome,
             'cofacial_sources':cofacial_sources(g,fs),
             'degree_five_cofacial_sources':[v for v in cofacial_sources(g,fs) if g.degree(v)==5],
             'simplicial':all(len(f)==3 for f in fs),
             'status':'solved' if universal or dome else 'open',
             'theorem':'edge_star' if universal else 'dome' if dome else None}
        candidates=[]
        for cand in cofacial_candidates(g,fs):
            audit=pair_audit(g,fs,cand['cut'],cand)
            candidates.append(dict(cand,audit=audit))
        row['cofacial_candidates']=sorted(candidates,key=lambda c:(len(c['audit']['unresolved']),c['source'],c['cut']))
        if scan_trees:
            best=None; count=0; structural_solutions=0
            for cut in original_cut_trees(g):
                count+=1
                audit=pair_audit(g,fs,cut)
                score=len(audit['unresolved'])
                if score==0: structural_solutions+=1
                if best is None or score < len(best['audit']['unresolved']):
                    best={'cut':cut,'audit':audit}
            row['all_tree_scan']={'count':count,'structural_solutions':structural_solutions,'best':best}
            if structural_solutions and row['status']=='open':
                row['status']='solved';row['theorem']='structural_pairs'
        if row['cofacial_candidates'] and not row['cofacial_candidates'][0]['audit']['unresolved'] and row['status']=='open':
            row['status']='solved';row['theorem']='cofacial_core'
        rows.append(row)
    rows.sort(key=lambda r:(r['edge_count'],r['atlas_index']))
    return {'schema':1,'scope':'All unlabelled simple 3-connected planar graphs on seven vertices. Combinatorial census, not numerical realization sampling.',
            'dependencies':{'networkx':nx.__version__, 'n6_code_imported':False, 'geometric_formal_verification':False},
            'counts':dict(Counter(r['status'] for r in rows)),
            'edge_histogram':dict(Counter(r['edge_count'] for r in rows)), 'graphs':rows}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--scan-trees',action='store_true');p.add_argument('--output',type=Path,default=ROOT/'results/catalogue.json');args=p.parse_args()
    data=census(args.scan_trees);args.output.write_text(json.dumps(data,indent=2)+'\n')
    print('Graphs:',len(data['graphs']), 'Status:',data['counts'])
    for r in data['graphs']:
        c=r['cofacial_candidates'];best=r.get('all_tree_scan',{}).get('best')
        print(r['id'],r['status'],r['theorem'],'cofacial',len(c),'best cofacial residual',len(c[0]['audit']['unresolved']) if c else '-', 'best structural residual',len(best['audit']['unresolved']) if best else '-')
