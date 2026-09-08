"""Exact small-polyhedron counterexample encoding and combinatorial census.

Requires networkx, sympy, z3-solver. All geometric constraints are polynomial.
Boundary contacts are allowed; positive-area overlap is forbidden.
No universal result is implied by a timeout, a model of a partial query, or census.
"""
from __future__ import annotations
import argparse, itertools, json, time
from pathlib import Path
import networkx as nx
import sympy as sp
import z3


def export_smt2(assertions,path):
    """Write the arithmetic DAG once, avoiding exponential pretty-printing."""
    names={}
    with Path(path).open('w') as out:
        out.write('(set-logic QF_NRA)\n')
        for assertion in assertions:
            stack=[(assertion,False)]
            while stack:
                term,ready=stack.pop();tid=term.get_id()
                if tid in names:continue
                children=term.children()
                if not children:
                    names[tid]=term.sexpr()
                    if term.decl().kind()==z3.Z3_OP_UNINTERPRETED:
                        out.write(f'(declare-fun {term.sexpr()} () {term.sort().sexpr()})\n')
                elif ready:
                    name=f'_term{tid}';names[tid]=name
                    op=term.decl().name()
                    out.write(f'(define-fun {name} () {term.sort().sexpr()} ({op} '+
                              ' '.join(names[c.get_id()] for c in children)+'))\n')
                else:
                    stack.append((term,True))
                    stack.extend((child,False) for child in reversed(children) if child.get_id() not in names)
            out.write(f'(assert {names[assertion.get_id()]})\n')
        out.write('(check-sat)\n')
    return len(names)


def faces_and_dual(g):
    ok, emb = nx.check_planarity(g)
    if not ok or nx.node_connectivity(g) < 3:
        raise ValueError('Expected a 3-connected planar graph')
    seen, faces = set(), []
    for a, b in emb.edges():
        if (a, b) not in seen:
            faces.append(tuple(emb.traverse_face(a, b, seen)))
    dual, incident = nx.Graph(), {}
    dual.add_nodes_from(range(len(faces)))
    for i, f in enumerate(faces):
        for a, b in zip(f, f[1:] + f[:1]):
            e = tuple(sorted((a,b)))
            if e in incident:
                dual.add_edge(incident[e], i, primal=e)
            else:
                incident[e] = i
    assert len(faces) == g.number_of_edges() - len(g) + 2
    return faces, dual


def atlas():
    for g in nx.graph_atlas_g():
        if len(g) < 4 or min(dict(g.degree()).values()) < 3:
            continue
        if nx.check_planarity(g)[0] and nx.node_connectivity(g) >= 3:
            yield g


def graph6(g):
    return nx.to_graph6_bytes(g, header=False).decode().strip()


def tau(g):
    L = nx.laplacian_matrix(g).toarray()
    return int(sp.Matrix(L[:-1, :-1]).det())


def spanning_trees(g):
    # At n <= 7 brute-force cut sets have at most binomial(15,6)=5005 cases.
    edges = list(g.edges())
    for es in itertools.combinations(edges, len(g)-1):
        t = nx.Graph()
        t.add_nodes_from(g)
        t.add_edges_from(es)
        if nx.is_tree(t):
            yield t


def dual_trees(g, dual):
    # Enumerating cuts in the primal is cheaper for many-faced polyhedra.
    for cut in spanning_trees(g):
        es = {tuple(sorted(e)) for e in cut.edges()}
        t = dual.copy()
        t.remove_edges_from([(a,b) for a,b,d in dual.edges(data=True) if d['primal'] in es])
        assert nx.is_tree(t)
        yield t


def tree_paths(t):
    for a,b in itertools.combinations(sorted(t),2):
        p = tuple(nx.shortest_path(t,a,b))
        if len(p) >= 3:  # Faces joined directly by a hinge cannot overlap.
            yield p


def census():
    rows=[]
    for g in atlas():
        fs,d=faces_and_dual(g)
        paths=set()
        count=0
        for t in dual_trees(g,d):
            count += 1
            paths.update(tree_paths(t))
        assert count == tau(g) == tau(d)
        rows.append(dict(graph6=graph6(g), vertices=len(g), edges=g.number_of_edges(),
                         faces=[list(f) for f in fs], degree_sequence=sorted(dict(g.degree()).values()),
                         cut_trees=count, distinct_nondirect_dual_paths=len(paths),
                         simplicial=all(len(f)==3 for f in fs),
                         universal_vertices=[v for v in g if g.degree(v)==len(g)-1],
                         dome_bases=[i for i,f in enumerate(fs) if d.degree(i)==len(fs)-1]))
    return rows


def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def cross(a,b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
def det2(a,b): return a[0]*b[1]-a[1]*b[0]


class Counterexample:
    """Exact, polynomial shared-face/path encoding for one combinatorial type.

    A face f is represented in 3D by its vertices x and oriented normal N_f.
    h_f > 0 and h_f^2 = N_f.N_f encode its normal length. An unfolded face
    uses homogeneous planar coordinates (Q_v,D), D>0. Thus no divisions or
    transcendental functions occur, and only 3n-7 + F real variables are used.
    """
    def __init__(self,g, *, prune_vertex_fans=False):
        if set(g) != set(range(len(g))):
            raise ValueError('Vertex labels must be consecutive integers starting at 0')
        self.g=g.copy()
        self.prune_vertex_fans=prune_vertex_fans
        self.faces,self.dual=faces_and_dual(g)
        self.x=[tuple(z3.Real(f'x{i}_{j}') for j in range(3)) for i in g]
        a,b,c=self.faces[0][:3]
        self.x[a]=(z3.RealVal(0),)*3
        self.x[b]=(z3.RealVal(1),z3.RealVal(0),z3.RealVal(0))
        self.x[c]=(z3.Real(f'x{c}_0'),z3.Real(f'x{c}_1'),z3.RealVal(0))
        self.constraints=[self.x[c][1]>0]
        self.N=[];self.h=[]
        for i,f in enumerate(self.faces):
            a,b,c=f[:3]
            N=cross(sub(self.x[b],self.x[a]),sub(self.x[c],self.x[a]))
            h=z3.Real(f'h{i}')
            self.N.append(N);self.h.append(h)
            self.constraints += [h>0,h*h==dot(N,N)]
            for v in g:
                s=dot(N,sub(self.x[v],self.x[a]))
                self.constraints.append(s==0 if v in f else s<0)
            if len(f)>3:
                # Each polygon edge supports a strictly convex, ordered facet.
                for u,v in zip(f,f[1:]+f[:1]):
                    for w in f:
                        if w not in (u,v):
                            self.constraints.append(dot(N,cross(sub(self.x[v],self.x[u]),sub(self.x[w],self.x[u])))>0)
        self.develop_cache={}
        self.overlap_cache={}
        self.asserted_paths=set()

    def develop(self,path):
        path=tuple(path)
        if path in self.develop_cache:
            return self.develop_cache[path]
        f=self.faces[path[-1]]; h=self.h[path[-1]]; N=self.N[path[-1]]
        if len(path)==1:
            a,b=f[:2]
            edge=sub(self.x[b],self.x[a])
            if len(f)==3:
                Q={a:(0,0),b:(dot(edge,edge),0),f[2]:(dot(edge,sub(self.x[f[2]],self.x[a])),h)}
                ans=(Q,z3.RealVal(1))
            else:
                Q={v:(h*dot(edge,sub(self.x[v],self.x[a])),
                      dot(N,cross(edge,sub(self.x[v],self.x[a])))) for v in f}
                ans=(Q,h)
        else:
            old,D=self.develop(path[:-1])
            shared=set(self.faces[path[-2]])&set(f)
            a,b=next((a,b) for a,b in zip(f,f[1:]+f[:1]) if a in shared and b in shared)
            edge=sub(self.x[b],self.x[a]); s=dot(edge,edge)
            U=sub(old[b],old[a]); JU=(-U[1],U[0])
            Q={}
            for v in f:
                V=sub(self.x[v],self.x[a]); d=dot(edge,V); k=dot(N,cross(edge,V))
                if len(f)==3:
                    # A cyclic change of triangle origin preserves its normal.
                    k=0 if v in (a,b) else h
                    Q[v]=tuple(s*old[a][j]+d*U[j]+k*JU[j] for j in range(2))
                else:
                    Q[v]=tuple(h*s*old[a][j]+h*d*U[j]+k*JU[j] for j in range(2))
            ans=(Q,D*s if len(f)==3 else D*h*s)
        self.develop_cache[path]=ans
        return ans

    def overlap(self,path):
        path=tuple(path)
        if path[0]>path[-1]:path=path[::-1]
        if len(path)<3:return z3.BoolVal(False)
        # This is a combinatorial common COPY: every face on the hinge
        # path contains the vertex. Coincident numerical coordinates alone
        # do not justify this lemma. Convexity makes the fan angle < 2*pi.
        if self.prune_vertex_fans and set.intersection(*(set(self.faces[f]) for f in path)):
            return z3.BoolVal(False)
        if path in self.overlap_cache:return self.overlap_cache[path]
        A,DA=self.develop(path[:1]);B,DB=self.develop(path)
        fa=self.faces[path[0]];fb=self.faces[path[-1]]
        tests=[]
        for X,DX,fx,Y,DY,fy in ((A,DA,fa,B,DB,fb),(B,DB,fb,A,DA,fa)):
            for u,v in zip(fx,fx[1:]+fx[:1]):
                edge=sub(X[v],X[u])
                tests.append(z3.Or(*[det2(edge,tuple(DX*Y[w][j]-DY*X[u][j] for j in range(2)))>0 for w in fy]))
        # Separating-axis theorem, with strict inequalities to allow contacts.
        ans=z3.And(*tests)
        self.overlap_cache[path]=ans
        return ans

    def bad_tree(self,t):
        return z3.Or(*[self.overlap(p) for p in tree_paths(t)])

    def add_tree(self,solver,t):
        # Tseitin Boolean sharing keeps shared path geometry out of duplicate
        # copies of different tree clauses. Variables remain existential.
        literals=[]
        for p in tree_paths(t):
            ov=self.overlap(p)
            if z3.is_false(ov):continue
            lit=z3.Bool('overlap_'+'_'.join(map(str,p)))
            if p not in self.asserted_paths:
                solver.add(lit==ov)
                self.asserted_paths.add(p)
            literals.append(lit)
        solver.add(z3.Or(*literals))

    def vertex_star_tree(self,v):
        t=self.dual.copy()
        t.remove_edges_from([(a,b) for a,b,d in t.edges(data=True) if v in d['primal']])
        assert nx.is_tree(t)
        return t


def benchmark(g,timeout_ms,output,limit):
    build_start=time.monotonic()
    ce=Counterexample(g)
    class Assertions:
        def __init__(self):self.items=[]
        def add(self,*items):self.items.extend(items)
    assertions=Assertions()
    assertions.add(*ce.constraints)
    stars=[v for v in g if g.degree(v)==len(g)-1]
    trees=([ce.vertex_star_tree(stars[0])] if stars else list(dual_trees(g,ce.dual)))
    if not stars:
        trees.sort(key=lambda t:(nx.diameter(t),tuple(sorted(t.edges()))))
    selected=trees[:limit] if limit else trees
    for i,t in enumerate(selected):
        ce.add_tree(assertions,t)
        if (i+1)%200==0:print(f'Encoded {i+1}/{len(selected)} trees',flush=True)
    path=Path(output)
    print('Exporting shared arithmetic DAG',flush=True)
    dag_nodes=export_smt2(assertions.items,path)
    build_seconds=time.monotonic()-build_start
    print(f'Checking {len(selected)} trees; {dag_nodes} DAG nodes',flush=True)
    t0=time.monotonic()
    # Export before submitting to SMT: native polynomial preprocessing can
    # be expensive and need not reliably obey the check() timeout.
    solver=z3.Solver();solver.set(timeout=timeout_ms)
    solver.add(*assertions.items)
    result=solver.check()
    report=dict(graph6=graph6(g),n=len(g),selected_trees=len(selected),all_trees=tau(g),
                full_tree_family=len(selected)==tau(g),shared_paths=len(ce.overlap_cache),
                essential_real_variables=3*len(g)-7+len(ce.faces),
                result=str(result),seconds=time.monotonic()-t0,
                reason_unknown=solver.reason_unknown() if result==z3.unknown else None,
                smt2_bytes=path.stat().st_size,z3_version=z3.get_version_string(),
                arithmetic_dag_nodes=dag_nodes,build_seconds=build_seconds)
    if result==z3.sat:
        report['scope']='SAT only certifies a counterexample if full_tree_family is true; otherwise a partial query.'
        path.with_suffix('.model.txt').write_text(str(solver.model()))
    elif result==z3.unsat:
        report['scope']='Solver reports universal coverage by selected trees; no independent proof certificate was generated.'
    else:
        report['scope']='Unresolved; timeout/unknown is not evidence of universal unfoldability.'
    path.with_suffix('.result.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    sp_=ap.add_subparsers(dest='command',required=True)
    c=sp_.add_parser('census');c.add_argument('--output',default='census.json')
    b=sp_.add_parser('benchmark');b.add_argument('graph6');b.add_argument('--timeout-ms',type=int,default=30000)
    b.add_argument('--output',default='query.smt2');b.add_argument('--trees',type=int,default=1,help='0 means all trees; default is only a solver calibration')
    args=ap.parse_args()
    if args.command=='census':
        rows=census();Path(args.output).write_text(json.dumps(rows,indent=2)+'\n')
        for n in range(4,8):
            rs=[r for r in rows if r['vertices']==n]
            print(json.dumps(dict(n=n,graphs=len(rs),trees=sum(r['cut_trees'] for r in rs),
                                  max_trees=max(r['cut_trees'] for r in rs),
                                  universal_vertex_types=sum(bool(r['universal_vertices']) for r in rs),
                                  unique_paths=sum(r['distinct_nondirect_dual_paths'] for r in rs))))
    else:
        print(json.dumps(benchmark(nx.from_graph6_bytes(args.graph6.encode()),args.timeout_ms,args.output,args.trees),indent=2))

if __name__=='__main__':main()
