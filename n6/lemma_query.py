"""Focused exact polynomial queries for Lemma L and omitted Case-B regimes.

Curvature order uses complex products and branch signs, with no arccos or
floating approximation. Solver-reported UNSAT still lacks an independent proof.
"""
import argparse
import json
from pathlib import Path
import time
from n6.query import run_bounded,write_report


def formulation(target,hypothesis='H3R',hard_local=False):
    import networkx as nx
    import z3
    from n6.encoding import Counterexample
    from n6.curvature import angle_product,angle_le,face_angle,curvature_sum_lt_pi,curvature_sum_lt_angle,face_plus_curvature_lt_pi,sum_angles_lt_pi
    ce=Counterexample(nx.octahedral_graph(),prune_vertex_fans=True)
    v,w,u=0,5,1
    products={x:angle_product(ce.x,ce.faces,ce.h,x) for x in ce.g}
    assertions=list(ce.constraints)
    if hypothesis in ('H3','H3R'):
        assertions += [angle_le(products[v],products[x]) for x in ce.g if x!=v]
    if hypothesis=='H3R':
        assertions += [angle_le(products[u],products[x]) for x in ce.g[w] if x!=u]
    cuts={tuple(sorted((v,x))) for x in ce.g[v]}|{tuple(sorted((w,u)))}
    t=ce.dual.copy();t.remove_edges_from([(a,b) for a,b,d in ce.dual.edges(data=True) if d['primal'] in cuts])
    lookup={frozenset(f):i for i,f in enumerate(ce.faces)}
    nxt={}
    for f in ce.faces:
        if w in f:
            k=f.index(w);nxt[f[(k+1)%3]]=f[(k+2)%3]
    ring=[u]
    while len(ring)<4:ring.append(nxt[ring[-1]])
    V=[lookup[frozenset((v,ring[i],ring[(i+1)%4]))] for i in range(4)]
    W=[lookup[frozenset((w,ring[i],ring[(i+1)%4]))] for i in range(4)]
    def overlap(a,b):return ce.overlap(tuple(nx.shortest_path(t,a,b)))
    def angle(f,x):return face_angle(ce.x,ce.faces[f],ce.h[f],x)
    caseA=curvature_sum_lt_angle(products[ring[2]],products[ring[3]],angle(V[2],v))
    leftD=face_plus_curvature_lt_pi(angle(V[2],ring[2]),products[ring[2]])
    rightD=face_plus_curvature_lt_pi(angle(V[2],ring[3]),products[ring[3]])
    smallSW=sum_angles_lt_pi([angle(W[1],ring[2]),angle(W[2],ring[2]),
                              angle(W[2],ring[3]),angle(W[3],ring[3])])
    claims={
        'local_vv':overlap(V[0],V[3]),
        'local_vw':overlap(V[0],W[3]),
        'opposite':overlap(V[1],V[3]),
        'large_D':z3.And(z3.Not(caseA),z3.Or(z3.Not(leftD),z3.Not(rightD))),
        'caseB_small_D':z3.And(z3.Not(caseA),leftD,rightD,overlap(V[1],V[3])),
        'caseB_large_D':z3.And(z3.Not(caseA),z3.Or(z3.Not(leftD),z3.Not(rightD)),overlap(V[1],V[3])),
        # The base-cone partition leaves all small-SW cases, including large D.
        'caseB_small_SW':z3.And(smallSW,overlap(V[1],V[3])),
    }
    assertions.append(claims[target])
    if hard_local:assertions.append(curvature_sum_lt_pi(products[u],products[w]))
    return ce,assertions,dict(apex=v,antipode=w,slit_vertex=u,equator=ring,cuts=sorted(cuts),
                             local_pairs=[[V[0],V[3]],[V[0],W[3]],[V[3],W[0]]],opposite_pair=[V[1],V[3]])


def worker(job):
    import z3
    from n6.encoding import export_smt2
    z3.set_param('memory_max_size',job['memory_mb'])
    ce,assertions,geometry=formulation(job['target'],job['hypothesis'],job['hard_local'])
    auxiliary_count=0
    if job.get('lifted'):
        from n6.lift import arithmetic_lift
        assertions,auxiliaries=arithmetic_lift(assertions)
        auxiliary_count=len(auxiliaries)
    path=Path(job['output']);nodes=export_smt2(assertions,path.with_suffix('.smt2'))
    report={**job,'result':'exported','geometry':geometry,'assertions':len(assertions),
            'dag_nodes':nodes,'smt2_bytes':path.with_suffix('.smt2').stat().st_size,
            'independent_proof_certificate':False,'z3_version':z3.get_version_string(),
            'auxiliary_variables':auxiliary_count}
    write_report(path.with_suffix('.result.json'),report)
    if job['export_only']:return
    if job.get('lifted'):
        from n6.lift import lifted_solver
        solver=lifted_solver(job['solver_ms'])
    else:
        solver=z3.SolverFor('QF_NRA');solver.set(timeout=job['solver_ms'])
    start=time.monotonic()
    try:
        solver.add(*assertions);result=solver.check()
        report.update(result=str(result),solver_seconds=time.monotonic()-start)
        if result==z3.unknown:report['reason_unknown']=solver.reason_unknown()
        elif result==z3.sat:path.with_suffix('.model.txt').write_text(str(solver.model())+'\n')
        report['scope']={
            'unsat':'Solver-reported exclusion for this target and hypotheses; no independent proof certificate.',
            'sat':'Candidate realization satisfying this target; exact model extraction and geometric checking still required.',
            'unknown':'Unresolved; no mathematical conclusion.'}[str(result)]
    except z3.Z3Exception as e:report.update(result='solver_error',error=str(e),scope='Unresolved; no mathematical conclusion.')
    write_report(path.with_suffix('.result.json'),report)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--worker',type=Path,help=argparse.SUPPRESS)
    ap.add_argument('--target',choices=['local_vv','local_vw','opposite','large_D','caseB_small_D','caseB_large_D','caseB_small_SW'],default='local_vv')
    ap.add_argument('--hypothesis',choices=['none','H3','H3R'],default='H3R')
    ap.add_argument('--hard-local',action='store_true')
    ap.add_argument('--lifted',action='store_true',help='Keep expression DAGs as low-degree auxiliary equations')
    ap.add_argument('--solver-ms',type=int,default=600000);ap.add_argument('--wall-seconds',type=float,default=660)
    ap.add_argument('--memory-mb',type=int,default=1024);ap.add_argument('--export-only',action='store_true')
    ap.add_argument('--output',default='n6/results/lemma-query')
    args=ap.parse_args()
    if args.worker:worker(json.loads(args.worker.read_text()));return
    if min(args.solver_ms,args.wall_seconds,args.memory_mb)<=0:ap.error('limits must be positive')
    job=vars(args);job.pop('worker')
    print(json.dumps(run_bounded(job,worker_module='n6.lemma_query'),indent=2))


if __name__=='__main__':main()
