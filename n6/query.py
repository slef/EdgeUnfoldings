"""Export and run exact counterexample queries with a hard subprocess deadline.

Example: python -m n6.query --family nearstar --output n6/results/nearstar
UNSAT is a solver result, not an independently checked proof certificate.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time


def nearstar_trees(ce):
    import networkx as nx
    g = ce.g
    if len(g) != 6 or any(g.degree(v) != 4 for v in g):
        raise ValueError('nearstar requires the octahedral graph')
    for v in g:
        w = next(x for x in g if x != v and not g.has_edge(v,x))
        for u in sorted(g[w]):
            cut = {tuple(sorted((v,x))) for x in g[v]} | {tuple(sorted((w,u)))}
            t = ce.dual.copy()
            t.remove_edges_from([(a,b) for a,b,d in t.edges(data=True) if d['primal'] in cut])
            if not nx.is_tree(t):
                raise ValueError('Invalid near-star tree')
            yield t


def write_report(path, data):
    temp = path.with_suffix('.tmp')
    temp.write_text(json.dumps(data,indent=2)+'\n')
    temp.replace(path)


def worker(job):
    import networkx as nx
    import z3
    from n6.encoding import Counterexample, dual_trees, export_smt2, graph6, tau
    z3.set_param('memory_max_size',job['memory_mb'])
    g = nx.from_graph6_bytes(job['graph6'].encode()) if job['graph6'] else nx.octahedral_graph()
    ce = Counterexample(g, prune_vertex_fans=not job['no_prune'])
    if job['family'] == 'nearstar':
        trees = list(nearstar_trees(ce))
    elif job['family'] == 'stars':
        trees = [ce.vertex_star_tree(v) for v in g if g.degree(v) == len(g)-1]
    else:
        trees = list(dual_trees(g,ce.dual))
    if job['trees']:
        trees = trees[:job['trees']]
    if not trees:
        raise ValueError('Empty tree family')
    class Assertions:
        def __init__(self): self.items = list(ce.constraints)
        def add(self,*items): self.items.extend(items)
    assertions = Assertions()
    for t in trees:
        ce.add_tree(assertions,t)
    path = Path(job['output'])
    nodes = export_smt2(assertions.items,path.with_suffix('.smt2'))
    report = {**job, 'graph6':graph6(g), 'result':'exported', 'selected_trees':len(trees),
              'all_trees':tau(g), 'full_tree_family':len(trees)==tau(g),
              'shared_paths':len(ce.overlap_cache), 'assertions':len(assertions.items),
              'dag_nodes':nodes, 'smt2_bytes':path.with_suffix('.smt2').stat().st_size,
              'z3_version':z3.get_version_string(), 'independent_proof_certificate':False}
    result_path = path.with_suffix('.result.json')
    write_report(result_path, report)
    if job['export_only']:
        return
    s = z3.SolverFor('QF_NRA')
    s.set(timeout=job['solver_ms'])
    t0 = time.monotonic()
    try:
        s.add(*assertions.items)
        result = s.check()
        report.update(result=str(result),solver_seconds=time.monotonic()-t0)
        if result == z3.unknown:
            report['reason_unknown'] = s.reason_unknown()
        elif result == z3.sat:
            path.with_suffix('.model.txt').write_text(str(s.model())+'\n')
        report['scope'] = {
            'unsat':'Solver-reported coverage by this tree family; encoding and solver are trusted, no independent certificate.',
            'sat':'Candidate failure of selected trees; a Durer counterexample requires all trees and exact model verification.',
            'unknown':'Unresolved; no mathematical conclusion.'}[str(result)]
    except z3.Z3Exception as e:
        report.update(result='solver_error',error=str(e),scope='Unresolved; no mathematical conclusion.')
    write_report(result_path,report)


def run_bounded(job):
    path = Path(job['output']).resolve()
    path.parent.mkdir(parents=True,exist_ok=True)
    job = {**job, 'output':str(path)}
    jobpath = path.with_suffix('.job.json')
    jobpath.write_text(json.dumps(job,indent=2)+'\n')
    resultpath = path.with_suffix('.result.json')
    write_report(resultpath, {**job,'result':'building','independent_proof_certificate':False})
    start = time.monotonic()
    with path.with_suffix('.worker.log').open('w') as log:
        proc = subprocess.Popen([sys.executable,'-m','n6.query','--worker',str(jobpath)],stdout=log,stderr=subprocess.STDOUT)
        timed_out = False
        try:
            proc.wait(timeout=job['wall_seconds'])
        except subprocess.TimeoutExpired:
            timed_out = True
            proc.kill()
            proc.wait()
    report = json.loads(resultpath.read_text())
    if timed_out or proc.returncode:
        report['stage_before_termination'] = report['result']
        report.update(result='wall_timeout' if timed_out else 'process_error',
                      scope='Unresolved; no mathematical conclusion.')
    report.update(wall_seconds_observed=time.monotonic()-start,process_returncode=proc.returncode)
    write_report(resultpath,report)
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--worker',type=Path,help=argparse.SUPPRESS)
    ap.add_argument('--graph6',default=None)
    ap.add_argument('--family',choices=['nearstar','stars','all'],default='nearstar')
    ap.add_argument('--trees',type=int,default=0,help='0 includes the whole selected family')
    ap.add_argument('--solver-ms',type=int,default=15000)
    ap.add_argument('--wall-seconds',type=float,default=30)
    ap.add_argument('--memory-mb',type=int,default=1024)
    ap.add_argument('--output',default='n6/results/nearstar')
    ap.add_argument('--no-prune',action='store_true')
    ap.add_argument('--export-only',action='store_true')
    args = ap.parse_args()
    if args.worker:
        worker(json.loads(args.worker.read_text())); return
    if args.trees < 0 or min(args.solver_ms,args.wall_seconds,args.memory_mb) <= 0:
        ap.error('Limits must be positive and --trees nonnegative')
    job = vars(args); job.pop('worker')
    print(json.dumps(run_bounded(job),indent=2))


if __name__ == '__main__':
    main()
