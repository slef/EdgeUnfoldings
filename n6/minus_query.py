"""Exact polynomial counterexample queries for the two-tree conjecture.

The coordinate chart covers every labelled convex realization up to a rigid
motion and scaling. It does not bound thickness, angles, or coordinates.
Solver UNSAT is a report, not an independently replayable proof certificate.
"""
import argparse
import json
from pathlib import Path
import time
from n6.families import MINUS_FACES as FACES
from n6.minus_pair import paired_trees,obligations
from n6.direct_query import d2,sub,dot,determinant,interior_overlap
from n6.query import run_bounded,write_report


def spatial_geometry():
    import z3
    c,d,e,f,r,s,h,t,k,l=z3.Reals('c d e f r s h t k l')
    p=[(0,0,0),(1,0,0),(c,-d,0),(e,f,0),(r,s,-h),(t,k,-l)]
    assertions=[d>0,f>0,h>0,l>0,c*f+d*e>0,c*f+d*e<d+f]
    for face in FACES:
        a,b,c=face[:3];u=sub(p[b],p[a]);v=sub(p[c],p[a])
        normal=(u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0])
        assertions.extend(dot(normal,sub(p[w],p[a]))<0 for w in range(6) if w not in face)
    return p,assertions


def develop(p,tree):
    """Keep the original quadrilateral whole; only the other faces are triangles."""
    import z3
    placed={0:{v:p[v][:2] for v in FACES[0]}};assertions=[];order=[0]
    adj={i:[] for i in range(7)}
    for a,b in tree['hinges']:adj[a].append(b);adj[b].append(a)
    for parent in order:
        for child in adj[parent]:
            if child in placed:continue
            face=FACES[child]
            a,b=next((a,b) for a,b in zip(face,face[1:]+face[:1]) if a in placed[parent] and b in placed[parent])
            c=next(v for v in face if v not in (a,b))
            q={a:placed[parent][a],b:placed[parent][b],c:(z3.FreshReal('net_x'),z3.FreshReal('net_y'))}
            assertions.extend([d2(q[a],q[c])==d2(p[a],p[c]),d2(q[b],q[c])==d2(p[b],p[c]),
                               determinant(sub(q[b],q[a]),sub(q[c],q[a]))>0])
            placed[child]=q;order.append(child)
    return placed,assertions


def formulation(class_id):
    orbits=obligations()['orbits']
    if not 1<=class_id<=len(orbits):raise ValueError('Class ID must be between 1 and 28')
    p,assertions=spatial_geometry();pairs=orbits[class_id-1][0]
    for tree,pair in zip(paired_trees(),pairs):
        net,conditions=develop(p,tree);assertions+=conditions
        assertions.append(interior_overlap(net,FACES,*pair))
    return assertions,dict(class_id=class_id,simultaneous_pairs=pairs,
                           point_chart='A=0, B=(1,0,0), C.y<0, D.y>0, P.z<0, Q.z<0; no coordinate bounds',
                           faces=FACES,cut_trees=[t['cuts'] for t in paired_trees()])


def worker(job):
    import z3
    z3.set_param('memory_max_size',job['memory_mb'])
    assertions,metadata=formulation(job['class_id']);solver=z3.SolverFor('QF_NRA')
    solver.set(timeout=job['solver_ms']);solver.add(*assertions);path=Path(job['output'])
    path.with_suffix('.smt2').write_text(solver.to_smt2())
    report={**metadata,'result':'exported','assertions':len(assertions),'z3_version':z3.get_version_string(),
            'independent_proof_certificate':False,'scope':'Unresolved until a model or proof is independently checked.'}
    write_report(path.with_suffix('.result.json'),report)
    if not job['export_only']:
        start=time.monotonic();result=solver.check();report.update(result=str(result),solver_seconds=time.monotonic()-start)
        if result==z3.unknown:report['reason_unknown']=solver.reason_unknown()
        if result==z3.sat:path.with_suffix('.model.txt').write_text(str(solver.model())+'\n')
        write_report(path.with_suffix('.result.json'),report)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--worker',type=Path,help=argparse.SUPPRESS)
    ap.add_argument('--class-id',type=int,default=14)
    ap.add_argument('--solver-ms',type=int,default=15000)
    ap.add_argument('--wall-seconds',type=float,default=25)
    ap.add_argument('--memory-mb',type=int,default=1024)
    ap.add_argument('--output',default='n6/results/minus-class-14')
    ap.add_argument('--export-only',action='store_true');args=ap.parse_args()
    if args.worker:worker(json.loads(args.worker.read_text()))
    else:
        if not 1<=args.class_id<=28 or min(args.solver_ms,args.wall_seconds,args.memory_mb)<=0:ap.error('Invalid class or limit')
        job=vars(args);job.pop('worker');print(json.dumps(run_bounded(job,'n6.minus_query'),indent=2))
