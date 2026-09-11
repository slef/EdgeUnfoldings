"""Focused nonlinear queries using explicit planar triangle coordinates.

Each hinge adds two squared-distance equations and an orientation inequality.
These specify the unique development on the correct side of the hinge without
the large homogeneous expressions used by the archive encoding. SAT candidates
still require an independent geometric audit; UNSAT is a solver report only.
"""
import argparse
import json
from pathlib import Path
import time
from n6.query import run_bounded, write_report


def dot(a,b): return sum(x*y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def d2(a,b):
    e=sub(a,b); return dot(e,e)
def determinant(a,b): return a[0]*b[1]-a[1]*b[0]


def direct_net(points,faces,hinges,normalized_root=False):
    """Return placed faces, doubled areas, and exact development constraints."""
    import z3
    adj={i:[] for i in range(len(faces))}
    for a,b in hinges:adj[a].append(b);adj[b].append(a)
    if len(hinges)!=len(faces)-1:raise ValueError('Expected a hinge tree')
    a,b,c=faces[0]
    if normalized_root:
        q={a:points[a][:2],b:points[b][:2],c:points[c][:2]};assertions=[]
    else:
        ell,x,y=z3.FreshReal('root_length'),z3.FreshReal('root_x'),z3.FreshReal('root_y')
        q={a:(0,0),b:(ell,0),c:(x,y)}
        assertions=[ell>0,y>0]+[d2(q[u],q[v])==d2(points[u],points[v]) for u,v in ((a,b),(a,c),(b,c))]
    placed={0:q};order=[0]
    for parent in order:
        for child in adj[parent]:
            if child in placed:continue
            face=faces[child];old=placed[parent]
            a,b=next((u,v) for u,v in zip(face,face[1:]+face[:1]) if u in old and v in old)
            c=next(v for v in face if v not in (a,b))
            q={a:old[a],b:old[b],c:(z3.FreshReal('net_x'),z3.FreshReal('net_y'))}
            assertions.extend((d2(q[a],q[c])==d2(points[a],points[c]),
                               d2(q[b],q[c])==d2(points[b],points[c]),
                               determinant(sub(q[b],q[a]),sub(q[c],q[a]))>0))
            placed[child]=q;order.append(child)
    if len(placed)!=len(faces):raise ValueError('Disconnected hinge tree')
    areas=[]
    for i,f in enumerate(faces):
        a,b,c=(placed[i][v] for v in f)
        areas.append(determinant(sub(b,a),sub(c,a)))
    return placed,areas,assertions


def interior_overlap(placed,faces,a,b):
    import z3
    p=(z3.FreshReal('intersection_x'),z3.FreshReal('intersection_y'))
    return z3.And(*(determinant(sub(placed[f][v],placed[f][u]),sub(p,placed[f][u]))>0
                    for f in (a,b) for u,v in zip(faces[f],faces[f][1:]+faces[f][:1])))


def formulation(target,hypothesis='H3R',hard_local=False,lifted=False):
    import networkx as nx
    import z3
    from n6.encoding import Counterexample
    from n6.curvature import cmul,angle_le,curvature_sum_lt_pi,sum_angles_lt_pi,curvature_sum_lt_angle
    ce=Counterexample(nx.octahedral_graph(),prune_vertex_fans=True)
    v,w,u=0,5,1
    cuts={tuple(sorted((v,x))) for x in ce.g[v]}|{tuple(sorted((w,u)))}
    hinges=[(a,b) for a,b,d in ce.dual.edges(data=True) if d['primal'] not in cuts]
    placed,areas,development=direct_net(ce.x,ce.faces,hinges,normalized_root=True)
    # Strict supporting faces establish the convex octahedron. Heights from
    # the explicit isometric developments supply the angle products below.
    assertions=[ce.constraints[0]]
    for f,N in zip(ce.faces,ce.N):
        assertions.extend(dot(N,sub(ce.x[t],ce.x[f[0]]))<0 for t in ce.g if t not in f)
    assertions+=development
    angles={}
    for i,f in enumerate(ce.faces):
        for t in f:
            a,b=(x for x in f if x!=t)
            angles[i,t]=(dot(sub(placed[i][a],placed[i][t]),sub(placed[i][b],placed[i][t])),areas[i])
    products={}
    for t in ce.g:
        product=(1,0)
        for i,f in enumerate(ce.faces):
            if t in f:product=cmul(product,angles[i,t])
        products[t]=product
    if hypothesis in ('H3','H3R'):
        assertions.extend(angle_le(products[v],products[t]) for t in ce.g if t!=v)
    if hypothesis in ('R','H3R'):
        assertions.extend(angle_le(products[u],products[t]) for t in ce.g[w] if t!=u)
    if hard_local:assertions.append(curvature_sum_lt_pi(products[u],products[w]))
    lookup={frozenset(f):i for i,f in enumerate(ce.faces)};nxt={}
    for f in ce.faces:
        if w in f:
            i=f.index(w);nxt[f[(i+1)%3]]=f[(i+2)%3]
    ring=[u]
    while len(ring)<4:ring.append(nxt[ring[-1]])
    V=[lookup[frozenset((v,ring[i],ring[(i+1)%4]))] for i in range(4)]
    W=[lookup[frozenset((w,ring[i],ring[(i+1)%4]))] for i in range(4)]
    if target=='local_vv':pair=(V[0],V[3])
    elif target=='local_vw':pair=(V[0],W[3])
    elif target=='opposite':pair=(V[1],V[3])
    elif target in ('caseA_low_fan','caseA_low_fan_wide_failure'):
        pair=(V[1],V[3])
        # Convexity gives Gamma_w in (0,2*pi), so sin(Gamma_w)<=0
        # means Gamma_w>=pi, equivalently kappa_w<=pi. Keep equality.
        assertions.append(products[w][1]<=0)
        assertions.append(curvature_sum_lt_angle(products[ring[2]],products[ring[3]],angles[V[2],v]))
        if target=='caseA_low_fan_wide_failure':
            # Test the stronger sufficient-condition conjecture, not overlap.
            # The right edge reaches p*, so the distance-sum lemma makes the
            # left one short. Require its angle to exceed (pi+theta)/2.
            from n6.curvature import conjugate,cdet
            alpha=cmul(angles[V[2],ring[2]],conjugate(products[ring[2]]))
            beta=cmul(angles[V[2],ring[3]],conjugate(products[ring[3]]))
            theta=cmul(alpha,beta);left=angles[V[1],v];square=cmul(left,left)
            assertions.extend([left[0]<0,cdet((-square[0],-square[1]),theta)<0,
                d2(ce.x[v],ce.x[ring[3]])*theta[1]**2 >=
                d2(ce.x[ring[2]],ce.x[ring[3]])*alpha[1]**2*dot(beta,beta)])
    elif target in ('caseB_small_SW','left_apex','right_apex'):
        pair=(V[1],V[3])
        assertions.append(sum_angles_lt_pi([angles[W[1],ring[2]],angles[W[2],ring[2]],
                                            angles[W[2],ring[3]],angles[W[3],ring[3]]]))
    else:raise ValueError('Unknown target')
    if target in ('left_apex','right_apex'):
        if target=='left_apex':
            line_face=W[3];a,b=ring[3],ring[0];apex_face=V[1]
        else:
            line_face=W[1];a,b=ring[2],ring[1];apex_face=V[3]
        q=placed[line_face];direction=sub(q[b],q[a])
        assertions.append(determinant(direction,sub(placed[apex_face][v],q[a]))*
                          determinant(direction,sub(q[w],q[a]))<0)
    elif target!='caseA_low_fan_wide_failure':
        assertions.append(interior_overlap(placed,ce.faces,*pair))
    auxiliary_count=0
    if lifted:
        from n6.lift import arithmetic_lift
        assertions,aux=arithmetic_lift(assertions);auxiliary_count=len(aux)
    return assertions,dict(apex=v,antipode=w,slit_vertex=u,equator=ring,cuts=sorted(cuts),pair=pair,
                           faces=ce.faces,auxiliary_variables=auxiliary_count)


def worker(job):
    import z3
    from n6.encoding import export_smt2
    z3.set_param('memory_max_size',job['memory_mb'])
    assertions,geometry=formulation(job['target'],job['hypothesis'],job['hard_local'],job['lifted'])
    path=Path(job['output']);nodes=export_smt2(assertions,path.with_suffix('.smt2'))
    report={**job,'result':'exported','geometry':geometry,'assertions':len(assertions),
            'dag_nodes':nodes,'smt2_bytes':path.with_suffix('.smt2').stat().st_size,
            'independent_proof_certificate':False,'z3_version':z3.get_version_string()}
    write_report(path.with_suffix('.result.json'),report)
    if job['export_only']:return
    if job['lifted']:
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
            'sat':'Candidate only; exact model extraction and geometric checking required.',
            'unknown':'Unresolved; no mathematical conclusion.'}[str(result)]
    except z3.Z3Exception as error:
        report.update(result='solver_error',error=str(error),scope='Unresolved; no mathematical conclusion.')
    write_report(path.with_suffix('.result.json'),report)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--worker',type=Path,help=argparse.SUPPRESS)
    ap.add_argument('--target',choices=['local_vv','local_vw','opposite','caseA_low_fan','caseA_low_fan_wide_failure','caseB_small_SW','left_apex','right_apex'],default='local_vv')
    ap.add_argument('--hypothesis',choices=['none','H3','R','H3R'],default='H3R')
    ap.add_argument('--hard-local',action='store_true');ap.add_argument('--lifted',action='store_true')
    ap.add_argument('--solver-ms',type=int,default=600000);ap.add_argument('--wall-seconds',type=float,default=660)
    ap.add_argument('--memory-mb',type=int,default=1024);ap.add_argument('--export-only',action='store_true')
    ap.add_argument('--output',default='n6/results/direct-query')
    args=ap.parse_args()
    if args.worker:worker(json.loads(args.worker.read_text()));return
    if min(args.solver_ms,args.wall_seconds,args.memory_mb)<=0:ap.error('limits must be positive')
    job=vars(args);job.pop('worker')
    print(json.dumps(run_bounded(job,worker_module='n6.direct_query'),indent=2))


if __name__=='__main__':main()
