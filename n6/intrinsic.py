"""Exact necessary metric conditions for the remaining apex-angle question.

Twelve shared edge lengths determine eight Euclidean triangles. This is an
intrinsic relaxation: no convex realization with those original facets is
asserted. Verification uses rational bounds; the optional nonlinear solver
searches for candidates and does not supply an independently checked proof.
"""
from n6.certify import require
from n6.curvature import cmul,cdet,angle_le,sum_angles_lt_pi
from n6.intervals import I


def triangle_angles(q,h):
    """Angles opposite squared sides q; h is four times triangle area."""
    return [(sum(q)-2*x,h) for x in q]


def incident_angles(angles):
    return [angles['nu'],angles['om']]+[
        [angles['aV'][i],angles['aVp'][i-1],angles['bW'][i],angles['bWp'][i-1]]
        for i in range(4)]


def product(angles):
    acc=angles[0]
    for a in angles[1:]:acc=cmul(acc,a)
    return acc


def sum_angles_lt_turn(angles):
    """Symbolic sum below 2*pi; each input angle must lie in (0,pi)."""
    import z3
    if not angles:raise ValueError('Expected positive angles')
    acc=angles[0];conditions=[]
    for a in angles[1:]:
        nxt=cmul(acc,a)
        conditions.append(z3.Not(z3.And(acc[1]<0,nxt[1]>=0)))
        acc=nxt
    return z3.And(*conditions)


def checked_sum(angles):
    """Prove a sum is in (0,2*pi), rejecting full turns or undecided signs."""
    require(angles and all(a[1].lo>0 for a in angles),'Nonpositive face angle')
    acc=angles[0]
    for a in angles[1:]:
        nxt=cmul(acc,a)
        if acc[1].hi<0:
            require(nxt[1].hi<0,'Full turn or unresolved angle sum')
        else:
            require(acc[1].lo>=0,'Unresolved intermediate angle sum')
        acc=nxt
    return acc


def strict_angle_lt(a,b):
    """Both arguments must already represent angles strictly in (0,2*pi)."""
    def half(z):
        if z[1].lo>=0:return 0
        if z[1].hi<0:return 1
        return None
    ha,hb=half(a),half(b)
    if ha is None or hb is None:return False
    return ha<hb if ha!=hb else cdet(a,b).lo>0


def metric_angles(lengths):
    require(set(lengths)=={'s','r','l'},'Expected squared s, r, l lengths')
    require(all(len(q)==4 for q in lengths.values()),'Expected four edges per row')
    q={name:[I(x) for x in row] for name,row in lengths.items()}
    require(all(x.lo>0 for row in q.values() for x in row),'Nonpositive squared edge')
    angles={n:[] for n in ('nu','aV','aVp','om','bW','bWp')}
    for prefix,names in [('s',('nu','aV','aVp')),('r',('om','bW','bWp'))]:
        for i in range(4):
            sides=[q['l'][i],q[prefix][(i+1)%4],q[prefix][i]]
            a,b,c=sides;heron=4*b*c-(b+c-a).square()
            require(heron.lo>0,'Triangle inequality or area not certified')
            for name,z in zip(names,triangle_angles(sides,heron.sqrt())):angles[name].append(z)
    return angles


def verify(spec):
    require(spec.get('schema')=='n6-intrinsic-octahedron-metric-v1','Unknown intrinsic schema')
    k=spec['slit_index'];i=spec['triple_index']
    require(type(k) is int and type(i) is int and k in range(4) and i in range(4),'Invalid ring index')
    require(k in (i,(i-1)%4),'Triple crosses the slit')
    angles=metric_angles(spec['squared_edge_lengths']);inc=incident_angles(angles)
    totals=[checked_sum(row) for row in inc]
    cone=[all(strict_angle_lt(cmul(a,a),total) for a in row) for row,total in zip(inc,totals)]
    cone_failures=[any(strict_angle_lt(total,cmul(a,a)) for a in row) for row,total in zip(inc,totals)]
    if spec.get('require_cone',True):require(all(cone),'Strict convex-vertex cone inequality not certified')
    require(all(strict_angle_lt(totals[0],t) for t in totals[1:]),'Strict sharpest-apex ranking not certified')
    require(all(strict_angle_lt(totals[k+2],totals[t+2]) for t in range(4) if t!=k),'Strict slit ranking not certified')
    j,jj=(i+1)%4,(i+2)%4
    target=[angles['bWp'][i],angles['bW'][j],angles['bWp'][j],angles['bW'][jj],angles['aVp'][i]]
    total=checked_sum(target)
    require(total[1].lo>0,'Strict apex-direction bound violation not certified')
    return dict(result='verified_intrinsic_angle_countermodel',triangles=8,positive_curvature_vertices=6,
                strict_cone_inequalities_by_vertex=cone,strict_H_and_R=True,
                proved_cone_violations_by_vertex=cone_failures,
                target='Sigma_W+a < pi',target_product=[x.pair() for x in total],
                scope='Shared Euclidean triangle lengths and the stated checks only. No convex original-facet realization or unfolding overlap is asserted.')


def query(cone=True,sharpest=True,slit_index=3):
    import z3
    if slit_index not in (0,3):raise ValueError('Triple 0 permits slit 0 or 3')
    lengths={n:[z3.Real(f'{n}2_{i}') for i in range(4)] for n in ('s','r','l')}
    heights=[z3.Real(f'area4_{i}') for i in range(8)]
    assertions=[x>0 for row in lengths.values() for x in row]+[h>0 for h in heights]
    assertions.append(lengths['s'][0]==1)
    angles={n:[] for n in ('nu','aV','aVp','om','bW','bWp')}
    for offset,prefix,names in [(0,'s',('nu','aV','aVp')),(4,'r',('om','bW','bWp'))]:
        for i in range(4):
            sides=[lengths['l'][i],lengths[prefix][(i+1)%4],lengths[prefix][i]]
            a,b,c=sides;h=heights[offset+i]
            assertions.append(h*h==4*b*c-(b+c-a)**2)
            for name,z in zip(names,triangle_angles(sides,h)):angles[name].append(z)
    inc=incident_angles(angles);totals=[product(row) for row in inc]
    assertions += [sum_angles_lt_turn(row) for row in inc]
    if cone:assertions += [angle_le(cmul(a,a),total) for row,total in zip(inc,totals) for a in row]
    if sharpest:assertions += [angle_le(totals[0],t) for t in totals[1:]]
    assertions += [angle_le(totals[slit_index+2],totals[t+2]) for t in range(4) if t!=slit_index]
    assertions.append(sum_angles_lt_pi([angles['bWp'][0],angles['bW'][1],angles['bWp'][1],angles['bW'][2],angles['aVp'][0]]))
    return assertions,lengths


def worker(job):
    import json,time
    from pathlib import Path
    from types import SimpleNamespace
    args=SimpleNamespace(**job);args.output=Path(args.output)
    import z3
    from n6.lift import arithmetic_lift,lifted_solver
    z3.set_param('memory_max_size',args.memory_mb)
    start=time.monotonic();assertions,lengths=query(not args.without_cone,not args.without_H,args.slit_index)
    if args.unlifted:
        solver=z3.SolverFor('QF_NRA');solver.set(timeout=1000*args.seconds);aux=[]
    else:assertions,aux=arithmetic_lift(assertions);solver=lifted_solver(1000*args.seconds)
    solver.add(*assertions)
    args.output.with_suffix('.smt2').write_text(solver.to_smt2())
    result=solver.check();report=dict(job,result=str(result),seconds=time.monotonic()-start,auxiliaries=len(aux),
        cone=not args.without_cone,H=not args.without_H,R=True,
        slit_index=args.slit_index,triple_index=0,
        scope='Solver exploration of an intrinsic relaxation, without an independent proof certificate. SAT values require exact replay and do not establish convex realization.')
    if result==z3.unknown:report['reason']=solver.reason_unknown()
    if result==z3.sat:
        m=solver.model();report['squared_lengths_solver_values']={k:[str(m.eval(x)) for x in row] for k,row in lengths.items()}
    args.output.write_text(json.dumps(report,indent=2)+'\n')


def main():
    import argparse,json
    from pathlib import Path
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--worker',type=Path,help=argparse.SUPPRESS)
    sub=ap.add_subparsers(dest='action')
    check=sub.add_parser('verify');check.add_argument('input',type=Path)
    search=sub.add_parser('query');search.add_argument('--output',type=Path,required=True)
    search.add_argument('--seconds',type=int,default=600);search.add_argument('--without-cone',action='store_true')
    search.add_argument('--without-H',action='store_true');search.add_argument('--unlifted',action='store_true')
    search.add_argument('--slit-index',type=int,choices=(0,3),default=3)
    search.add_argument('--wall-seconds',type=float);search.add_argument('--memory-mb',type=int,default=1024)
    args=ap.parse_args()
    if args.worker:worker(json.loads(args.worker.read_text()));return
    if args.action is None:ap.error('verify or query required')
    if args.action=='verify':print(json.dumps(verify(json.loads(args.input.read_text())),indent=2));return
    wall=args.wall_seconds if args.wall_seconds is not None else args.seconds+30
    if min(args.seconds,wall,args.memory_mb)<=0:ap.error('Limits must be positive')
    from n6.query import run_bounded
    job={k:v for k,v in vars(args).items() if k not in ('action','worker')}
    job.update(output=str(args.output),wall_seconds=wall,solver_ms=1000*args.seconds)
    print(json.dumps(run_bounded(job,worker_module='n6.intrinsic',result_suffix='.json'),indent=2))


if __name__=='__main__':main()
