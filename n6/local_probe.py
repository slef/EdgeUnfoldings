"""Directed numerical search for selected-rule local and Case-B obstructions.

There is no fixed positive degeneracy guard. Numerically unresolved facets are
rejected by octa_structure. Hypotheses are selected numerically and must be
verified by the exact curvature checker before any candidate is a counterexample.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys
import time
import numpy as np
from n6.prism_diagonal import pair_score
from n6.query import write_report

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'durer_small_n'))
from octa import octa_structure,sharpest_apex,rand_points,Octa


def configuration(P):
    st=octa_structure(P)
    if st is None:return None
    o=sharpest_apex(P,*st);k=int(np.argmax(o.ku))
    local=[float(pair_score(*o.pair_faces(k,name))/o.scale) for name in Octa.LOCAL]
    triples=[]
    for i in (k,(k+1)%4):
        j,jj=(i+1)%4,(i+2)%4
        left=o.aV[j]+o.ku[j]-np.pi;right=o.aVp[j]+o.ku[jj]-np.pi
        triples.append(dict(i=i,caseA=bool(o.ku[j]+o.ku[jj]<o.nu[j]),
                            left_D_excess=float(left),right_D_excess=float(right),
                            sum_W=float(o.bWp[i]+o.bW[j]+o.bWp[j]+o.bW[jj])))
    return dict(points=np.asarray(P).tolist(),apex=o.v,antipode=o.w,slit_index=k,slit_vertex=o.u[k],
                equator=o.u,curvatures={str(v):float(a) for v,a in o.kappa.items()},
                local_scores=local,local=max(local),
                lean=float(o.B[k]+o.F[(k-1)%4]-o.kw),
                large_D=max(max(t['left_D_excess'],t['right_D_excess']) for t in triples),
                slit_curvature_sum=float(o.ku[k]+o.kw),triples=triples)


def normalize(P):
    P=np.asarray(P,dtype=float);P=P-P.mean(axis=0)
    return P/np.max(np.linalg.norm(P[:,None]-P[None],axis=2))


def run(samples,seconds,seed,objective,output):
    rng=np.random.default_rng(seed);start=time.monotonic();attempts=evaluations=restarts=0
    hist=Counter();best=None;recent=[]
    def inspect(P):
        nonlocal attempts,evaluations,best
        attempts+=1;c=configuration(P)
        if c is None:return None
        evaluations+=1
        hist['K<pi' if c['slit_curvature_sum']<np.pi else 'pi<=K<2pi' if c['slit_curvature_sum']<2*np.pi else 'K>=2pi']+=1
        hist['large_D']+=c['large_D']>=0
        hist['positive_local']+=c['local']>1e-7
        if best is None or c[objective]>best[objective]:best=c
        return c
    def report():
        return dict(scope='Numerical exploration only; no proof or certificate.',objective=objective,
                    evaluations=evaluations,attempts=attempts,restarts=restarts,seed=seed,
                    seconds=time.monotonic()-start,histogram=dict(hist),best=best,recent_restarts=recent[-20:])
    while evaluations<samples and time.monotonic()-start<seconds:
        P=normalize(rand_points(6,rng));cur=inspect(P)
        if cur is None:continue
        restarts+=1;step=.1
        for _ in range(400):
            if time.monotonic()-start>=seconds or evaluations>=samples:break
            if rng.random()<.35:Q=P@(np.eye(3)+rng.normal(size=(3,3))*step)
            else:Q=P+rng.normal(size=(6,3))*step
            Q=normalize(Q);candidate=inspect(Q)
            if candidate is not None and candidate[objective]>cur[objective]:P=Q;cur=candidate;step*=1.1
            else:step*=.98
            if step<1e-7:step=.1
            if best and best['local']>1e-7:break
        recent.append({objective:cur[objective],'local':cur['local'],'large_D':cur['large_D']})
        write_report(output,report())
        if restarts%10==0:print(restarts,evaluations,objective,best[objective],flush=True)
        if best and best['local']>1e-7:break
    result=report();write_report(output,result);return result


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--samples',type=int,default=100000);ap.add_argument('--seconds',type=float,default=1200)
    ap.add_argument('--seed',type=int,default=6090904)
    ap.add_argument('--objective',choices=['local','lean','large_D'],default='local')
    ap.add_argument('--output',type=Path,default=Path('n6/results/local-directed.json'))
    args=ap.parse_args()
    if min(args.samples,args.seconds)<=0:ap.error('limits must be positive')
    print(json.dumps(run(args.samples,args.seconds,args.seed,args.objective,args.output),indent=2))


if __name__=='__main__':main()
