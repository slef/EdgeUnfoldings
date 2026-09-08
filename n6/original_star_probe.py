"""Probe six original-edge star candidates for the prism with one diagonal.

This is a smaller candidate family than all 130 cut trees. No numerical result
from this file is a universal certificate. Failed candidates must be rechecked
with polynomial parameter coordinates so that facet coplanarity is exact.
"""
import argparse
import json
from pathlib import Path
import time
import numpy as np
from n6.families import PRISM_FACES
from n6.prism_diagonal import points,parameter_domain,develop,pair_score
from n6.trees import degree_four_stars
from n6.query import write_report


def inspect(parameters,trees):
    if not parameter_domain(parameters):return None
    p=points(parameters);p/=np.max(np.linalg.norm(p[:,None]-p[None],axis=2))
    for f in PRISM_FACES:
        a,b,c=p[list(f[:3])];N=np.cross(b-a,c-a);h=np.linalg.norm(N)
        if h<1e-13:return None
        if max((p[v]-a)@N/h for v in range(6) if v not in f)>=-1e-11:return None
    margins=[]
    for t in trees:
        net=develop(p,PRISM_FACES,t['hinges'],root=0)
        margins.append(float(min(-pair_score(net[a],net[b]) for a,b in t['pairs'])))
    return margins


def run(samples,seconds,seed,output):
    rng=np.random.default_rng(seed);start=time.monotonic();trees=degree_four_stars(PRISM_FACES)
    count=attempts=0;worst=None;successes=np.zeros(len(trees),dtype=int)
    while count<samples and time.monotonic()-start<seconds:
        attempts+=1
        x,u,v=rng.normal(size=3)*10**rng.uniform(-2,2,size=3)
        y,w=10**rng.uniform(-2,2,size=2);A,B,C,D=10**rng.uniform(-2,2,size=4)
        parameters=[x,y,u,v,w,A,B,C,D]
        margins=inspect(parameters,trees)
        if margins is None:continue
        count+=1;successes+=np.array(margins)>=0
        if worst is None or max(margins)<worst['best_margin']:
            worst=dict(parameters=list(map(float,parameters)),margins=margins,best_margin=max(margins))
        if max(margins)<-1e-7:break
        if count%1000==0:print(count,worst['best_margin'],flush=True)
    result=dict(scope='Numerical exploration only; a failed finite family is not a Durer counterexample.',
                samples=count,attempts=attempts,seconds=time.monotonic()-start,seed=seed,
                family_size=len(trees),trees=trees,successes=successes.tolist(),worst=worst,
                result='candidate_family_failure' if worst and worst['best_margin']<-1e-7 else 'no_failure_found')
    write_report(output,result);return result


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--samples',type=int,default=20000)
    ap.add_argument('--seconds',type=float,default=600);ap.add_argument('--seed',type=int,default=6090912)
    ap.add_argument('--output',type=Path,default=Path('n6/results/prism-star-family.json'))
    args=ap.parse_args()
    if min(args.samples,args.seconds)<=0:ap.error('Limits must be positive')
    print(json.dumps(run(args.samples,args.seconds,args.seed,args.output),indent=2))


if __name__=='__main__':main()
