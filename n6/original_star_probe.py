"""Probe small original-edge star families for the prism with one diagonal.

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
from n6.trees import degree_four_stars,quadrilateral_path_stars
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


def apex_curvature(p,faces,v):
    angles=[]
    for f in faces:
        if v not in f:continue
        i=f.index(v);a=p[f[i-1]]-p[v];b=p[f[(i+1)%len(f)]]-p[v]
        angles.append(np.arctan2(np.linalg.norm(np.cross(a,b)),a@b))
    return float(2*np.pi-sum(angles))


def run(samples,seconds,seed,output,family='six'):
    rng=np.random.default_rng(seed);start=time.monotonic();trees=(quadrilateral_path_stars if family=='quadrilateral' else degree_four_stars)(PRISM_FACES)
    count=attempts=0;worst=None;successes=np.zeros(len(trees),dtype=int)
    per_apex={str(v):0 for v in sorted({t['apex'] for t in trees})};per_apex_candidates={}
    selected_failures=shorter_failures=0;selected_candidate=None;shorter_candidate=None
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
        for apex in per_apex:
            value=max(m for t,m in zip(trees,margins) if t['apex']==int(apex))
            if value < -1e-7:
                per_apex[apex]+=1
                if apex not in per_apex_candidates or value<per_apex_candidates[apex]['best_margin']:
                    per_apex_candidates[apex]=dict(apex=int(apex),parameters=list(map(float,parameters)),margins=margins,best_margin=value)
        if family=='quadrilateral':
            p=points(parameters);apex=max(map(int,per_apex),key=lambda v:apex_curvature(p,PRISM_FACES,v))
            options=[j for j,t in enumerate(trees) if t['apex']==apex]
            selected=max(margins[j] for j in options)
            def path_length(j):
                t=trees[j];v,w,u=(t[n] for n in ('apex','antipode','slit_vertex'))
                return np.linalg.norm(p[v]-p[u])+np.linalg.norm(p[u]-p[w])
            short=min(options,key=path_length)
            if selected < -1e-7:
                selected_failures+=1
                if selected_candidate is None or selected<selected_candidate['best_margin']:
                    selected_candidate=dict(parameters=list(map(float,parameters)),apex=apex,best_margin=selected,margins=margins)
            if margins[short] < -1e-7:
                shorter_failures+=1
                if shorter_candidate is None or margins[short]<shorter_candidate['margin']:
                    shorter_candidate=dict(parameters=list(map(float,parameters)),apex=apex,tree_index=short,margin=margins[short],margins=margins)
        if max(margins)<-1e-7:break
        if count%1000==0:print(count,worst['best_margin'],flush=True)
    result=dict(scope='Numerical exploration only; a failed finite family is not a Durer counterexample.',
                samples=count,attempts=attempts,seconds=time.monotonic()-start,seed=seed,
                selected_apex_pair_failures=selected_failures,selected_apex_candidate=selected_candidate,shorter_path_failures=shorter_failures,shorter_path_candidate=shorter_candidate,
                family=family,family_size=len(trees),trees=trees,per_apex_failure_counts=per_apex,per_apex_candidates=per_apex_candidates,successes=successes.tolist(),worst=worst,
                result='candidate_family_failure' if worst and worst['best_margin']<-1e-7 else 'no_failure_found')
    write_report(output,result);return result


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--samples',type=int,default=20000)
    ap.add_argument('--seconds',type=float,default=600);ap.add_argument('--seed',type=int,default=6090912)
    ap.add_argument('--family',choices=('six','quadrilateral'),default='six')
    ap.add_argument('--output',type=Path,default=Path('n6/results/prism-star-family.json'))
    args=ap.parse_args()
    if min(args.samples,args.seconds)<=0:ap.error('Limits must be positive')
    print(json.dumps(run(args.samples,args.seconds,args.seed,args.output,args.family),indent=2))


if __name__=='__main__':main()
