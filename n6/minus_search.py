"""Bounded numerical counterexample search for a named minus-edge tree family.

Nelder-Mead runs in a ten-coordinate chart. Failure to find a counterexample
proves nothing; any negative candidate still requires exact verification.
"""
import argparse
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import minimize
from n6.minus_patterns import TreeBatch,family_indices,canonical_points,valid_points,random_points


def parameters(points):
    p=canonical_points(points)
    return np.array([p[2,0],np.log(-p[2,1]),p[3,0],np.log(p[3,1]),
                     p[4,0],p[4,1],np.log(-p[4,2]),p[5,0],p[5,1],np.log(-p[5,2])])


def points(q):
    a,b,c,d,r,s,h,t,k,l=q
    return np.array([[0.,0,0],[1,0,0],[a,-np.exp(b),0],[c,np.exp(d),0],
                     [r,s,-np.exp(h)],[t,k,-np.exp(l)]])


class Budget(Exception):pass


def search(family,seconds,seed,output):
    all_batch=TreeBatch();indices=family_indices(all_batch.trees)[family]
    batch=TreeBatch([all_batch.trees[i] for i in indices]);rng=np.random.default_rng(seed)
    start=time.monotonic();calls=accepted=completed=attempts=0;best=None;seeds=[]
    def objective(q):
        nonlocal calls,accepted,best
        if time.monotonic()-start>seconds:raise Budget()
        calls+=1
        if not np.isfinite(q).all() or max(abs(q[[1,3,6,9]]))>18:return 10.
        p=points(q);p=valid_points(p,tolerance=1e-10)
        if p is None:return 10.
        accepted+=1;margins=batch.margins(p);value=float(max(margins))
        if best is None or value<best['best_margin']:
            best={'parameters':q.tolist(),'points':points(q).tolist(),'margins':margins.tolist(),'best_margin':value}
        return value
    try:
        # Separate starts, rather than just following the thinnest sample.
        while len(seeds)<150:
            p=random_points(rng,attempts);attempts+=1
            if p is not None:
                q=parameters(p);objective(q);seeds.append(q)
        rng.shuffle(seeds)
        for q in seeds:
            simplex=np.tile(q,(11,1));steps=.08*np.maximum(abs(q),.5)
            for i in range(10):simplex[i+1,i]+=steps[i]
            minimize(objective,q,method='Nelder-Mead',options={
                'initial_simplex':simplex,'maxfev':1800,'xatol':1e-8,'fatol':1e-12})
            completed+=1
            print(json.dumps({'starts_completed':completed,'calls':calls,'best_margin':best['best_margin'],'seconds':time.monotonic()-start}),flush=True)
            if best['best_margin'] < -1e-8:break
    except Budget:pass
    result={'scope':'Numerical search only; no universal conclusion. Exact audit required for a failure.',
            'family':family,'tree_indices':indices,'trees':batch.trees,'seed':seed,
            'seconds':time.monotonic()-start,'calls':calls,'valid_calls':accepted,'starts_completed':completed,
            'point_domain':'P0=0, P1=(1,0,0); P2.y<0, P3.y>0; P4.z,P5.z<0. Strict facets screened numerically.',
            'screening_tolerance':1e-10,'log_coordinate_bound':18,'failure_threshold':-1e-8,
            'best':best,'result':'candidate_failure' if best and best['best_margin']<-1e-8 else 'no_failure_found'}
    output.write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--family',default='off_quad_pair_via_0')
    ap.add_argument('--seconds',type=float,default=180)
    ap.add_argument('--seed',type=int,default=6090922)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();print(json.dumps(search(args.family,args.seconds,args.seed,args.output),indent=2))
