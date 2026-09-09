"""Reproducible numerical searches of the remaining two-tree failure classes.

Numerical outcomes never close proof classes. Near-zero candidates can be
reconstructed as exact decimal coordinates and independently audited.
"""
import argparse
import json
from pathlib import Path
import time
from n6.query import write_report


def survey(samples=12000,seconds=60,seed=6090930):
    import numpy as np
    from n6.minus_patterns import TreeBatch,random_points
    from n6.minus_pair import paired_trees
    batch=TreeBatch(paired_trees());rng=np.random.default_rng(seed)
    counts=np.zeros((2,21),int);best=np.full((21,21),-np.inf);witnesses={}
    n=attempts=0;start=time.monotonic()
    while n<samples and time.monotonic()-start<seconds:
        p=random_points(rng,attempts);attempts+=1
        if p is None:continue
        scores=batch.pair_scores(p);n+=1;counts+=scores>1e-8
        joint=np.minimum(scores[0,:,None],scores[1,None,:]);rows,cols=np.where(joint>best)
        for i,j in zip(rows,cols):witnesses[f'{i},{j}']=p.tolist()
        best=np.maximum(best,joint)
    return dict(scope='Numerical survey only; no universal conclusions.',seed=seed,
                samples=n,attempts=attempts,seconds=time.monotonic()-start,pairs=batch.pairs,
                counts=counts.tolist(),best=[[None if not np.isfinite(x) else float(x) for x in row] for row in best],
                witnesses=witnesses,failure_threshold=1e-8)


class Budget(Exception):pass


def search(data,output,seconds=12,seed=6090931):
    import numpy as np
    from scipy.optimize import minimize
    from n6.minus_pair import paired_trees,proof_progress
    from n6.minus_patterns import TreeBatch,random_points,valid_points
    from n6.minus_search import points,parameters
    batch=TreeBatch(paired_trees());rng=np.random.default_rng(seed)
    records=[];start=time.monotonic();calls=0
    for item in proof_progress()['classes']:
        if item['status']!='open':continue
        a,b=map(tuple,item['orbit'][0]);i=batch.pairs.index(a);j=batch.pairs.index(b)
        best={'score':None};class_start=time.monotonic();class_calls=0
        def objective(q):
            nonlocal calls,class_calls
            calls+=1;class_calls+=1
            if time.monotonic()-class_start>seconds:raise Budget()
            if not np.isfinite(q).all() or max(abs(q[[1,3,6,9]]))>16:return 10.
            p=valid_points(points(q),tolerance=1e-10)
            if p is None:return 10.
            scores=batch.pair_scores(p);score=float(min(scores[0,i],scores[1,j]))
            if best['score'] is None or score>best['score']:
                best.update(score=score,points=points(q).tolist(),scores=[float(scores[0,i]),float(scores[1,j])])
            return -score
        seeds=[parameters(data['witnesses'][f'{i},{j}'])];attempts=0
        while len(seeds)<6:
            p=random_points(rng,attempts);attempts+=1
            if p is not None:seeds.append(parameters(p))
        try:
            for q in seeds:
                simplex=np.tile(q,(11,1));steps=.1*np.maximum(abs(q),.5)
                for k in range(10):simplex[k+1,k]+=steps[k]
                minimize(objective,q,method='Nelder-Mead',options={
                    'initial_simplex':simplex,'maxfev':3500,'xatol':1e-9,'fatol':1e-12})
                if best['score'] is not None and best['score']>1e-8:break
        except Budget:pass
        records.append(dict(**{'class':item['id']},pairs=[a,b],best=best,calls=class_calls,
                            seconds=time.monotonic()-class_start))
        write_report(output,dict(scope='Numerical search only; exact audit required.',seed=seed,
                                 calls=calls,seconds=time.monotonic()-start,classes=records))
        print(item['id'],best['score'],class_calls,flush=True)
        if best['score'] is not None and best['score']>1e-8:break


def audit(data,bits=240):
    from n6.intervals import set_precision
    from n6.minus_pair import paired_trees,make_bundle,verify_bundle
    set_precision(bits);audits=[];start=time.monotonic()
    for rec in data['classes']:
        if rec['best']['score'] is None or rec['best']['score']<=-1e-12:continue
        points=[[str(v) for v in row] for row in rec['best']['points']]
        try:
            bundle=make_bundle(points,paired_trees(),'off_quad_pair_via_0');report=verify_bundle(bundle)
            audits.append({'class':rec['class'],'certificate':bundle,'verification':report})
        except ValueError as error:
            audits.append({'class':rec['class'],'result':'unresolved','reason':str(error)})
    return dict(schema='n6-minus-targeted-audits-v1',fractional_bits=bits,audits=audits,
                seconds=time.monotonic()-start,
                scope='Exact decimal reconstructions of selected individual candidates; no whole failure class is excluded.')


def verify_audits(data):
    from n6.certify import require
    from n6.intervals import set_precision
    from n6.minus_pair import verify_bundle
    require(data.get('schema')=='n6-minus-targeted-audits-v1','Unknown audit schema')
    set_precision(data['fractional_bits']);seen=set();outcomes=[]
    for item in data['audits']:
        index=item['class'];require(index not in seen and 1<=index<=28,'Repeated or invalid class')
        seen.add(index)
        if 'certificate' not in item:
            require(item.get('result')=='unresolved','Missing audit certificate')
            outcomes.append(dict(class_id=index,result='unresolved'));continue
        result=verify_bundle(item['certificate'])
        outcomes.append(dict(class_id=index,**result))
    return dict(result='replayed_individual_audits',fractional_bits=data['fractional_bits'],outcomes=outcomes,
                scope='Exact outcomes at the supplied shapes only. No universal class exclusion follows.')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action',choices=('survey','search','audit','verify-audits'))
    ap.add_argument('--input',type=Path);ap.add_argument('--output',type=Path)
    ap.add_argument('--samples',type=int,default=12000);ap.add_argument('--seconds',type=float)
    ap.add_argument('--seed',type=int);args=ap.parse_args()
    if args.action!='survey' and args.input is None:ap.error('--input is required')
    if args.action!='verify-audits' and args.output is None:ap.error('--output is required')
    if args.samples<=0 or (args.seconds is not None and args.seconds<=0):ap.error('Limits must be positive')
    source=json.loads(args.input.read_text()) if args.input else None
    if args.action=='survey':
        result=survey(args.samples,args.seconds or 60,6090930 if args.seed is None else args.seed)
    elif args.action=='search':
        search(source,args.output,args.seconds or 12,6090931 if args.seed is None else args.seed);result=None
    elif args.action=='audit':result=audit(source)
    else:result=verify_audits(source)
    if result is not None:
        if args.output:write_report(args.output,result)
        else:print(json.dumps(result,indent=2))
