"""Explore sharp-slit and high-source two-route hypotheses, never prove them."""
import argparse
from collections import Counter
import json
from pathlib import Path
import time
import numpy as np
from n6.families import MINUS_FACES,PRISM_FACES
from n6.flat_octahedron import original_candidates
from n6.minus_patterns import TreeBatch
from n6.original_rule_probe import SEEDS,sample
from n6.original_star_probe import apex_curvature
from n6.trees import tree_data


def run(kind,samples,seed,seconds):
    faces=MINUS_FACES if kind=='minus' else PRISM_FACES
    family,trees=original_candidates(faces)
    batch=TreeBatch([tree_data(faces,t['cuts']) for t in trees],faces)
    rng=np.random.default_rng(seed);start=time.monotonic();counts=Counter();failures={};worst={};tol=1e-7
    attempts=0
    while counts['samples']<samples and time.monotonic()-start<seconds:
        attempts+=1;proposal=sample(rng,np.array(SEEDS[kind],dtype=np.int64))
        if proposal is None:continue
        p,exact=proposal
        if any(np.linalg.norm(np.cross(p[f[1]]-p[f[0]],p[f[2]]-p[f[0]]))<1e-12 for f in faces):continue
        k=np.array([apex_curvature(p,faces,x) for x in range(6)])
        if min(k)<1e-8 or max(k)>2*np.pi-1e-8:continue
        counts['samples']+=1
        eligible=[i for i,t in enumerate(trees) if k[t['slit']]>np.pi+tol and k[t['fan']]<np.pi-tol]
        high_sources=[v for v in {t['source'] for t in trees} if k[v]>np.pi+tol]
        if not eligible and not high_sources:continue
        margins=batch.margins(p)
        counts['sharp_slit_candidates']+=len(eligible)
        for i in eligible:
            if margins[i]<-tol:
                counts['sharp_slit_failures']+=1
                if 'sharp_slit' not in failures or margins[i]<failures['sharp_slit']['margin']:
                    failures['sharp_slit']=dict(**exact,tree=i,margin=float(margins[i]),
                        curvature_degrees=(k*180/np.pi).tolist(),net_margins=margins.tolist())
        for v in high_sources:
            options=[i for i,t in enumerate(trees) if t['source']==v]
            counts['high_source_all_original_slits']+=1
            if max(margins[options]) < -tol:
                counts['high_source_all_original_slits_failures']+=1
                failures.setdefault('high_source_all_slits',dict(**exact,source=v,trees=options,
                    curvature_degrees=(k*180/np.pi).tolist(),net_margins=margins.tolist()))
            w=trees[options[0]]['fan'];forbidden=[e for e in family['artificial_diagonals'] if w in e]
            if not forbidden:continue
            diagonal=set(forbidden[0]);quad=next(f for f in faces if len(f)==4 and diagonal<=set(f))
            endpoints=set(quad)-diagonal;routes=[i for i in options if trees[i]['slit'] in endpoints]
            counts['high_source_two_routes']+=1
            value=float(max(margins[routes]))
            if 'high_source' not in worst or value<worst['high_source']['margin']:
                worst['high_source']=dict(**exact,source=v,trees=routes,margin=value,
                    curvature_degrees=(k*180/np.pi).tolist(),net_margins=margins.tolist())
            if value<-tol:
                counts['high_source_two_route_failures']+=1;failures['high_source']=worst['high_source']
        if kind=='prism':
            v=max((1,3),key=lambda x:k[x]);w=5 if v==1 else 2
            quad=next(f for f in faces if len(f)==4 and {v,w}<=set(f))
            endpoints=set(quad)-{v,w}
            routes=[i for i,t in enumerate(trees) if t['source']==v and t['slit'] in endpoints]
            counts['sharper_source_cofacial_routes']+=1
            if max(margins[routes]) < -tol:
                counts['sharper_source_cofacial_route_failures']+=1
                failures.setdefault('sharper_source_cofacial',dict(**exact,source=v,trees=routes,
                    curvature_degrees=(k*180/np.pi).tolist(),net_margins=margins.tolist()))
        if 'sharp_slit' in failures:break
        if counts['samples']%5000==0:print(kind,dict(counts),flush=True)
    return dict(scope='Numerical hypothesis exploration only; all failures require exact replay.',kind=kind,
        seed=seed,sample_limit=samples,counts=dict(counts),attempts=attempts,seconds=time.monotonic()-start,
        tolerance=tol,trees=trees,failures=failures,worst=worst)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('kind',choices=SEEDS)
    ap.add_argument('--samples',type=int,default=20000);ap.add_argument('--seed',type=int,default=6091211)
    ap.add_argument('--seconds',type=float,default=90);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();report=run(args.kind,args.samples,args.seed,args.seconds)
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'counts':report['counts'],'failures':list(report['failures'])}))
