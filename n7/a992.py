"""Isolated floating discovery and drawing tools for N7-A992.

Floating searches discover candidates only; they are never universal proofs.
"""
from __future__ import annotations
import argparse
import itertools as it
import json
import math
from pathlib import Path
import random
import numpy as np
from n7.catalogue import edge

ROOT=Path(__file__).resolve().parent
FACES=((0,3,2,4),(0,3,6),(0,4,6),(1,3,5),(1,3,6),(1,5,2,4,6),(2,3,5))
EDGES=sorted(set(e for f in FACES for e in (edge(f[i],f[(i+1)%len(f)]) for i in range(len(f)))))
T=((0,3),(0,4),(1,3),(2,3),(3,5),(3,6))
T_OTHER=((0,3),(1,3),(2,3),(2,4),(3,5),(3,6))

def points_from_parameters(q):
    # P2=(0,0,0), P4=(1,0,0), base P6,P1,P5 are planar.
    # P0=a*P3+b*P4 preserves the quadrilateral exactly.
    x6,y6,x1,y1,x5,y5,x3,y3,z3,a,b=q
    p=np.array([[a*x3+b,a*y3,a*z3],[x1,y1,0],[0,0,0],[x3,y3,z3],[1,0,0],[x5,y5,0],[x6,y6,0]],float)
    return p

def valid(p,tol=1e-9):
    scale=max(1.,np.ptp(p,axis=0).max())
    for f in FACES:
        a,b,c=p[list(f[:3])];n=np.cross(b-a,c-a);norm=np.linalg.norm(n)
        if norm<tol*scale*scale:return False
        n=n/norm
        if max(abs((p[i]-a)@n) for i in f)>tol*scale:return False
        signs=[(p[i]-a)@n for i in range(7) if i not in f]
        if not (min(signs)>tol*scale or max(signs)<-tol*scale):return False
        corners=[np.cross(p[f[(i+1)%len(f)]]-p[f[i]],p[f[(i+2)%len(f)]]-p[f[(i+1)%len(f)]])@n for i in range(len(f))]
        if min(corners)<=tol*scale*scale:return False
    return True

def unfold(p,cut=T,faces=FACES,root=5):
    es={edge(*e) for e in cut};ef={}
    for i,f in enumerate(faces):
        for k,u in enumerate(f):ef.setdefault(edge(u,f[(k+1)%len(f)]),[]).append(i)
    adj=[[] for _ in faces]
    for (a,b),ids in ef.items():
        if len(ids)==2 and (a,b) not in es:
            i,j=ids;adj[i].append((j,a,b));adj[j].append((i,a,b))
    f=faces[root];a,b,c=p[list(f[:3])];e=(b-a)/np.linalg.norm(b-a);n=np.cross(b-a,c-a);n/=np.linalg.norm(n);perp=np.cross(n,e)
    placed={root:{v:np.array([(p[v]-a)@e,(p[v]-a)@perp]) for v in f}};queue=[root]
    for parent in queue:
        for child,a,b in adj[parent]:
            if child in placed:continue
            A,B=placed[parent][a],placed[parent][b];e=(B-A)/np.linalg.norm(B-A);perp=np.array([-e[1],e[0]])
            other=next(v for v in faces[parent] if v not in (a,b))
            if (placed[parent][other]-A)@perp>0:perp=-perp
            L=np.linalg.norm(p[b]-p[a]);new={a:A,b:B}
            for v in faces[child]:
                if v in new:continue
                da=(p[v]-p[a])@(p[v]-p[a]);db=(p[v]-p[b])@(p[v]-p[b]);x=(da-db+L*L)/(2*L)
                y=math.sqrt(max(0,da-x*x));new[v]=A+x*e+y*perp
            placed[child]=new;queue.append(child)
    if len(placed)!=len(faces):raise ValueError('Disconnected uncut dual')
    return [np.array([placed[i][v] for v in f]) for i,f in enumerate(faces)]

def penetration(a,b):
    answer=float('inf')
    for poly in (a,b):
        for x,y in zip(poly,np.roll(poly,-1,axis=0)):
            e=y-x;n=np.array([-e[1],e[0]])/np.linalg.norm(e)
            aa=a@n;bb=b@n;answer=min(answer,min(max(aa),max(bb))-max(min(aa),min(bb)))
    return float(answer)

def sample(rng):
    # Perturb a convex base; sample roof height and the coplanar extra corner.
    base=[1+rng.uniform(-.8,.8),10**rng.uniform(-.7,.7),rng.uniform(-.5,1.0),10**rng.uniform(-.1,.8),rng.uniform(-1.5,.3),10**rng.uniform(-.8,.5)]
    top=[rng.uniform(-2,3),rng.uniform(-2,3),10**rng.uniform(-2,1)]
    a=10**rng.uniform(-1.5,.6);b=10**rng.uniform(-1.5,.6)
    return base+top+[a,b]

def survey(count=2000,seed=992):
    rng=random.Random(seed);seen=0;attempts=0;best=None;failures=[]
    while seen<count and attempts<100*count:
        attempts+=1;q=sample(rng);p=points_from_parameters(q)
        if not valid(p):continue
        seen+=1;net=unfold(p);score=penetration(net[0],net[1])/max(1,np.ptp(p,axis=0).max())
        row={'parameters':q,'points':p.tolist(),'normalized_pair_penetration':score}
        if best is None or score>best['normalized_pair_penetration']:best=row
        if score>1e-8:
            failures.append(row)
            if len(failures)>=5:break
    return {'scope':'Numerical discovery only; no proof of a point or universal rule.', 'attempted':attempts,'valid':seen,'failures':failures,'best':best}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--samples',type=int,default=2000);p.add_argument('--output',type=Path,default=ROOT/'results/a992-survey.json');args=p.parse_args()
    result=survey(args.samples);args.output.write_text(json.dumps(result,indent=2)+'\n');print({k:result[k] for k in ['attempted','valid']}, 'failures',len(result['failures']), 'best',result['best']['normalized_pair_penetration'] if result['best'] else None)

def intersection_polygon(a,b):
    """Floating convex clipping for figures / discovery, never a proof predicate."""
    result=[np.asarray(v) for v in a]
    cross2=lambda x,y: x[0]*y[1]-x[1]*y[0]
    signed=sum(cross2(b[(i+1)%len(b)]-b[i],b[(i+2)%len(b)]-b[(i+1)%len(b)]) for i in range(len(b)))
    sign=1 if signed>0 else -1
    for x,y in zip(b,np.roll(b,-1,axis=0)):
        old=result;result=[]
        if not old:break
        d=y-x
        for A,B in zip(old,old[1:]+old[:1]):
            sa=sign*cross2(d,A-x);sb=sign*cross2(d,B-x)
            if sa>=0:result.append(A)
            if (sa<0<sb) or (sb<0<sa):result.append(A+sa/(sa-sb)*(B-A))
    return np.array(result)
