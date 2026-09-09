"""Numerical pattern discovery on the original octahedron-minus-edge surface.

Every numerical success or failure here is a proposal, not a proof. In
particular, saved cover witnesses need not be the only successful cut trees.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path
import time
import numpy as np
from n6.cover import read_cover, leaves
from n6.families import MINUS_FACES as FACES
from n6.trees import all_trees, incidence, degree_four_stars, quadrilateral_path_stars
from n6.original_star_probe import apex_curvature


class TreeBatch:
    """Develop all trees in batches; preserve full original polygonal faces."""
    def __init__(self, trees=None, faces=FACES):
        self.faces = faces
        self.width = max(map(len, faces))
        self.trees = all_trees(faces) if trees is None else trees
        self.padded = np.array([list(f)+[f[0]]*(self.width-len(f)) for f in faces])
        self.pairs = [(a,b) for a in range(len(faces)) for b in range(a+1,len(faces))]
        self.pair_mask = np.array([[p in t['pairs'] for p in self.pairs] for t in self.trees])
        transitions = []
        for owners in incidence(faces).values():
            for par,ch in (owners,owners[::-1]):
                f = faces[ch]
                a,b = next((a,b) for a,b in zip(f,f[1:]+f[:1]) if a in faces[par] and b in faces[par])
                transitions.append((par,ch,a,b,faces[par].index(a),faces[par].index(b)))
        self.transitions = transitions
        lookup = {(p,c):i for i,(p,c,*_) in enumerate(transitions)}
        levels = [[] for _ in range(len(faces)-1)]
        for ti,t in enumerate(self.trees):
            adj = {i:[] for i in range(len(faces))}
            for a,b in t['hinges']: adj[a].append(b); adj[b].append(a)
            seen = {0}; todo = [(0,0)]
            for par,depth in todo:
                for ch in adj[par]:
                    if ch in seen: continue
                    seen.add(ch); todo.append((ch,depth+1))
                    levels[depth].append((ti,lookup[par,ch]))
        self.levels = [np.array(x).T for x in levels if x]

    def nets(self, points):
        p = np.asarray(points,dtype=float)
        normals = np.array([np.cross(p[f[1]]-p[f[0]],p[f[2]]-p[f[0]]) for f in self.faces])
        normals /= np.linalg.norm(normals,axis=1)[:,None]
        coefficients = []
        for par,ch,a,b,pa,pb in self.transitions:
            e=p[b]-p[a]; v=p[self.padded[ch]]-p[a]; s=e@e
            coefficients.append(np.stack((v@e,np.cross(e,v)@normals[ch]),axis=1)/s)
        coefficients=np.array(coefficients)
        out=np.zeros((len(self.trees),len(self.faces),self.width,2))
        a,b=self.faces[0][:2]; ex=p[b]-p[a]; ex/=np.linalg.norm(ex)
        ey=np.cross(normals[0],ex)
        out[:,0]=np.stack(((p[self.padded[0]]-p[a])@ex,(p[self.padded[0]]-p[a])@ey),axis=1)
        trans=np.array(self.transitions)
        for ti,tr in self.levels:
            par,ch,_,_,pa,pb=trans[tr].T
            origin=out[ti,par,pa]; u=out[ti,par,pb]-origin
            ju=np.stack((-u[:,1],u[:,0]),axis=1)
            out[ti,ch]=origin[:,None,:]+coefficients[tr,:,0,None]*u[:,None,:]+coefficients[tr,:,1,None]*ju[:,None,:]
        return out

    def pair_scores(self, points):
        net=self.nets(points)
        a=net[:,[p[0] for p in self.pairs]]; b=net[:,[p[1] for p in self.pairs]]
        scores=[]
        for x,y in ((a,b),(b,a)):
            e=np.roll(x,-1,axis=2)-x; norm=np.linalg.norm(e,axis=-1)
            delta=y[:,:,None,:,:]-x[:,:,:,None,:]
            cross=e[:,:,:,None,0]*delta[...,1]-e[:,:,:,None,1]*delta[...,0]
            with np.errstate(divide='ignore',invalid='ignore'):
                values=np.max(cross,axis=-1)/norm
            values=np.where(norm>0,values,np.inf)
            scores.append(np.min(values,axis=-1))
        scores=np.minimum(*scores)
        return np.where(self.pair_mask,scores,-np.inf)

    def margins(self, points):
        return -np.max(self.pair_scores(points),axis=1)


def valid_points(points, tolerance=1e-11):
    """Floating strict-facet screening only, normalized by the diameter."""
    p=np.asarray(points,dtype=float)
    scale=np.max(np.linalg.norm(p[:,None]-p[None,:],axis=-1))
    if not np.isfinite(scale) or scale<=0: return None
    p=(p-p[0])/scale
    for f in FACES:
        n=np.cross(p[f[1]]-p[f[0]],p[f[2]]-p[f[0]]); length=np.linalg.norm(n)
        if length<1e-14: return None
        if max((p[v]-p[f[0]])@n/length for v in range(6) if v not in f)>=-tolerance: return None
    return p


def family_indices(trees):
    lookup={tuple(map(tuple,t['cuts'])):i for i,t in enumerate(trees)}
    stars=degree_four_stars(FACES); paths=quadrilateral_path_stars(FACES)
    out={'all':list(range(len(trees))), 'degree_four_stars':[lookup[tuple(t['cuts'])] for t in stars],
         'quad_paths':[lookup[tuple(t['cuts'])] for t in paths]}
    inc=incidence(FACES)
    for v in range(6):
        star={e for e in inc if v in e}
        out[f'full_star_{v}']=[i for i,t in enumerate(trees) if star<=set(t['cuts'])]
    for v in (0,1,4,5):out[f'apex_{v}']=[lookup[tuple(t['cuts'])] for t in stars if t['apex']==v]
    for u in (0,1):
        out[f'off_quad_pair_via_{u}']=[lookup[tuple(t['cuts'])] for t in stars
                                      if t['apex'] in (4,5) and t['slit_vertex']==u]
    return out


def canonical_points(points):
    """Euclidean similarity: the quadrilateral lies in z=0, P0=0, P1=(1,0,0)."""
    p=np.asarray(points,dtype=float);ex=p[1]-p[0];length=np.linalg.norm(ex);ex/=length
    z=np.cross(p[2]-p[0],p[1]-p[0]);z/=np.linalg.norm(z);y=np.cross(z,ex)
    q=(p-p[0])@np.array([ex,y,z]).T/length
    q[:4,2]=0;q[0]=0;q[1]=[1,0,0]
    return q


def selection_rules(p, curvature, trees, families):
    """Small geometry-based choices; each returned list is a candidate family."""
    lookup={tuple(t['cuts']):t for t in degree_four_stars(FACES)}
    four=max((0,1,4,5),key=lambda v:curvature[v]);quad=max((0,1),key=lambda v:curvature[v])
    ridge=max((4,5),key=lambda v:curvature[v]);sharp=max(range(6),key=lambda v:curvature[v])
    result={'sharpest_degree_four':families[f'apex_{four}'],
            'sharpest_quad_corner_paths':[i for i in families['quad_paths'] if i in families[f'apex_{quad}']],
            'sharpest_full_star':families[f'full_star_{sharp}'],
            'sharper_off_quad_apex':families[f'apex_{ridge}'],
            'off_quad_apices':families['apex_4']+families['apex_5']}
    for u in (0,1):
        result[f'off_quad_pair_via_{u}/sharper_apex']=[i for i in families[f'off_quad_pair_via_{u}']
                                                    if i in families[f'apex_{ridge}']]
    for name,v in [(f'apex_{v}',v) for v in (0,1,4,5)]+[('sharpest_degree_four',four),('sharper_off_quad',ridge)]:
        indices=families[f'apex_{v}']
        options={i:lookup[tuple(trees[i]['cuts'])] for i in indices}
        def distance(a,b):return float(np.linalg.norm(p[a]-p[b]))
        rules={
            'sharpest_slit':lambda t:curvature[t['slit_vertex']],
            'longest_slit':lambda t:distance(t['antipode'],t['slit_vertex']),
            'farthest_from_apex':lambda t:distance(t['apex'],t['slit_vertex']),
            'shortest_boundary_route':lambda t:-distance(t['apex'],t['slit_vertex'])-distance(t['antipode'],t['slit_vertex']),
        }
        for rule,key in rules.items():result[f'{name}/{rule}']=[max(indices,key=lambda i:key(options[i]))]
    return result


def cover_centers():
    cover=read_cover(Path('n6/results/minus-merged-cover.certificate.json.gz'))
    for node,box,depth in leaves(cover):
        center=[(Fraction(a)+Fraction(b))/2 for a,b in box]
        def evaluate(raw):
            total=Fraction(0)
            for c,powers in raw:
                value=Fraction(c)
                for x,k in zip(center,powers):value*=x**k
                total+=value
            return float(total)
        yield np.array([[evaluate(q) for q in p] for p in cover['geometry']['coordinate_polynomials']])


def random_points(rng, index):
    """Mixture of roof shapes and perspective/affine distortions; not exhaustive."""
    if index%3==0:
        p=np.array([[0.,0,0],[1,1,0],[1,0,0],[0,1,0],[.75,.25,-1],[.25,.75,-1]])
        p[1:, :2]+=rng.normal(0,.3,(5,2));p[4:,2]=-10**rng.uniform(-1,1,2)
    else:
        a,c=rng.uniform(-2,3,2); b,d=10**rng.uniform(-1.5,1.5,2)
        if not 0<(a*d+b*c)/(b+d)<1:return None
        p=np.array([[0.,0,0],[1,0,0],[a,-b,0],[c,d,0],[0,0,0],[0,0,0]])
        for v,tri in ((4,[0,2,1]),(5,[0,1,3])):
            weights=rng.dirichlet([.5]*3)
            p[v]=weights@p[tri];p[v,2]=-10**rng.uniform(-1.5,1.5)
    p=valid_points(p)
    if p is None:return None
    # A positive affine denominator keeps faces planar under perspective.
    direction=rng.normal(size=3); heights=p@direction
    distance=10**rng.uniform(-3,1)*(heights.max()-heights.min())
    p=p/(heights-heights.min()+distance)[:,None]
    transform=rng.normal(size=(3,3)); u,_,v=np.linalg.svd(transform)
    transform=u@np.diag(10**rng.uniform(-1.5,1.5,3))@v
    if np.linalg.det(transform)<0:transform[0]*=-1
    p=p@transform.T
    return valid_points(p)


def run(mode, samples, seconds, seed, output):
    batch=TreeBatch(); families=family_indices(batch.trees);rng=np.random.default_rng(seed)
    count=attempts=0;start=time.monotonic();success=np.zeros(len(batch.trees),int)
    failures=Counter();worst={};min_success=len(batch.trees);selected=[]
    source=iter(cover_centers()) if mode=='centers' else None
    while count<samples and time.monotonic()-start<seconds:
        if source is not None:
            p=next(source,None)
            if p is None:break
            p=valid_points(p)
        else:p=random_points(rng,attempts)
        attempts+=1
        if p is None:continue
        margins=batch.margins(p);count+=1;success+=margins>1e-9
        min_success=min(min_success,int(sum(margins>1e-9)))
        curvature=[apex_curvature(p,FACES,v) for v in range(6)]
        dynamic=selection_rules(p,curvature,batch.trees,families)
        for name,indices in {**families,**dynamic}.items():
            margin=float(max(margins[indices]))
            if margin < -1e-8:failures[name]+=1
            if name not in worst or margin<worst[name]['margin']:
                worst[name]={'margin':margin,'points':p.tolist(),'indices':indices,'curvatures':curvature,
                             'margins':margins[indices].tolist(),'best_all_tree':int(np.argmax(margins))}
        selected.append(np.packbits(margins>1e-9).tolist())
        if count%100==0:print(json.dumps({'samples':count,'seconds':time.monotonic()-start,'failures':dict(failures)}),flush=True)
    result={'scope':'Numerical exploration only; no universal claim or exact certificate.',
            'mode':mode,'seed':seed,'samples':count,'attempts':attempts,'seconds':time.monotonic()-start,
            'trees':batch.trees,'families':families,'success_counts':success.tolist(),
            'minimum_successful_trees':min_success,'failure_counts':dict(failures),'worst':worst,
            'successful_tree_masks_packbits':selected,'thresholds':{'success':1e-9,'failure':-1e-8}}
    write_report(output,result)
    return {k:v for k,v in result.items() if k not in ('trees','worst','successful_tree_masks_packbits')}


def write_report(output,result):
    """Keep one packed success mask per line so numerical corpora stay readable."""
    key='successful_tree_masks_packbits'
    payload=json.dumps({**result,key:[]},indent=2)
    rows=',\n'.join('    '+json.dumps(row,separators=(',',':')) for row in result[key])
    payload=payload.replace('"'+key+'": []','"'+key+'": [\n'+rows+'\n  ]')
    output.write_text(payload+'\n')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--mode',choices=('centers','random'),default='centers')
    ap.add_argument('--samples',type=int,default=409)
    ap.add_argument('--seconds',type=float,default=300)
    ap.add_argument('--seed',type=int,default=6090920)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    print(json.dumps(run(args.mode,args.samples,args.seconds,args.seed,args.output),indent=2))
