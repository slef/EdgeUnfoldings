"""Exact, standard-library checks for four fixed nonconvex examples.

No convex hull reconstruction is used: the supplied face incidence is retained.
The n=6 angle obstructions use integer dot products, not numerical angles.
This checks fixed examples, not a universal unfoldability theorem.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
import json


def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def mul(t,a): return tuple(t*x for x in a)
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def cross(a,b): return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def norm2(a): return dot(a,a)
def edge(a,b): return tuple(sorted((a,b)))
def require(b,s):
    if not b: raise ValueError(s)
def incidence(fs):
    inc={}
    for i,f in enumerate(fs):
        for a,b in zip(f,f[1:]+f[:1]):inc.setdefault(edge(a,b),[]).append(i)
    return inc
def normal(t): return cross(sub(t[1],t[0]),sub(t[2],t[0]))
def inside(p,t):
    n=normal(t)
    return dot(n,sub(p,t[0]))==0 and all(dot(n,cross(sub(b,a),sub(p,a)))>=0 for a,b in zip(t,t[1:]+t[:1]))
def on_segment(p,a,b):
    d=sub(b,a)
    if norm2(d)==0:return p==a
    return norm2(cross(sub(p,a),d))==0 and 0<=dot(sub(p,a),d)<=norm2(d)


def intersections(a,b):
    """Vertices of the convex intersection of two nondegenerate triangles."""
    na,nb=normal(a),normal(b)
    out={p for p in a if inside(p,b)}|{p for p in b if inside(p,a)}
    if norm2(cross(na,nb))==0:
        if dot(na,sub(b[0],a[0]))!=0:return out
        # Coplanar edge crossings, expressed in 3D using the common normal.
        for p,q in zip(a,a[1:]+a[:1]):
            u=sub(q,p)
            for r,s in zip(b,b[1:]+b[:1]):
                v=sub(s,r); den=dot(na,cross(u,v))
                if den:
                    t=F(dot(na,cross(sub(r,p),v)),den)
                    z=F(dot(na,cross(sub(r,p),u)),den)
                    if 0<=t<=1 and 0<=z<=1:out.add(add(p,mul(t,u)))
                else:
                    for x in (p,q,r,s):
                        if on_segment(x,p,q) and on_segment(x,r,s):out.add(x)
    else:
        for t,other in ((a,b),(b,a)):
            n=normal(other)
            for p,q in zip(t,t[1:]+t[:1]):
                x=dot(n,sub(p,other[0]));y=dot(n,sub(q,other[0]))
                if x*y<0:
                    r=add(p,mul(F(x,x-y),sub(q,p)))
                    if inside(r,other):out.add(r)
    return out


def connected(vs,es):
    vs=set(vs)
    if not vs:return True
    seen={min(vs)}
    while True:
        nxt=seen|{b for a,b in es if a in seen}|{a for a,b in es if b in seen}
        if nxt==seen:return seen==vs
        seen=nxt


def verify_mesh(p,fs,original):
    """Embedded oriented triangulated sphere, with original graph 3-connected."""
    inc=incidence(fs)
    require(all(len(v)==2 for v in inc.values()),'two triangles per edge')
    directed=Counter((a,b) for f in fs for a,b in zip(f,f[1:]+f[:1]))
    require(all(n==1 and directed[b,a]==1 for (a,b),n in directed.items()),'coherent orientation')
    require(connected(p,inc),'connected surface graph')
    require(len(p)-len(inc)+len(fs)==2,'Euler characteristic two')
    for v in p:
        link=[tuple(x for x in f if x!=v) for f in fs if v in f]
        vertices={x for e in link for x in e}
        require(all(sum(x in e for e in link)==2 for x in vertices) and connected(vertices,link),'vertex link cycle')
    for removed_count in range(3):
        for removed in combinations(p,removed_count):
            rest=set(p)-set(removed)
            require(connected(rest,[e for e in original if set(e)<=rest]),'original graph 3-connected')
    triangles=[tuple(p[x] for x in f) for f in fs]
    require(all(norm2(normal(t))>0 for t in triangles),'nondegenerate triangles')
    for e in original:
        i,j=inc[e]
        require(norm2(cross(normal(triangles[i]),normal(triangles[j])))>0,'original edges have nonflat hinges')
    for (i,a),(j,b) in combinations(enumerate(triangles),2):
        common=[p[x] for x in fs[i] if x in fs[j]]
        for x in intersections(a,b):
            require((len(common)==1 and x==common[0]) or
                    (len(common)==2 and on_segment(x,*common)),f'extraneous face intersection {i}/{j}: {x}')
    return len(list(combinations(fs,2)))


P6={k:tuple(map(F,v)) for k,v in {
    'A':(-3000,0,0),'B':(0,-100,0),'C':(-1000,0,0),
    'D':(0,100,0),'E':(-800,-62,1),'F':(-800,62,1)}.items()}
F6=['CBA','ADC','ABE','AEF','AFD','BCE','CFE','CDF']
ORIGINAL6=['DCBA','ABE','AEF','AFD','BCE','CFE','CDF']
P5={k:tuple(map(F,v)) for k,v in {'A':(0,0,0),'B':(4,0,0),'C':(1,1,0),'D':(0,4,0),'P':(0,0,2)}.items()}
F5=['CBA','DCA','ABP','BCP','CDP','DAP']


def angle_data(p,a,b,c):
    u=sub(p[a],p[b]);v=sub(p[c],p[b])
    return dot(u,v),norm2(u)*norm2(v)


def verify_six():
    es=set(incidence(ORIGINAL6))
    require(set(incidence(F6))-es=={edge('A','C')},'only auxiliary diagonal AC')
    # The original quadrilateral is a disk, with C as its one reflex corner:
    # its two oriented triangles share AC and have no extraneous intersection.
    pair_checks=verify_mesh(P6,F6,es)
    n=normal(tuple(P6[x] for x in 'CBA'))
    turn=dot(n,cross(sub(P6['C'],P6['D']),sub(P6['B'],P6['C'])))
    require(turn<0,'quadrilateral DCBA reflex at C')
    midpoint_bd=mul(F(1,2),add(P6['B'],P6['D']))
    require(not any(inside(midpoint_bd,tuple(P6[x] for x in f)) for f in F6[:2]),'octahedral diagonal BD exits the original quadrilateral')
    # theta=minor angle BCD. Both cosines are positive, so squaring is safe.
    d,r=angle_data(P6,'B','C','E');e,s=angle_data(P6,'B','C','D')
    require(d>0 and e>0 and d*d*s<e*e*r,'angle BCE > theta: equation (9)')
    # Three angles at E exceed 150,150,60 degrees, respectively.
    angle_bounds=[]
    for triple in ['AEB','BEC']:
        d,r=angle_data(P6,*triple)
        require(d<0 and 4*d*d>3*r,f'{triple}>150 degrees')
        angle_bounds.append({'angle':triple,'lower_degrees':150,'integer_margin':str(4*d*d-3*r)})
    d,r=angle_data(P6,'C','E','F')
    require(d>0 and 4*d*d<r,'CEF>60 degrees')
    angle_bounds.append({'angle':'CEF','lower_degrees':60,'integer_margin':str(r-4*d*d)})
    # Hence E and (by reflection) F are negative; equation (9) makes C negative.
    require(all(P6[x]==(P6[y][0],-P6[y][1],P6[y][2]) for x,y in [('B','D'),('E','F')]),'reflection symmetry')
    counts=Counter();last=[]
    for t in combinations(sorted(es),5):
        if not connected(P6,t):continue
        counts['spanning_trees']+=1
        degree={v:sum(v in e for e in t) for v in P6}
        if any(degree[v]==1 for v in 'CEF'):
            counts['negative_curvature_leaf']+=1
        elif not {edge('B','C'),edge('C','D')}<=set(t):
            counts['forced_hinge_overlap']+=1
        else:
            bad_e=degree['E']==2 and {edge('A','E'),edge('E','F')}<=set(t)
            bad_f=degree['F']==2 and {edge('A','F'),edge('E','F')}<=set(t)
            require(bad_e or bad_f,'every remaining tree has the >360 degree E/F sector')
            counts['overfull_E_or_F_sector']+=1;last.append(t)
    require(counts=={'spanning_trees':224,'negative_curvature_leaf':194,'forced_hinge_overlap':26,'overfull_E_or_F_sector':4},'complete graph enumeration')
    # A,B,D cannot have zero curvature: use a small common-direction cone.
    # Each of their incident triangle angles is acute. At A the quadrilateral
    # splits into two triangles, so certify the original base angle separately.
    for v,triples in {'A':['DAB','BAE','EAF','FAD'],'B':['ABC','ABE','CBE'],'D':['ADC','ADF','CDF']}.items():
        require(all(angle_data(P6,*tri)[0]>0 for tri in triples),f'positive curvature at {v}')
    return {'mesh_triangle_pairs_checked':pair_checks,'octahedral_diagonal_BD_is_outside':True,'angle_lower_bounds':angle_bounds,
            'curvature_signs':{'A':'+','B':'+','C':'-','D':'+','E':'-','F':'-'},
            'tree_counts':dict(counts),'last_four_trees':last}


def verify_five():
    es=set(incidence(F5))-{edge('A','C')}
    checks=verify_mesh(P5,F5,es)
    n=normal(tuple(P5[x] for x in 'CBA'))
    require(dot(n,cross(sub(P5['C'],P5['D']),sub(P5['B'],P5['C'])))<0,'C is reflex in the base')
    require(angle_data(P5,'B','C','P')[0]<0 and angle_data(P5,'D','C','P')[0]<0,'both side angles at C exceed pi/2')
    # A reflex base angle > pi plus two obtuse side angles exceeds 2*pi.
    star={edge('P',v) for v in 'ABCD'}
    require(sum('C' in e for e in star)==1,'C is a leaf of the apex star')
    return {'mesh_triangle_pairs_checked':checks,'apex_star_cut_edges':sorted(star),
            'conclusion':'C has negative curvature; the apex star overlaps locally'}


def verify_reflected_bipyramid():
    p={k:tuple(map(F,v)) for k,v in {'A':(-1,-1,0),'B':(1,-1,0),'C':(0,1,0),'P':(0,0,3),'Q':(0,0,1)}.items()}
    fs=['PAB','PBC','PCA','QBA','QCB','QAC'];es=set(incidence(fs))
    require(verify_mesh(p,fs,es)==15,'nested bipyramid is embedded')
    weights={'P':F(1,3),'A':F(1,6),'B':F(1,6),'C':F(1,3)}
    q=tuple(sum(weights[v]*p[v][i] for v in weights) for i in range(3))
    require(q==p['Q'],'Q is strictly inside the tetrahedron PABC')
    convex=dict(p);convex['Q']=(F(0),F(0),F(-1))
    for f in fs:
        t=tuple(convex[v] for v in f);n=normal(t)
        require(all(dot(n,sub(convex[v],t[0]))<0 for v in set(p)-set(f)),'reflected face is strictly supporting')
    require(all(norm2(sub(p[a],p[b]))==norm2(sub(convex[a],convex[b])) for a,b in es),'all nine original edge lengths unchanged')
    require(p['P'][2]>0 and p['Q'][2]>0,'original pole segment misses z=0')
    return {'mesh_triangle_pairs_checked':15,'original_pole_segment_misses_equator_plane':True,
            'reflected_realization_strictly_convex':True,'original_edge_lengths_preserved':9,
            'conclusion':'the same face metric has a convex realization, so its equator-star nets transfer'}


def verify_two_saddles():
    p={k:tuple(map(F,v)) for k,v in {'A':(0,0,0),'B':(10,0,0),'C':(0,10,0),'P':(40,-40,1),'Q':(-10,-20,-5)}.items()}
    fs=['PAB','PBC','PCA','QBA','QCB','QAC'];es=set(incidence(fs))
    require(verify_mesh(p,fs,es)==15,'two-saddle bipyramid embedded')
    # At A the two P angles sum to pi (opposite cosines), and both Q angles
    # are obtuse. At B use strict lower bounds 120+150+90+0 = 360 degrees.
    x,r=angle_data(p,'B','A','P');y,s=angle_data(p,'C','A','P')
    require(x==-y and r==s,'P angles at A sum to pi')
    require(angle_data(p,'B','A','Q')[0]<0 and angle_data(p,'C','A','Q')[0]<0,'Q angles at A are obtuse')
    x,r=angle_data(p,'A','B','P');require(x<0 and 4*x*x>r,'ABP>120 degrees')
    x,r=angle_data(p,'C','B','P');require(x<0 and 4*x*x>3*r,'CBP>150 degrees')
    require(angle_data(p,'C','B','Q')[0]==0,'CBQ=90 degrees')
    for source in 'ABC':
        cuts={e for e in es if source in e}
        require(len(cuts)==4,'equator vertex universal')
        require(any(sum(v in e for e in cuts)==1 for v in 'AB'),'a negative-curvature vertex remains a leaf')
    return {'mesh_triangle_pairs_checked':15,'negative_curvature_vertices_certified':['A','B'],
            'all_three_equator_stars_fail_locally':True,
            'conclusion':'choosing a different universal vertex cannot repair the star rule in general'}


if __name__=='__main__':
    print(json.dumps({'scope':'four fixed examples; exact rational arithmetic',
                      'n5_pyramid':verify_five(),'n5_bipyramid':verify_reflected_bipyramid(),
                      'n5_two_saddles':verify_two_saddles(),'n6':verify_six()},indent=2))
