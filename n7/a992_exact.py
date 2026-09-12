"""Rational, outward-rounded certificates for a *specified* N7-A992 shape.

No floating predicate is trusted. A successful net uses published / written
pair lemmas plus strictly certified separators for the residual pairs.
This is a small reproducible checker, not Lean or a universal graph proof.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
import itertools as it
import json
from pathlib import Path
import networkx as nx
from n7.catalogue import pair_audit

FACES=((0,3,2,4),(0,3,6),(0,4,6),(1,3,5),(1,3,6),(1,5,2,4,6),(2,3,5))
EDGES=sorted({tuple(sorted((u,f[(i+1)%len(f)]))) for f in FACES for i,u in enumerate(f)})
T=((0,3),(0,4),(1,3),(2,3),(3,5),(3,6))
T_OTHER=((0,3),(1,3),(2,3),(2,4),(3,5),(3,6))
V=((0,3),(0,4),(1,5),(1,6),(2,4),(4,6))
ROOT=Path(__file__).resolve().parent
BITS=160
S=1<<BITS

@dataclass(frozen=True)
class I:
    """Integer endpoints in units 2^-160; every nonlinear operation rounds out."""
    lo:int
    hi:int
    def __post_init__(self):
        if self.lo>self.hi:raise ValueError('Reversed interval')
    @staticmethod
    def bounds(lo,hi=None):
        lo=F(lo);hi=lo if hi is None else F(hi)
        return I((lo*S).__floor__(),(hi*S).__ceil__())
    def __add__(self,o):
        o=o if isinstance(o,I) else I.bounds(o)
        return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-(o if isinstance(o,I) else I.bounds(o))
    def __rsub__(self,o):return I.bounds(o)+-self
    def __mul__(self,o):
        o=o if isinstance(o,I) else I.bounds(o)
        vals=[a*b for a in (self.lo,self.hi) for b in (o.lo,o.hi)]
        return I(min(vals)//S,-(-max(vals)//S))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=o if isinstance(o,I) else I.bounds(o)
        if o.lo<=0<=o.hi:raise ValueError('Division through zero')
        return self*I(S*S//o.hi,-(-S*S//o.lo))
    def sqrt(self):
        if self.lo<0:raise ValueError('Uncertified nonnegative square root')
        a=isqrt(self.lo*S);b=isqrt(self.hi*S)
        return I(a,b+(b*b<self.hi*S))
    def export(self):return [str(F(self.lo,S)),str(F(self.hi,S))]
    def mid(self):return float(F(self.lo+self.hi,2*S))

def sub(a,b):return [x-y for x,y in zip(a,b)]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]]
def cross2(a,b):return a[0]*b[1]-a[1]*b[0]
def points(q):
    x6,y6,x1,y1,x5,y5,x3,y3,z3,a,b=q
    return [[a*x3+b,a*y3,a*z3],[x1,y1,0],[0,0,0],[x3,y3,z3],[1,0,0],[x5,y5,0],[x6,y6,0]]

def geometry(q,epsilon=F(0)):
    q=list(map(F,q));epsilon=F(epsilon)
    if epsilon<0:raise ValueError('Negative radius')
    exact=points(q)
    p=points([I.bounds(x-epsilon,x+epsilon) for x in q])
    p=[[x if isinstance(x,I) else I.bounds(x) for x in v] for v in p]
    supports=[];corners=[]
    for fi,f in enumerate(FACES):
        a,b,c=[exact[v] for v in f[:3]];n=cross(sub(b,a),sub(c,a))
        # Both polygon planes persist identically in the parameterization:
        # P is z=0 and Q is span(P3,P4), with P2=0 and P0=a P3+b P4.
        if any(dot(n,sub(exact[v],a))!=0 for v in f):raise ValueError('Nonplanar face')
        aa,bb,cc=[p[v] for v in f[:3]];nn=cross(sub(bb,aa),sub(cc,aa))
        rest=[v for v in range(7) if v not in f]
        val=dot(n,sub(exact[rest[0]],a));sgn=1 if val>0 else -1
        for v in rest:
            x=sgn*dot(nn,sub(p[v],aa))
            if x.lo<=0:raise ValueError('Strict facet support not certified')
            supports.append({'face':fi,'other_vertex':v,'sign':sgn,'bound':x.export()})
        for i,v in enumerate(f):
            x=dot(cross(sub(p[f[(i+1)%len(f)]],p[v]),sub(p[f[(i+2)%len(f)]],p[f[(i+1)%len(f)]])),nn)
            if x.lo<=0:raise ValueError('Strict convex corner not certified')
            corners.append({'face':fi,'vertex':v,'bound':x.export()})
    return p,{'parameters':list(map(str,q)),'parameter_half_width':str(epsilon),
              'center_points':[[str(x) for x in v] for v in exact],
              'planarity':'Exact identities P: z=0; Q: span(P3,P4), P2=0, P0=a P3+b P4.',
              'supports':supports,'corners':corners}

def develop(p,cut):
    cut={tuple(sorted(e)) for e in cut}
    if len(cut)!=6 or not cut<=set(EDGES) or not nx.is_tree(nx.Graph(list(cut))):raise ValueError('Not an original-edge spanning tree')
    ef={}
    for i,f in enumerate(FACES):
        for k,u in enumerate(f):ef.setdefault(tuple(sorted((u,f[(k+1)%len(f)]))),[]).append(i)
    adj=[[] for _ in FACES]
    for (a,b),ids in ef.items():
        if (a,b) not in cut:
            i,j=ids;adj[i].append((j,a,b));adj[j].append((i,a,b))
    placed={5:{v:p[v][:2] for v in FACES[5]}};queue=[5]
    for parent in queue:
        for child,a,b in adj[parent]:
            if child in placed:continue
            A,B=placed[parent][a],placed[parent][b];d=sub(B,A);perp=[-d[1],d[0]]
            other=next(v for v in FACES[parent] if v not in (a,b))
            side=cross2(d,sub(placed[parent][other],A))
            if side.lo>0:perp=[-x for x in perp]
            elif side.hi>=0:raise ValueError('Parent side indeterminate')
            L2=dot(sub(p[b],p[a]),sub(p[b],p[a]));new={a:A,b:B}
            for v in FACES[child]:
                if v in new:continue
                da=dot(sub(p[v],p[a]),sub(p[v],p[a]));db=dot(sub(p[v],p[b]),sub(p[v],p[b]))
                D=da-db+L2;t=D/(2*L2);h=(4*L2*da-D*D).sqrt()/(2*L2)
                new[v]=[A[j]+t*d[j]+h*perp[j] for j in range(2)]
            placed[child]=new;queue.append(child)
    if len(placed)!=7:raise ValueError('Disconnected dual')
    return [[placed[i][v] for v in f] for i,f in enumerate(FACES)]

def inside(poly,w):
    w=[I.bounds(x) for x in w];out=[]
    for a,b in zip(poly,poly[1:]+poly[:1]):out.append(cross2(sub(b,a),sub(w,a)))
    if all(x.lo>0 for x in out):sgn=1
    elif all(x.hi<0 for x in out):sgn=-1
    else:raise ValueError('Strict interior point not certified')
    return [ (sgn*x).export() for x in out]

def separating_axis(a,b):
    # A strictly separated projection is enough; candidate axes may themselves
    # vary within the box. Uniform interval bounds prove the desired inequality.
    for poly in (a,b):
        for k,(x,y) in enumerate(zip(poly,poly[1:]+poly[:1])):
            d=sub(y,x);n=[-d[1],d[0]];aa=[dot(v,n) for v in a];bb=[dot(v,n) for v in b]
            for left,right,direction in ((aa,bb,1),(bb,aa,-1)):
                gap=min(v.lo for v in right)-max(v.hi for v in left)
                if gap>0:return {'axis_polygon':0 if poly is a else 1,'edge_index':k,'direction':direction,'gap_lower_bound':str(F(gap,S))}
    raise ValueError('No strict separator certified')

def audit_for(cut):
    data=json.loads((ROOT/'results/catalogue.json').read_text());row=next(r for r in data['graphs'] if r['atlas_index']==992)
    key={tuple(sorted(e)) for e in cut}
    matches=[c for c in row['cofacial_candidates'] if {tuple(e) for e in c['cut']}==key]
    cand=min(matches,key=lambda c:len(c['audit']['unresolved'])) if matches else None
    return pair_audit(nx.Graph(EDGES),FACES,cut,cand)

def certificate(q,failed_cut=T,pair=(0,1),witness=None,successful_cut=T_OTHER,epsilon=F(0)):
    p,g=geometry(q,epsilon);bad=develop(p,failed_cut)
    if witness is None:raise ValueError('A rational witness point is required')
    proof=[inside(bad[i],witness) for i in pair]
    result={'kind':'exact_outward_rational_interval_certificate','arithmetic_bits':BITS,
      'scope':'A specified rational shape or parameter box only. Not a universal graph theorem or a proof-assistant artifact.',
      'geometry':g,'failed_cut':failed_cut,'overlapping_faces':pair,'interior_witness':list(map(str,witness)),'strict_interior_bounds':proof}
    if successful_cut is not None:
        good=develop(p,successful_cut);audit=audit_for(successful_cut);seps=[]
        for r in audit['unresolved']:
            i,j=r['faces'];seps.append({'faces':[i,j],**separating_axis(good[i],good[j])})
        result['successful_cut']=successful_cut;result['successful_pair_audit']=audit;result['residual_separators']=seps
    return result



def corner_six_signs(p):
    """Certify R6 without evaluating trigonometric functions.

    A negative signed corner of the developed patch proves e6 > pi.
    The other signs prove beta > pi/2 and 0 < h < pi/2; see A992_CONES.md.
    """
    net=develop(p,T)
    v4,v0,v6=net[2][1],net[2][0],net[2][2]
    v3=net[1][1]
    orientation=cross2(sub(v0,v4),sub(v6,v4))
    if orientation.lo>0:sgn=1
    elif orientation.hi<0:sgn=-1
    else:raise ValueError('Patch orientation not certified')
    inward=-sgn*cross2(sub(v6,v3),sub(v4,v6))
    obtuse=-dot(sub(p[4],p[3]),sub(p[0],p[3]))
    u,v,w=sub(p[2],p[4]),sub(p[6],p[4]),sub(p[0],p[4])
    a,b=dot(u,v),dot(v,w)
    uv,vw=cross(u,v),cross(v,w)
    c,d=dot(uv,uv).sqrt(),dot(vw,vw).sqrt()
    vals={'inward_corner_6':inward,'negative_dot_at_3':obtuse,
          'cos_h_positive_numerator':a*b-c*d,
          'sin_h_positive_numerator':c*b+a*d}
    if any(x.lo<=0 for x in vals.values()):raise ValueError('R6 signs not certified')
    return {k:x.export() for k,x in vals.items()}


def replay_saved():
    """Recompute every geometric sign; saved margins are outputs, never premises."""
    def replay_one(c):
        g=c['geometry']
        fresh=certificate(g['parameters'],c['failed_cut'],c['overlapping_faces'],
            [F(x) for x in c['interior_witness']],c.get('successful_cut'),F(g['parameter_half_width']))
        for k,v in fresh.items():
            if json.loads(json.dumps(v))!=c[k]:raise AssertionError('Certificate mismatch: '+k)
        return geometry(g['parameters'],F(g['parameter_half_width']))[0]
    first=json.loads((ROOT/'results/a992-exact-counterexample.json').read_text());replay_one(first)
    old=json.loads((ROOT/'results/a992-quadrilateral-repair-box.json').read_text());replay_one(old)
    second=json.loads((ROOT/'results/a992-length-rule-counterexample.json').read_text());p=replay_one(second)
    diff=dot(sub(p[3],p[6]),sub(p[3],p[6]))-dot(sub(p[0],p[6]),sub(p[0],p[6]))
    assert diff.lo>0 and diff.export()==second['length_squared_36_minus_06']
    both=json.loads((ROOT/'results/a992-two-source3-counterexample.json').read_text())
    assert len(both['failures'])==2
    assert both['failures'][0]['geometry']==both['failures'][1]['geometry']
    for c in both['failures']:p=replay_one(c)
    good=develop(p,both['successful_cut']);audit=audit_for(both['successful_cut']);seps=[]
    for r in audit['unresolved']:
        i,j=r['faces'];seps.append({'faces':[i,j],**separating_axis(good[i],good[j])})
    assert json.loads(json.dumps(audit))==both['successful_pair_audit']
    assert seps==both['residual_separators']
    sharp=json.loads((ROOT/'results/a992-corner-six-counterexample.json').read_text())
    p=replay_one(sharp)
    assert corner_six_signs(p)==sharp['R6_sign_bounds']
    return {'certified_overlap_tests':6,'certified_successful_nets':5,
            'counterexample_box_parameters':11,'counterexample_box_half_width':first['geometry']['parameter_half_width'],
            'universal_graph_status':'open'}

if __name__=='__main__':
    print(json.dumps(replay_saved(),indent=2))
