"""Independent finite checks and rational box certificate for n7 arguments."""
from __future__ import annotations
import itertools as it
import json
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import networkx as nx
from n7.catalogue import facets, face_edges, pair_audit
ROOT=Path(__file__).resolve().parent

@dataclass(frozen=True)
class Interval:
    lo:F
    hi:F
    def __post_init__(self):
        if self.lo>self.hi:raise ValueError('Reversed interval')
    @staticmethod
    def point(x):return Interval(F(x),F(x))
    def __add__(self,o):
        if not isinstance(o,Interval):o=Interval.point(o)
        return Interval(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return Interval(-self.hi,-self.lo)
    def __sub__(self,o):return self+-o
    def __mul__(self,o):
        if not isinstance(o,Interval):o=Interval.point(o)
        vals=[a*b for a in (self.lo,self.hi) for b in (o.lo,o.hi)]
        return Interval(min(vals),max(vals))
    __rmul__=__mul__
    def export(self):return [str(self.lo),str(self.hi)]

def sub(a,b):return [x-y for x,y in zip(a,b)]
def dot(a,b):return sum((x*y for x,y in zip(a,b)),Interval.point(0))
def cross(a,b):return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]]

def acute_box(epsilon=F(1,1000)):
    coords=[[F(1),F(0),F(0)],[F(3,5),F(4,5),F(0)],[F(-3,5),F(4,5),F(0)],
            [F(-1),F(0),F(0)],[F(0),F(-1),F(0)],[F(0),F(0),F(1)],[F(0),F(0),F(-1)]]
    ps=[[Interval(c-epsilon,c+epsilon) for c in row] for row in coords]
    triangles=[(p,i,(i+1)%5) for p in (5,6) for i in range(5)]
    support=[];corners=[]
    for fi,tri in enumerate(triangles):
        a,b,c=[ps[i] for i in tri];n=cross(sub(b,a),sub(c,a))
        out=[i for i in range(7) if i not in tri]
        center=[[Interval.point(t) for t in row] for row in coords]
        aa,bb,cc=[center[i] for i in tri]
        val=dot(cross(sub(bb,aa),sub(cc,aa)),sub(center[out[0]],aa)).lo
        sign=1 if val>0 else -1
        for j in out:
            det=sign*dot(n,sub(ps[j],a))
            if det.lo<=0:raise ValueError('A supporting facet is not certified')
            support.append({'facet':fi,'other_vertex':j,'inward_sign':sign,'oriented_determinant':det.export()})
        for k,v in enumerate(tri):
            d=dot(sub(ps[tri[(k+1)%3]],ps[v]),sub(ps[tri[(k+2)%3]],ps[v]))
            if d.lo<=0:raise ValueError('An acute corner is not certified')
            corners.append({'facet':fi,'vertex':v,'dot_product':d.export()})
    return {'kind':'exact_rational_interval_hypothesis_certificate',
            'scope':'One explicit 21-coordinate box. All ten polestar-plus-slit trees are safe by the written all-convex-patches theorem; no universal graph or Lean certification.',
            'center':[[str(x) for x in row] for row in coords], 'half_width':str(epsilon),
            'facets':triangles,'support_count':len(support),'corner_count':len(corners),
            'minimum_support_lower_bound':str(min(F(x['oriented_determinant'][0]) for x in support)),
            'minimum_corner_lower_bound':str(min(F(x['dot_product'][0]) for x in corners)),
            'supports':support,'corners':corners}

def canonical_pattern(p):
    q=p[::-1].translate(str.maketrans('BF','FB'))
    return min([p[k:]+p[:k] for k in range(len(p))]+[q[k:]+q[:k] for k in range(len(p))])

def patch_patterns():
    families={}
    for p in it.product('CBF',repeat=5):
        if any(p[i]=='F' and p[(i+1)%5]=='B' for i in range(5)):continue
        if all(x=='F' for x in p) or all(x=='B' for x in p):continue
        p=''.join(p);families.setdefault(canonical_pattern(p),[]).append(p)
    proved={'CCCCC':'C','BCCCC':'One','BCCFC':'Toward','BCFCC':'Chain','BCBCC':'Separated','BFCCC':'Long-chain'}
    rows=[]
    for rep, members in sorted(families.items(),key=lambda kv:(5-kv[0].count('C'),kv[0])):
        rows.append({'representative':rep,'inward_count':5-rep.count('C'),'labelled_count':len(members),
                     'members':members,'status':'proved conditional family' if rep in proved else 'open',
                     'theorem':proved.get(rep), 'large_pole_theorem':'Shortest-patch replacement (either pole curvature at least pi)', 'extra_partial_theorem':'TwoGap (one pole curvature at least pi)' if rep=='BBCCC' else 'Receiver (weighted pole-curvature gate)' if rep in ('BCBCC','BCFCC','BFCCC') else None})
    return {'scope':'Necessary symbolic patterns; not every admitted pattern is asserted realizable. Counts are not fractions of metric space.',
            'labelled_count':sum(map(len,families.values())),'class_count':len(rows),'proved_classes':len(proved),'classes':rows}

def spanning_tree_count(g):
    # Rational Gaussian elimination of a Laplacian cofactor (Matrix Tree Theorem).
    vs=sorted(g)[:-1];a=[[F(g.degree(i) if i==j else -int(g.has_edge(i,j))) for j in vs] for i in vs]
    result=F(1)
    for k in range(len(a)):
        pivot=next((i for i in range(k,len(a)) if a[i][k]),None)
        if pivot is None:return 0
        if pivot!=k:a[k],a[pivot]=a[pivot],a[k];result=-result
        val=a[k][k];result*=val
        for i in range(k+1,len(a)):
            ratio=a[i][k]/val
            for j in range(k+1,len(a)):a[i][j]-=ratio*a[k][j]
    if result.denominator!=1:raise AssertionError('Noninteger tree count')
    return int(result)

def verify_catalogue(data):
    gs=data['graphs'];checks=0
    for row in gs:
        g=nx.from_graph6_bytes(row['graph6'].encode())
        assert sorted([list(sorted(e)) for e in g.edges()])==row['edges']
        assert sorted(map(list,facets(g)))==row['facets']
        assert len(g)==7 and nx.is_planar(g) and nx.node_connectivity(g)>=3
        assert spanning_tree_count(g)==row['all_tree_scan']['count']
        for c in row['cofacial_candidates']:
            assert nx.is_tree(nx.Graph(c['cut']))
            assert pair_audit(g,row['facets'],c['cut'],c)==c['audit'];checks+=1
        best=row['all_tree_scan']['best']
        assert pair_audit(g,row['facets'],best['cut'])==best['audit'];checks+=1
        assert row['status']==('solved' if row['universal_vertices'] or row['dome_bases'] else 'open')
    return {'graphs_checked':len(gs),'saved_candidate_audits_replayed':checks,
            'all_tree_count_independently_matched':sum(r['all_tree_scan']['count'] for r in gs),
            'solved_graphs':sum(r['status']=='solved' for r in gs),
            'open_graphs':sum(r['status']=='open' for r in gs),
            'scope':'Finite combinatorial verification plus stated geometric theorem dependencies; not proof-assistant verification.'}

def plantri_comparison(data, source):
    gs=data['graphs'];matches=[]
    lines=Path(source).read_text().splitlines()
    for line in lines:
        if not line or line.startswith('>>'):continue
        g=nx.from_graph6_bytes(line.encode());hit=[]
        for row in gs:
            matcher=nx.algorithms.isomorphism.GraphMatcher(g,nx.Graph(row['edges']))
            if matcher.is_isomorphic():hit.append((row['id'],dict(matcher.mapping)))
        assert len(hit)==1
        matches.append({'plantri_graph6':line,'atlas_id':hit[0][0],'vertex_mapping':hit[0][1]})
    assert len(matches)==len(gs)==34 and len({m['atlas_id'] for m in matches})==34
    return {'generator':'plantri 5.8','command':'plantri -pg 7 n7.g6',
            'source':'https://users.cecs.anu.edu.au/~bdm/plantri/plantri58.tar.gz',
            'archive_sha256':'e78a944116fec9f2c9f5e484206276cc2b0043bae803e9815f4b2683614629b8',
            'output_count':len(matches),'all_atlas_graphs_matched_once':True,'matches':matches}

def core_completions(data):
    sims=[r for r in data['graphs'] if r['simplicial']];rows=[]
    for r in data['graphs']:
        if r['cofacial_sources']:continue
        polys=[f for f in r['facets'] if len(f)>3]
        assert all(len(f)==4 for f in polys)
        completions=[]
        for diagonals in it.product(*[[(f[0],f[2]),(f[1],f[3])] for f in polys]):
            g=nx.Graph(r['edges']);g.add_edges_from(diagonals)
            targets=[s['id'] for s in sims if nx.is_isomorphic(g,nx.Graph(s['edges']))]
            assert len(targets)==1
            completions.append({'auxiliary_diagonals':diagonals,'completed_graph':targets[0],
                                'restriction':'Every inserted diagonal must stay uncut in an original-edge net.'})
        rows.append({'id':r['id'],'completions':completions})
    return rows

if __name__=='__main__':
    data=json.loads((ROOT/'results/catalogue.json').read_text())
    results={'validation.json':verify_catalogue(data),'patch-patterns.json':patch_patterns(),
             'acute-bipyramid-box.json':acute_box(),'core-completions.json':core_completions(data),
             'plantri-comparison.json':plantri_comparison(data,ROOT/'results/plantri.g6')}
    for name,content in results.items():(ROOT/'results'/name).write_text(json.dumps(content,indent=2)+'\n')
    print(json.dumps(results['validation.json'],indent=2))
    print('Patch classes:',results['patch-patterns.json']['class_count'])
    print('Positive exact corner margin:',results['acute-bipyramid-box.json']['minimum_corner_lower_bound'])
