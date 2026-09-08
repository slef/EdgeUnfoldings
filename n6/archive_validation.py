"""Focused independent checks of the polynomial unfolding encoding."""
import itertools,json,math
import numpy as np
import networkx as nx
import z3
from n6.encoding import Counterexample,dual_trees,faces_and_dual


def numeric_model(ce,p):
    vals={}
    for i in ce.g:
        for j in range(3):
            t=ce.x[i][j]
            if z3.is_const(t) and t.decl().kind()==z3.Z3_OP_UNINTERPRETED:
                vals[t.decl().name()]=float(p[i][j])
    for k,f in enumerate(ce.faces):
        vals[f'h{k}']=float(np.linalg.norm(np.cross(p[f[1]]-p[f[0]],p[f[2]]-p[f[0]])))
    return vals


def evaluate(expr,vals,memo):
    if isinstance(expr,(int,float)):return expr
    key=expr.get_id()
    if key in memo:return memo[key]
    if z3.is_rational_value(expr):ans=expr.numerator_as_long()/expr.denominator_as_long()
    elif z3.is_true(expr):ans=True
    elif z3.is_false(expr):ans=False
    elif not expr.num_args():ans=vals[expr.decl().name()]
    else:
        a=[evaluate(x,vals,memo) for x in expr.children()];op=expr.decl().name()
        if op=='+':ans=sum(a)
        elif op=='*':ans=math.prod(a)
        elif op=='-':ans=-a[0] if len(a)==1 else a[0]-sum(a[1:])
        elif op=='and':ans=all(a)
        elif op=='or':ans=any(a)
        elif op=='=':ans=a[0]==a[1]
        elif op=='>':ans=a[0]>a[1]+1e-9*max(1,abs(a[0]),abs(a[1]))
        elif op=='<':ans=a[0]<a[1]-1e-9*max(1,abs(a[0]),abs(a[1]))
        else:raise ValueError(op)
    memo[key]=ans;return ans


def reference_development(ce,p,t):
    faces=ce.faces;placed={};root=0;f=faces[root];a,b=f[:2]
    e=p[b]-p[a];ell=np.linalg.norm(e)
    placed[root]={v:np.array([np.dot(e,p[v]-p[a])/ell,
                             np.linalg.norm(np.cross(e,p[v]-p[a]))/ell]) for v in f}
    for par,ch in nx.bfs_edges(t,root):
        f=faces[ch];old=placed[par];shared=set(f)&set(faces[par])
        a,b=next((a,b) for a,b in zip(f,f[1:]+f[:1]) if a in shared and b in shared)
        e=p[b]-p[a];s=np.dot(e,e);u=old[b]-old[a];ju=np.array([-u[1],u[0]])
        placed[ch]={v:old[a]+np.dot(e,p[v]-p[a])/s*u+
                    np.linalg.norm(np.cross(e,p[v]-p[a]))/s*ju for v in f}
    return [np.array([placed[i][v] for v in f]) for i,f in enumerate(faces)]


def cross2(a,b):return a[0]*b[1]-a[1]*b[0]


def clipped_area(A,B):
    output=[q.copy() for q in A]
    for c,d in zip(B,np.roll(B,-1,axis=0)):
        old=output;output=[]
        if not old:return 0.
        u=old[-1];fu=cross2(d-c,u-c)
        for v in old:
            fv=cross2(d-c,v-c)
            if (fu>=0)!=(fv>=0):output.append(u+(v-u)*(fu/(fu-fv)))
            if fv>=0:output.append(v)
            u,fu=v,fv
    if len(output)<3:return 0.
    return abs(sum(cross2(output[i],output[(i+1)%len(output)]) for i in range(len(output))))/2


def main():
    records=[]
    for name,coords in [('right',[(0,0,0),(1,0,0),(0,1,0),(0,0,-1)]),
                        ('skew',[(0,0,0),(1,0,0),(3,1,0),(10,1,-1)])]:
        ce=Counterexample(nx.complete_graph(4));a,b,c=ce.faces[0];d=next(v for v in ce.g if v not in (a,b,c))
        p=np.empty((4,3));p[[a,b,c,d]]=coords;vals=numeric_model(ce,p);memo={}
        nbad=0
        for t in dual_trees(ce.g,ce.dual):
            expr=ce.bad_tree(t);encoded=evaluate(expr,vals,{})
            ps=reference_development(ce,p,t)
            reference=any(clipped_area(A,B)>1e-9 for A,B in itertools.combinations(ps,2))
            assert encoded==reference,(name,list(t.edges()),encoded,reference)
            nbad+=reference
        records.append(dict(case=name,trees=16,overlapping=nbad,comparison='independent polygon clipping; floating-point validation only'))
    assert records[0]['overlapping']==0
    assert records[1]['overlapping']>0
    # Validate the SMT2 DAG writer by round-tripping a small nonlinear query.
    from n6.encoding import export_smt2
    x=z3.Real('test_x');s=z3.SolverFor('QF_NRA');s.add(x*x==2,x>0)
    export_smt2(s.assertions(),'validation-query.smt2')
    other=z3.SolverFor('QF_NRA');other.from_file('validation-query.smt2');assert other.check()==z3.sat
    records.append(dict(case='SMT2 exporter',result='round-trip SAT for positive square root of 2'))
    print(json.dumps(records,indent=2));open('validation-results.json','w').write(json.dumps(records,indent=2)+'\n')

if __name__=='__main__':main()
