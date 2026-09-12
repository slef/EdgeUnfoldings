"""Replay finite exact examples of the base-edge extension theorem.

The universal geometric argument is in A992_BASE_EDGES.md. The records here
verify two rational shapes, including an exact parallel-edge boundary.
"""
from fractions import Fraction as F
import json
from n7.a992_exact import ROOT,T,certificate,geometry,develop,points,sub,dot,cross,cross2
from n7.r0_examples import orientation_sign
RIGHT=((0,3),(0,4),(0,6),(1,3),(2,3),(3,5))
AUX_FACES=((0,3,6),(0,6,2),(0,2,3),(7,3,6),(7,6,2),(7,2,3))
AUX_CUT=((0,3),(0,6),(0,2),(3,7))

def extension_data(parameters):
    p=points(list(map(F,parameters)));C,D,U,V=(p[i] for i in (6,2,1,5))
    a,b=sub(U,C),sub(V,D);turn=cross2(a,b)
    if cross2(sub(C,D),a)<=0 or cross2(sub(C,D),b)<=0:
        raise ValueError('The base rays do not have the stated orientation')
    result={'hinge_determinant':str(turn),
            'classification':'converging' if turn<0 else 'parallel' if turn==0 else 'diverging',
            'negative_dot_angle603':str(-dot(sub(p[6],p[0]),sub(p[3],p[0])))}
    if turn<0:
        t=cross2(sub(D,C),b)/turn;s=cross2(sub(D,C),a)/turn
        if min(t,s)<=1:raise ValueError('Intersection is not beyond both original hinges')
        x=[c+t*d for c,d in zip(C,a)]
        if x!=[d+s*b_ for d,b_ in zip(D,b)]:raise AssertionError('Ray intersection mismatch')
        pp={i:p[i] for i in (0,2,3,6)};pp[7]=x;checks=[]
        for face in AUX_FACES:
            A,B,C0=[pp[v] for v in face];n=cross(sub(B,A),sub(C0,A))
            vals=[dot(n,sub(pp[v],A)) for v in pp if v not in face]
            if not(all(z>0 for z in vals) or all(z<0 for z in vals)):
                raise ValueError('An auxiliary facet is not strictly supporting')
            checks.append({'face':list(face),'strict_supports':list(map(str,vals))})
        result.update({'t':str(t),'s':str(s),'x':list(map(str,x)),'auxiliary_facets':checks})
    return result

def example_signs(parameters):
    out=extension_data(parameters)
    if out['classification']=='diverging':raise ValueError('Outside the proved base-edge subcase')
    if F(out['negative_dot_angle603'])<0:raise ValueError('Petal angle is acute')
    p,_=geometry(parameters);n=develop(p,T)
    A,B,C,D=n[2][1],n[2][0],n[1][1],n[2][2]
    orient=orientation_sign(cross2(sub(B,A),sub(D,A)))
    inward=-orient*cross2(sub(B,A),sub(C,B))
    if inward.lo<=0:raise ValueError('Inward corner at 0 is not certified')
    out['Left_inward_at_0']=inward.export()
    return out

def replay():
    saved=json.loads((ROOT/'results/a992-base-edge-examples.json').read_text())
    classes=[]
    for c in saved['examples']:
        g=c['geometry']
        fresh=certificate(g['parameters'],c['failed_cut'],c['overlapping_faces'],
            [F(x) for x in c['interior_witness']],c['successful_cut'],F(g['parameter_half_width']))
        for k,v in fresh.items():
            if json.loads(json.dumps(v))!=c[k]:raise AssertionError('Certificate mismatch: '+k)
        signs=example_signs(g['parameters'])
        if signs!=c['base_edge_signs']:raise AssertionError('Base-edge branch mismatch')
        classes.append(signs['classification'])
    if classes!=['converging','parallel']:raise AssertionError('Missing an intended branch example')
    return {'scope':'Two rational shapes only; the general proof is written separately.',
            'exact_classes':classes,'strict_Left_overlaps':2,
            'strict_Right_residual_separators':6,'whole_graph_status':'open'}

if __name__=='__main__':print(json.dumps(replay(),indent=2))
