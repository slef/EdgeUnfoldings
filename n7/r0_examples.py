"""Replay an exact A992 example exercising the obtuse-petal proof's hard branch."""
from fractions import Fraction as F
import json
from n7.a992_exact import ROOT,I,geometry,develop,certificate,sub,dot,cross,cross2

def orientation_sign(value):
    if value.lo>0:return 1
    if value.hi<0:return -1
    raise ValueError('Orientation is not strict')

def branch_signs(p,left,right):
    a,b,d,z=right[4][0],right[1][1],right[1][0],right[1][2]
    sgn=orientation_sign(cross2(sub(b,a),sub(z,a)))
    inward=-sgn*cross2(sub(z,d),sub(a,z))
    obtuse=-dot(sub(p[3],p[0]),sub(p[6],p[0]))
    co,si=I.bounds(1),I.bounds(0)
    for u,v in ((3,6),(6,5),(5,3)):
        U,V=sub(p[u],p[1]),sub(p[v],p[1]);C=dot(U,V)
        cv=cross(U,V);S=dot(cv,cv).sqrt()
        co,si=co*C-si*S,si*C+co*S
    A,B,C,D=left[2][1],left[2][0],left[1][1],left[2][2]
    s=orientation_sign(cross2(sub(B,A),sub(D,A)))
    vals={'obtuse_E_at_0':obtuse,'Right_patch_inward_at_6':inward,
          'positive_sin_fan_sum_at_1':si,
          'Left_patch_inward_at_0':-s*cross2(sub(B,A),sub(C,B))}
    if any(v.lo<=0 for v in vals.values()):raise ValueError('Narrow-fan R0 branch not certified')
    return {k:v.export() for k,v in vals.items()}

def replay():
    c=json.loads((ROOT/'results/a992-r0-narrow-fan-example.json').read_text())
    g=c['geometry']
    fresh=certificate(g['parameters'],c['failed_cut'],c['overlapping_faces'],
        [F(x) for x in c['interior_witness']],c['successful_cut'],F(g['parameter_half_width']))
    for k,v in fresh.items():
        if json.loads(json.dumps(v))!=c[k]:raise AssertionError('Example mismatch: '+k)
    p,_=geometry(g['parameters'],F(g['parameter_half_width']))
    signs=branch_signs(p,develop(p,c['failed_cut']),develop(p,c['successful_cut']))
    if signs!=c['R0_narrow_fan_signs']:raise AssertionError('Branch sign mismatch')
    return {'scope':'One rational A992 shape, not a universal proof premise.',
            'strict_Left_overlap':True,'strict_Right_residual_separators':3,
            'strict_branch_signs':4,'whole_graph_status':'open'}

if __name__=='__main__':print(json.dumps(replay(),indent=2))
