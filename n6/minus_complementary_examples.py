"""Exact examples for the sharp-corner complementary-source theorem."""
from fractions import Fraction as F
import json
from pathlib import Path
from n6.families import MINUS_FACES,region
from n6.certify import require
from n6.intervals import set_precision
from n6.polynomials import Poly
from n6.polycert import point_spec,make_certificate,verify as all_pairs
from n6.minus_complementary_sources import select

NUMERATORS=[[0,0,0],[16200,2100,-2580],[12000,720,-840],[4200,1380,-1740],[-7950,-255,-1725],[-11850,75,-2175]]
DENOMINATORS=[375,535,195,715,5,265]


def specification(kind='strict',family=False):
    if kind=='boundary':p=[[F(x) for x in row] for row in [[3,0,3],[3,3,0],[0,0,0],[6,3,3],[0,3,3],[3,4,4]]]
    elif kind in ('fallback','fallback_reflected'):
        nums=[[0,0,0],[8400,114000,600],[5000,58000,5200],[3400,56000,-4600],[4600,-2500,1150],[3800,-3500,-3750]]
        p=[[F(x,d) for x in row] for row,d in zip(nums,[231,551,251,531,1,141])]
    else:p=[[F(x,d) for x in row] for row,d in zip(NUMERATORS,DENOMINATORS)]
    if kind in ('reflected','fallback_reflected'):p=[[-p[i][0],p[i][1],p[i][2]] for i in [0,1,3,2,5,4]]
    origin=p[0];p=[[x-y for x,y in zip(row,origin)] for row in p]
    scale=max(abs(x) for row in p for x in row);p=[[x/scale for x in row] for row in p]
    cuts=[[0,2],[0,3],[0,4],[0,5],[1,2 if kind not in ('reflected','fallback_reflected') else 3]]
    if not family:return point_spec([[str(x) for x in row] for row in p],MINUS_FACES,cuts)
    require(kind!='boundary','The boundary illustration uses its exact point')
    x,y,u,v,r,s,h,t,k,l=[Poly.variable(10,i) for i in range(10)]
    constant=lambda point:[Poly.constant(10,q) for q in point]
    points=[constant(row) for row in p]
    points[1]=[points[1][j]+x*p[2][j]+y*p[1][j] for j in range(3)]
    points[3]=[points[3][j]+u*p[2][j]+v*p[1][j] for j in range(3)]
    points[4]=[q+d for q,d in zip(points[4],[r,s,h])]
    points[5]=[q+d for q,d in zip(points[5],[t,k,l])]
    return {**region([['-1/100000000','1/100000000']]*10,points,MINUS_FACES,cuts,
                     ['B_C','B_B','D_C','D_B','P_x','P_y','P_z','Q_x','Q_y','Q_z']),
            'arithmetic_mode':'affine','suggested_fractional_bits':240,
            'family_description':'Full ten-parameter local original-face chart with A,C and the base plane fixed by Euclidean normalization.'}


def main():
    set_precision(240);root=Path(__file__).parent/'results'
    for kind,family in [('strict',False),('strict',True),('reflected',False),('boundary',False),('fallback',False),('fallback',True),('fallback_reflected',False)]:
        spec=specification(kind,family)
        if kind.startswith('fallback'):
            from n6.minus_edge_theorem import select as full_select
            choice=full_select(spec)
        else:choice=select(spec)
        cert=make_certificate({**spec,'cut_edges':choice['cut_edges']})
        report=dict(choice=choice,independent_all_original_pairs=all_pairs(cert))
        name='minus-complementary-'+kind+('-family' if family else '')
        for suffix,value in [('certificate',cert),('verification',report)]:
            (root/f'{name}.{suffix}.json').write_text(json.dumps(value,indent=2)+'\n')
        print(name,choice['branch'],'verified',flush=True)


if __name__=='__main__':main()
