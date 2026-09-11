"""Exact sharp-route Case A families needing the new wider angle bound."""
from fractions import Fraction as F
import json
from pathlib import Path
from n6.cofacial_star_reduction import verify_case_A
from n6.families import MINUS_FACES,PRISM_FACES,region
from n6.intervals import set_precision
from n6.polycert import point_spec,make_certificate,verify as all_pairs
from n6.polynomials import Poly

DATA={
 'minus':dict(numerators=[[0,0,0],[1080,12600,980],[420,13800,420],[660,-1200,560],[-780,16650,915],[-660,9150,985]],
              denominators=[122,242,342,22,162,2],
              cuts=[[0,3],[1,2],[1,3],[1,4],[1,5]],faces=MINUS_FACES),
 'prism':dict(numerators=[[-9000,-780,38000],[-12000,1080,46000],[0,0,0],[-19200,-1296,41600],[-20400,720,42000],[-8400,-360,-4000]],
              denominators=[685,225,285,545,5,65],
              cuts=[[0,3],[1,3],[2,5],[3,4],[3,5]],faces=PRISM_FACES),
}


def specification(kind,family=False):
    data=DATA[kind];p=[[F(x,d) for x in row] for row,d in zip(data['numerators'],data['denominators'])]
    origin=p[0];p=[[x-y for x,y in zip(row,origin)] for row in p]
    scale=max(abs(x) for row in p for x in row);p=[[x/scale for x in row] for row in p]
    if not family:return point_spec([[str(x) for x in row] for row in p],data['faces'],data['cuts'])
    a,b,c,d,e,f=[Poly.variable(6,i) for i in range(6)];matrix=[[1+a,b,c],[b,1+d,e],[c,e,1+f]]
    coordinates=[[sum(matrix[i][j]*row[j] for j in range(3)) for i in range(3)] for row in p]
    return {**region([['-1/1000000','1/1000000']]*6,coordinates,data['faces'],data['cuts'],
                     ['xx','xy','xz','yy','yz','zz']),
            'arithmetic_mode':'affine','suggested_fractional_bits':240,
            'family_description':'Six independent symmetric affine deformations of the stated exact point; not a full realization-space chart.'}


def main():
    set_precision(240);root=Path(__file__).parent/'results'
    for kind in DATA:
        for family in (False,True):
            cert=make_certificate(specification(kind,family));hypotheses=verify_case_A(cert)
            assert not hypotheses['left_condition'] and not hypotheses['right_condition']
            report=dict(hypotheses=hypotheses,independent_all_original_pairs=all_pairs(cert))
            name='cofacial-case-A-'+kind+('-family' if family else '')
            for suffix,data in [('certificate',cert),('verification',report)]:
                (root/f'{name}.{suffix}.json').write_text(json.dumps(data,indent=2)+'\n')
            print(name,'verified',flush=True)


if __name__=='__main__':main()
