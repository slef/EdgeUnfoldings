"""Exact original-facet examples of the strictly low-curvature theorems."""
import json
from fractions import Fraction as F
from pathlib import Path
from n6.families import minus_region,prism_region,MINUS_FACES,PRISM_FACES,center_parameters
from n6.intervals import set_precision
from n6.polycert import point_spec,make_certificate,verify as all_pairs
from n6.low_curvature_types import candidate_trees,verify

DATA={
    'minus':(minus_region,MINUS_FACES,['1','1','0','1','3/4','1/4','1','1/4','3/4','1']),
    'prism':(prism_region,PRISM_FACES,['0','1','0','0','1','6/5','1','1','1']),
}


def specification(name,region=False):
    builder,faces,center=DATA[name]
    tree=candidate_trees(faces)['candidate_trees'][0]
    radius=F(1,1000) if region else F(0)
    spec=builder([[str(F(c)-radius),str(F(c)+radius)] for c in center],cuts=tree['cuts'])
    if region:spec=center_parameters(spec)
    else:
        # Integer coordinates keep the displayed model exactly tied to its input.
        parameters=list(map(F,center))
        def evaluate(terms):
            total=F(0)
            for coefficient,powers in terms:
                value=F(coefficient)
                for parameter,power in zip(parameters,powers):value*=parameter**power
                total+=value
            return total
        exact=[[evaluate(terms)*20 for terms in point] for point in spec['coordinate_polynomials']]
        assert all(x.denominator==1 for point in exact for x in point)
        points=[[int(x) for x in point] for point in exact]
        spec=point_spec(points,faces,tree['cuts'])
    return {**spec,'suggested_fractional_bits':240}


def main():
    set_precision(240);results=Path(__file__).parent/'results'
    for name in DATA:
        for is_region in [False,True]:
            label=name+('-family' if is_region else '')
            cert=make_certificate(specification(name,is_region))
            report=dict(hypotheses=verify(cert),independent_input_net=all_pairs(cert))
            for suffix,data in [('certificate',cert),('verification',report)]:
                (results/f'low-curvature-{label}.{suffix}.json').write_text(json.dumps(data,indent=2)+'\n')
            print(label,'verified',flush=True)


if __name__=='__main__':main()
