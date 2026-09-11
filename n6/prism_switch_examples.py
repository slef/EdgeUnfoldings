"""Exact point and full-chart checks of both new prism fallback branches."""
from fractions import Fraction as F
import json
from pathlib import Path
from n6.intervals import set_precision
from n6.families import PRISM_CUTS
from n6.prism_complementary_examples import specification as chart
from n6.prism_switch_checks import verify_sharp_fan_fallback,verify_gate_fallback
from n6.polycert import make_certificate,verify as all_pairs

DATA={
 'sharp':([[3600,-840,-5400],[-4600,-120,-5800],[0,0,0],[720,-1008,-10280],[-8200,-120,-9600],[-3600,0,-3800]],[50,350,10,258,550,210]),
 'gate':([[-6000,-320,2000],[-4800,-460,36000],[0,0,0],[-7400,-284,2400],[-5000,-360,36000],[-200,100,0]],[1280,1220,1000,1536,1420,1200]),
}


def specification(kind,family=False):
    nums,dens=DATA[kind];p=[[F(x,d) for x in row] for row,d in zip(nums,dens)]
    return {**chart(family=family,points=p),'cut_edges':[list(e) for e in PRISM_CUTS]}


def main():
    set_precision(240);root=Path(__file__).parent/'results'
    for kind,check in [('sharp',verify_sharp_fan_fallback),('gate',verify_gate_fallback)]:
        for family in (False,True):
            s=specification(kind,family);r=check(s);c=make_certificate(s)
            name='prism-switch-'+kind+('-family' if family else '-point')
            report=dict(hypotheses=r,independent_all_original_pairs=all_pairs(c))
            for suffix,data in [('certificate',c),('verification',report)]:
                (root/(name+'.'+suffix+'.json')).write_text(json.dumps(data,indent=2)+'\n')
            print(name,'verified',flush=True)


if __name__=='__main__':main()
