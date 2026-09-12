"""Rounded display frames for a separately proved insertion family."""
import json,math
import numpy as np
from n7.bipyramid_morph import ROOT,FACES,cut_at
from n7.bipyramid_switch_insertion import geometry
from n7.a992 import unfold

def build():
    row=json.loads((ROOT/'results/bipyramid-switch-insertion.json').read_text());ex,c,direction,_=geometry(row);base=np.array(ex,float);c=np.array(c,float);direction=np.array(direction,float);frames=[]
    for i in range(101):
        p=base.copy();p[5]=c+(i/100)*direction;d=np.linalg.norm(p[:5]-p[5],axis=1)+np.linalg.norm(p[:5]-p[6],axis=1);slit=int(np.argmax(d));cut=cut_at(6,slit);n=unfold(p,cut,FACES,0);gap=2*math.pi
        for j in range(5):
            a=p[j]-p[5];b=p[(j+1)%5]-p[5];gap-=math.atan2(np.linalg.norm(np.cross(a,b)),a@b)
        frames.append({'points':p.tolist(),'net':[a.tolist() for a in n],'cuts':cut,'slit':slit,'gap':gap})
    data={'faces':FACES,'frames':frames,'scope':'Rounded drawing frames; continuous safety follows from the written theorem and verified geometric hypotheses.'}
    (ROOT/'bipyramid-switch-demo.html').write_text((ROOT/'switch-demo-template.html').read_text().replace('SWITCH_DATA',json.dumps(data,separators=(',',':'))))
if __name__=='__main__':build()
