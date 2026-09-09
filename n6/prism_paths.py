"""Exact audit of the sharper-apex, shorter-quadrilateral-path proposal.

This verifies a specified counterexample, not a universal prism theorem.
Polygon corner angles use the two actual neighboring vertices of the facet.
"""
from n6.certify import require
from n6.curvature import cmul,interval_angle_le
from n6.intervals import I,sub,dot,cross,norm2
from n6.polycert import Geometry,verify_overlap
from n6.trees import quadrilateral_path_stars


def polygon_angle_product(g,vertex):
    product=(I(1),I(0))
    for face in g.faces:
        if vertex not in face:continue
        i=face.index(vertex)
        a=sub(g.p[face[i-1]],g.p[vertex])
        b=sub(g.p[face[(i+1)%len(face)]],g.p[vertex])
        product=cmul(product,(dot(a,b),norm2(cross(a,b)).sqrt()))
    return product


def verify_shorter_failure(cert):
    overlap=verify_overlap(cert)
    g=Geometry(cert);trees=quadrilateral_path_stars(g.faces)
    selected=cert['path_selection'];v,u=selected['apex'],selected['via']
    options=[t for t in trees if t['apex']==v]
    chosen=[t for t in options if t['slit_vertex']==u]
    require(len(chosen)==1 and len(options)==2,'Expected two quadrilateral paths at the selected apex')
    require(sorted(map(tuple,cert['cut_edges']))==chosen[0]['cuts'],'Certificate cuts do not match the selected path')
    others={t['apex'] for t in trees}-{v}
    require(len(others)==1,'Expected exactly two degree-four apex choices')
    other=next(iter(others));a,b=polygon_angle_product(g,v),polygon_angle_product(g,other)
    require(interval_angle_le(a,b) is True and interval_angle_le(b,a) is False,
            'The selected apex is not certified strictly sharper')
    def length(t):
        x,y,z=(t[k] for k in ('apex','slit_vertex','antipode'))
        return norm2(sub(g.p[x],g.p[y])).sqrt()+norm2(sub(g.p[y],g.p[z])).sqrt()
    short=length(chosen[0]);long=length(next(t for t in options if t is not chosen[0]))
    require(short.hi<long.lo,'Selected boundary route is not certified strictly shorter')
    return dict(result='verified_sharper_apex_shorter_path_failure',apex=v,via=u,
                strictly_sharper_than=other,shorter_length=short.pair(),longer_length=long.pair(),
                overlap=overlap,scope='This tree-selection rule fails. This does not refute success of the two-path family or edge unfoldability.')


def main():
    import argparse,json
    from pathlib import Path
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    args=ap.parse_args();print(json.dumps(verify_shorter_failure(json.loads(args.input.read_text())),indent=2))


if __name__=='__main__':main()
