"""Independent exact replays for the written selected-octahedron theorem."""
import json
from pathlib import Path

from n6.intervals import set_precision
from n6.point_audit import exact_hull, cuts_for
from n6.polycert import point_spec, make_certificate, verify as verify_all_pairs
from n6.selected_octahedron import verify

ROOT = Path(__file__).resolve().parent
SOURCES = {
    'high-curvature':'far-projection-high-curvature',
    'low-curvature':'far-projection-low-curvature',
    'low-curvature-family':'far-projection-low-curvature-family',
    'obtuse':'far-projection-obtuse-repaired',
    'apex-entry-family':'far-pair-apex-entry-family',
    'radial-family':'far-pair-radial-family',
}
NEW_EXAMPLES = ('curvature-equality','crossing-threshold','regular-ties')


def specification(name):
    if name in SOURCES:
        return json.loads((ROOT/f'results/{SOURCES[name]}.certificate.json').read_text())
    if name in ('curvature-equality','crossing-threshold'):
        # At vertex 0, all four edges have length 740. The successive face
        # angles have cosines 3/5,4/5,3/5,4/5, so their sum is exactly pi.
        points = [[0,0,0],[370,370,555],[0,0,740],
                  [592,0,444],[560,420,240],[0,444,592]]
    elif name=='regular-ties':
        points = [[0,0,1],[0,0,-1],[1,0,0],[0,1,0],[-1,0,0],[0,-1,0]]
    else:
        raise ValueError('Unknown selected-octahedron example')
    faces,adj = exact_hull(points)
    spec = point_spec(points,faces,cuts_for(0,2,adj))
    nxt={}
    for face in faces:
        if 1 in face:
            j=face.index(1)
            nxt[face[(j+1)%3]]=face[(j+2)%3]
    ring=[2]
    while len(ring)<4:
        ring.append(nxt[ring[-1]])
    spec['selection']=dict(apex=0,antipode=1,equator=ring,slit_index=0)
    spec['suggested_fractional_bits']=240
    if name=='crossing-threshold':
        spec['parameter_box']=[['-1/10000','1/10000'] for _ in range(18)]
        for i,point in enumerate(points):
            for j,value in enumerate(point):
                powers=[0]*18; powers[3*i+j]=1
                spec['coordinate_polynomials'][i][j]=[[str(value),[0]*18],['1',powers]]
    return spec


def main():
    set_precision(240)
    for name in (*SOURCES,*NEW_EXAMPLES):
        cert=make_certificate(specification(name))
        report=dict(theorem_hypotheses=verify(cert),independent_all_28_pairs=verify_all_pairs(cert))
        stem=ROOT/f'results/selected-octahedron-{name}'
        if name in NEW_EXAMPLES:
            Path(str(stem)+'.certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
            report['source_certificate']=stem.name+'.certificate.json'
        else:
            report['source_certificate']=SOURCES[name]+'.certificate.json'
        Path(str(stem)+'.verification.json').write_text(json.dumps(report,indent=2)+'\n')
        print(name,report['theorem_hypotheses']['proof_branch'],flush=True)


if __name__=='__main__':
    main()
