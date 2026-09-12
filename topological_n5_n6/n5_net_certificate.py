"""Verify one successful original-edge net of the concave n=5 pyramid.

Uses the repository's outward rational interval arithmetic. The selected tree
is a fixed example, not a universal rule. AC is an uncut drawing diagonal.
"""
from itertools import combinations
import json
import sys
from pathlib import Path

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from n6.intervals import I, sub, dot, norm2, cross, det
from exact_topological_audit import P5, F5, edge, incidence, verify_five, require

CUTS={edge(*e) for e in ['AB','AD','BC','CP']}


def verify():
    verify_five()
    p={v:tuple(I(x) for x in pt) for v,pt in P5.items()}
    inc=incidence(F5); adj={i:[] for i in range(len(F5))}
    require(edge('A','C') not in CUTS,'original quadrilateral remains uncut')
    for e,(i,j) in inc.items():
        if e not in CUTS:adj[i].append(j);adj[j].append(i)
    require(sum(map(len,adj.values()))==2*(len(F5)-1),'dual tree edge count')
    def path(i,j):
        todo=[(i,[i])];seen={i}
        for at,pa in todo:
            if at==j:return pa
            for n in adj[at]:
                if n not in seen:seen.add(n);todo.append((n,pa+[n]))
        raise ValueError('dual graph disconnected')
    def develop(pa):
        out=None
        for i in pa:
            f=F5[i]
            if out is None:
                a,b,c=f;ell=norm2(sub(p[b],p[a])).sqrt();A=(I(0),I(0));B=(ell,I(0))
            else:
                a,b=next((a,b) for a,b in zip(f,f[1:]+f[:1]) if a in out and b in out)
                c=next(c for c in f if c not in (a,b));A=out[a];B=out[b]
            u=sub(B,A);d=sub(p[b],p[a]);q=sub(p[c],p[a]);den=norm2(d)
            x=dot(d,q)/den;y=norm2(cross(d,q)).sqrt()/den
            out={a:A,b:B,c:tuple(A[k]+x*u[k]+y*(-u[1],u[0])[k] for k in range(2))}
        return out
    checks=[]
    for i,j in combinations(range(len(F5)),2):
        pa=path(i,j);A=develop(pa[:1]);B=develop(pa)
        found=None
        for own,target,oid,tid in [(A,B,i,j),(B,A,j,i)]:
            f=F5[oid]
            for a,b in zip(f,f[1:]+f[:1]):
                bounds=[]
                for v in F5[tid]:
                    same_endpoint=v in (a,b) and all(v in F5[k] for k in pa)
                    bounds.append(I(0) if same_endpoint else det(sub(own[b],own[a]),sub(target[v],own[a])))
                if all(t.hi<=0 for t in bounds):
                    found={'pair':[i,j],'owner':oid,'edge':[a,b],'target_signed_bounds':[t.pair() for t in bounds]};break
            if found:break
        require(found is not None,f'no interval separator for pair {i}/{j}')
        checks.append(found)
    return {'scope':'one fixed concave pyramid, all 15 triangle pairs; uncut AC rejoins the base',
            'cuts':sorted(CUTS),'pairs_verified':len(checks),'certificates':checks}

if __name__=='__main__': print(json.dumps(verify(),indent=2))
