"""Draw the verified individual-apex counterexample in its common net frame."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from n6.apex_entry import verify
from n6.polycert import Geometry,verify as verify_net
from n6.certify import tree_path


def render():
    root=Path(__file__).resolve().parent
    cert=json.loads((root/'results/caseB-apex-entry.certificate.json').read_text())
    verify(cert);verify_net(cert);g=Geometry(cert)
    sel=cert['selection'];v,w,u=sel['apex'],sel['antipode'],sel['equator']
    lookup={frozenset(f):i for i,f in enumerate(g.faces)}
    V=[lookup[frozenset((v,u[i],u[(i+1)%4]))] for i in range(4)]
    W=[lookup[frozenset((w,u[i],u[(i+1)%4]))] for i in range(4)]
    def development(f):return {k:np.array([float((x.lo+x.hi)/2) for x in p]) for k,p in g.develop(tree_path(g.adj,W[1],f)).items()}
    base=development(W[1]);origin=base[u[1]];ex=base[u[2]]-origin;ell=np.linalg.norm(ex);ex/=ell;ey=np.array([-ex[1],ex[0]])
    if (development(V[1])[v]-origin)@ey<0:ey=-ey
    def D(f):return {k:np.array([(p-origin)@ex,(p-origin)@ey])/ell for k,p in development(f).items()}
    sets={('V',i):D(V[i]) for i in range(3)}|{('W',i):D(W[i]) for i in range(3)}
    L,R,F=sets['V',0],sets['V',2],sets['W',1]
    points=np.array([p for q in sets.values() for p in q.values()]);lo=points.min(axis=0)-[.25,.28];hi=points.max(axis=0)+[.22,.25]
    lines=[(L[u[1]],L[u[0]]),(R[u[2]],R[u[3]])]
    cross=lambda a,b:a[0]*b[1]-a[1]*b[0]
    def clip(poly,a,b):
        d=b-a;sign=np.sign(cross(d,F[w]-a));value=lambda p:-sign*cross(d,p-a)
        out=[]
        for p,q in zip(poly,np.roll(poly,-1,axis=0)):
            fp,fq=value(p),value(q)
            if fp>=0:out.append(p)
            if (fp>=0)!=(fq>=0):out.append(p+fp/(fp-fq)*(q-p))
        return np.array(out)
    wedge=np.array([[lo[0],lo[1]],[hi[0],lo[1]],[hi[0],hi[1]],[lo[0],hi[1]]])
    for a,b in lines:wedge=clip(wedge,a,b)
    fig,ax=plt.subplots(figsize=(10.5,6.2))
    ax.add_patch(Polygon(wedge,facecolor='#faf2df',edgecolor='#c2a56b',hatch='///',linewidth=.5,zorder=0))
    for i in range(3):
        q=sets['W',i];ax.add_patch(Polygon([q[k] for k in g.faces[W[i]]],facecolor='#bddbef',edgecolor='#407698',linewidth=1.3))
    for i in (1,0,2):
        q=sets['V',i];fc,ec=('#e8e6e0','#96938b') if i==1 else ('#f2ba83','#a55319') if i==0 else ('#d7c8e8','#765593')
        ax.add_patch(Polygon([q[k] for k in g.faces[V[i]]],facecolor=fc,edgecolor=ec,linewidth=1.7,zorder=3))
    for a,b in lines:
        d=(b-a)/np.linalg.norm(b-a);ax.plot(*np.array([a-5*d,a+5*d]).T,'--',color='#9a8559',linewidth=1,zorder=2)
    ax.plot(*L[v],'o',color='#a55319',markersize=6,zorder=5)
    ax.annotate('This apex enters Ω',L[v],xytext=(10,-22),textcoords='offset points',fontsize=12,color='#8d4012',weight='bold',zorder=6)
    center=np.mean([R[k] for k in R],axis=0)
    ax.annotate('The other petal stays outside Ω',center,xytext=(-18,70),textcoords='offset points',fontsize=11,color='#684587',ha='center',arrowprops=dict(arrowstyle='->',color='#765593'),zorder=6)
    for p,label,offset in [(L[u[1]],'u',(0,9)),(R[u[2]],'u′',(6,-3)),(F[w],'w',(-16,4)),(L[u[0]],'slit vertex', (4,-14))]:
        ax.plot(*p,'o',color='#334654',markersize=3,zorder=5);ax.annotate(label,p,xytext=offset,textcoords='offset points',fontsize=10,zorder=6)
    ax.text(lo[0]+.08,lo[1]+.06,'Hatched: possible meeting region Ω',fontsize=10,color='#8c7140')
    ax.set(xlim=(lo[0],hi[0]),ylim=(lo[1],hi[1]));ax.set_aspect('equal');ax.axis('off')
    fig.suptitle('An apex can enter, while the petals remain disjoint',x=.035,ha='left',fontsize=17,weight='bold')
    fig.text(.035,.04,'Exact convex example under both selection rules. All 28 pairs of the complete unfolding are certified nonoverlapping.',fontsize=10,color='#44525d')
    fig.subplots_adjust(left=.025,right=.98,top=.9,bottom=.10)
    out=root/'figures/caseB-apex-entry';fig.savefig(out.with_suffix('.svg'));fig.savefig(out.with_suffix('.png'),dpi=140);plt.close(fig)
    svg=out.with_suffix('.svg');svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')


if __name__=='__main__':render()
