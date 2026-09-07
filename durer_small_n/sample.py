import numpy as np, time, sys, collections
from unfold import Polytope

def rand_points(n, rng):
    kind = rng.integers(4)
    if kind == 0:
        P = rng.normal(size=(n,3))
    elif kind == 1:
        P = rng.normal(size=(n,3)); P /= np.linalg.norm(P,axis=1,keepdims=True)
    elif kind == 2:
        P = rng.uniform(size=(n,3))
    else:
        P = rng.normal(size=(n,3)); P[0] *= np.exp(rng.uniform(0,5))  # one far point
    S = np.exp(rng.uniform(-4,4,size=3)); S[0]=1
    Q = np.linalg.qr(rng.normal(size=(3,3)))[0]
    P = (P*S) @ Q
    return P

n = int(sys.argv[1]); N = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv)>3 else 0
rng = np.random.default_rng(seed)
stats = collections.defaultdict(list)
worst = None
t0=time.time()
for it in range(N):
    P = rand_points(n, rng)
    try:
        p = Polytope(P)
    except Exception as e:
        continue
    if len(p.P) != n or len(p.faces) != 2*n-4: continue  # need all n vertices, simplicial
    degseq = tuple(sorted(p.deg.values()))
    pen = p.penetrations()
    good = int((pen<=0).sum())
    stats[degseq].append(good)
    if worst is None or good < worst[0]:
        worst = (good, degseq, P.copy())
print("n=%d samples=%d time=%.1fs"%(n, N, time.time()-t0))
for k,v in stats.items():
    v=np.array(v)
    print(" type",k,"count",len(v),"trees",len(Polytope(worst[2]).trees()) if k==worst[1] else '?',
          "min good",v.min(),"median",int(np.median(v)),"frac all-good %.3f"%np.mean(v==v.max()))
print("worst:", worst[0], worst[1]); np.save("worst_%d_%d.npy"%(n,seed), worst[2])
