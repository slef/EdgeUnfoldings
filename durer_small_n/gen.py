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

