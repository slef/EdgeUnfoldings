"""Adversarial closeness of the far pairs under (H) restricted to fat polytopes: thickness >= TMIN.
usage: adv_fat.py TMIN seed restarts steps"""
import numpy as np, sys, pickle
from octa import *
from adv_opp import separation, violation, DELTA
def thickness(P):
    Q = P - P.mean(0); sv = np.linalg.svd(Q, compute_uv=False); return float(sv[-1] / sv[0])
TMIN = float(sys.argv[1]); KMIN = float(sys.argv[5]) if len(sys.argv) > 5 else DELTA
def best_config(P):
    st = octa_structure(P)
    if st is None: return None
    o = sharpest_apex(P, st[0], st[1]); k = int(np.argmax(o.ku))
    deg = max(0.0, DELTA - min(o.r.min(), o.s.min(), o.l.min()) / o.scale, KMIN - min(o.kappa.values()), TMIN - thickness(P))
    best = None
    for nm in Octa.OPP + Octa.FARFAN:
        sep = separation(*o.pair_faces(k, nm)) / o.scale; sc = sep - 10 * deg
        if best is None or sc > best[0]: best = (sc, o.v, k, nm, sep, thickness(P))
    return best
if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[2])); R_ = int(sys.argv[3]); S = int(sys.argv[4]); res = []; r = 0
    while r < R_:
        P0 = rand_points(6, rng)
        if octa_structure(P0) is None or thickness(P0) < TMIN: continue
        r += 1
        f = lambda P: (lambda b: None if b is None else b[0])(best_config(P))
        P, sc = hill_climb(f, P0, rng, steps=S, step=0.2)
        b = best_config(P); res.append((b, P)); print("restart %d: score %.5f v=%d k=%d %s sep=%.5f thick=%.3f" % ((r,) + b), flush=True)
    res.sort(key=lambda t: -t[0][0]); pickle.dump(res, open('adv_fat_%.2f_k%.2f.pkl' % (TMIN, KMIN), 'wb')); print("BEST", res[0][0])
