"""Do the four opposite-quad wedge inequalities of the Proposition hold for ALL k when κ_v ≥ max κ_u ?
    F_k+B_{k+2} < ω_{k+1};  B_k+F_{k+2} < ω_{k-1}+κ_w;  F_{k+1}+B_{k-1} < ω_{k+2};  B_{k+1}+F_{k-1} < κ_w+ω_k
Also: the actual opposite-petal overlaps vs these inequalities, and lean statistics under the hypothesis.
usage: oppwedge.py seed N
"""
import numpy as np, sys, collections
from octa import *

if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[1])); N = int(sys.argv[2])
    st = collections.Counter(); worst = []
    for P, faces, adj in random_octahedra(rng, N):
        for o in all_apexes(P, faces, adj):
            hyp = o.kv >= o.ku.max(); hypw = hyp and o.kv >= o.kw
            F, B, om, kw = o.F, o.B, o.omega, o.kw
            for k in range(4):
                i = lambda t: (k + t) % 4
                ineq = {'F_k+B_k+2<om_k+1': F[i(0)] + B[i(2)] < om[i(1)],
                        'B_k+F_k+2<om_k-1+kw': B[i(0)] + F[i(2)] < om[i(3)] + kw,
                        'F_k+1+B_k-1<om_k+2': F[i(1)] + B[i(3)] < om[i(2)],
                        'B_k+1+F_k-1<kw+om_k': B[i(1)] + F[i(3)] < kw + om[i(0)]}
                ov = o.overlaps(k, Octa.OPP)
                st['nets'] += 1
                for tag, cond in (('all', True), ('hyp kv>=max ku', hyp), ('v sharpest', hypw)):
                    if not cond: continue
                    st[tag + ': nets'] += 1
                    st[tag + ': all four opp ineqs hold'] += all(ineq.values())
                    st[tag + ': opp overlap'] += bool(ov)
                    for nm, val in ineq.items():
                        st[tag + ': fails ' + nm] += (not val)
                if hyp and not all(ineq.values()):
                    worst.append((o.kv - o.ku.max(), k, {n: v for n, v in ineq.items() if not v}, np.round(F, 3), np.round(B, 3), np.round(om, 3), round(kw, 3), bool(ov)))
    for key, c in sorted(st.items()): print("  %-46s %d" % (key, c))
    worst.sort(key=lambda t: -t[0])
    for t in worst[:8]: print("  hyp-but-fails: kv-maxku=%.3f k=%d %s F=%s B=%s om=%s kw=%s overlap=%s" % t)
