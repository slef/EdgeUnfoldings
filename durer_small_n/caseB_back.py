"""Test: in sub-case (a,a) (both apexes beyond the other base line, no far vertex past X), does nu_m <= kappa_back hold?
kappa_back = k_{u_i} + k_{u_k} + k_w.  Runs over stat seeds and adversarial pickles."""
import numpy as np, pickle, sys, glob
from octa import *
from caseB_sub import geom, sub_of
rows = []
for f in ['caseB_sub_stat_H3.pkl', 'caseB_sub_stat_none.pkl']:
    for P, v, i, sub in pickle.load(open(f, 'rb')):
        o = Octa(P, v); rows.append((f, sub, o, i))
for f in glob.glob('caseB_sub_*_a_a.pkl') + glob.glob('caseB_sub_*_fa_a.pkl') + glob.glob('caseB_sub_*_a_fa.pkl'):
    for b, P in pickle.load(open(f, 'rb')):
        o = Octa(P, b[1]); i = b[2]; g = geom(o, i)
        if g is None or g['SW'] >= np.pi: continue
        ri, rjj = sub_of(g); rows.append((f, ri + '_' + rjj, o, i))
worst = {}
for f, sub, o, i in rows:
    j, jj, m = (i + 1) % 4, (i + 2) % 4, (i - 1) % 4
    kb = o.ku[i] + o.ku[m] + o.kw; d = o.nu[m] - kb
    key = (f.split('_')[2] if 'stat' in f else f, sub)
    if key not in worst or d > worst[key][0]: worst[key] = (d, o.nu[m], kb, np.round(o.ku, 3), o.kw, o.kv)
for key, val in sorted(worst.items()): print(key, "max(nu_m - kappa_back) = %.4f  (nu_m=%.3f kb=%.3f ku=%s kw=%.3f kv=%.3f)" % val)
