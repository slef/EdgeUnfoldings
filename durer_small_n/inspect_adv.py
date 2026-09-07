"""Inspect adversarial results: inspect_adv.py adv_opp_H2.pkl [n_best] [outdir]"""
import numpy as np, sys, pickle, os
from octa import *
from draw import draw_net
from oppcases import describe

res = pickle.load(open(sys.argv[1], 'rb')); n = int(sys.argv[2]) if len(sys.argv) > 2 else 5
out = sys.argv[3] if len(sys.argv) > 3 else os.path.splitext(sys.argv[1])[0]; os.makedirs(out, exist_ok=True)
for t, (b, P) in enumerate(res[:n]):
    sc, v, k, nm, sep, vio = b
    o = Octa(P, v); i = k if nm == 'V_k-V_k+2' else (k + 1) % 4; j, jj, m = (i + 1) % 4, (i + 2) % 4, (i - 1) % 4
    print("#%d score=%.6f v=%d k=%d %s (ring i=%d) sep=%.2e viol=%.3f" % (t, sc, v, k, nm, i, sep, vio))
    print("   kv=%.3f kw=%.3f ku=%s" % (o.kv, o.kw, np.round(o.ku, 3)))
    print("   nu=%s omega=%s" % (np.round(o.nu, 3), np.round(o.omega, 3)))
    print("   r=%s s=%s l=%s" % (np.round(o.r / o.scale, 3), np.round(o.s / o.scale, 3), np.round(o.l / o.scale, 3)))
    print("   aV=%s aVp=%s bW=%s bWp=%s" % (np.round(o.aV, 3), np.round(o.aVp, 3), np.round(o.bW, 3), np.round(o.bWp, 3)))
    print("   e=%s f=%s F=%s B=%s" % (np.round(o.e, 3), np.round(o.f, 3), np.round(o.F, 3), np.round(o.B, 3)))
    SW = o.bW[j] + o.bWp[i] + o.bWp[j] + o.bW[jj]
    print("   between petal j=%d: nu_j=%.3f ku_j+ku_jj=%.3f  SigmaW=%.3f (<pi: %s)  aVp_i=%.3f aV_jj=%.3f" % (j, o.nu[j], o.ku[j] + o.ku[jj], SW, SW < np.pi, o.aVp[i], o.aV[jj]))
    draw_net(o, k, os.path.join(out, 'best%d.png' % t), highlight=[nm])
    A, B = o.pair_faces(k, nm); c = np.vstack([A, B]).mean(0); r = max(np.ptp(np.vstack([A, B]), 0).max() * 0.7, 1e-3 * o.scale)
    draw_net(o, k, os.path.join(out, 'best%d_zoom.png' % t), highlight=[nm], zoom=(c[0], c[1], r))
