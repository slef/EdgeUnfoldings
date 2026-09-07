"""Emit TikZ code for a net Z_k (or for the three-petal v-fan picture) of an Octa.
usage as module: tikz_net(o, k, scale=..., highlight=[...]) -> str ;  tikz_triple(o, i) -> str
CLI: tikz_net.py case.npy v k out.tex   (P saved with np.save)"""
import numpy as np, sys
from octa import *

def _fmt(p): return "(%.4f,%.4f)" % (p[0], p[1])

def tikz_net(o, k, scale=None, highlight=(), labels=True, extra=""):
    net = o.Z(k)
    pts = np.vstack([T for key, T in net.items() if isinstance(key, tuple)])
    if scale is None: scale = 6.0 / np.ptp(pts, 0).max()
    out = ["\\begin{tikzpicture}[scale=%.4f, every node/.style={font=\\tiny}]" % scale]
    for key, T in net.items():
        if not isinstance(key, tuple): continue
        typ, j = key; t = (j - k) % 4; prime = "'" if t == 3 else ""
        style = "fill=fanblue" if typ == 'W' else "fill=petalorange"
        out.append("  \\draw[%s, draw=black, line width=0.3pt] %s -- %s -- %s -- cycle;" % (style, _fmt(T[0]), _fmt(T[1]), _fmt(T[2])))
        if labels:
            c = T.mean(0); out.append("  \\node at %s {$%s_{%d}%s$};" % (_fmt(c), typ, t, prime))
    for nm in highlight:
        X = o.intersection(k, nm)
        if len(X) >= 3: out.append("  \\fill[red] " + " -- ".join(_fmt(q) for q in X) + " -- cycle;")
    if labels:
        for t in range(4):
            j = (k + t) % 4; W = net[('W', j)]; V = net[('V', j)]
            out.append("  \\node[blue, anchor=south west] at %s {$u_{%d}$};" % (_fmt(W[1]), t))
            out.append("  \\node[red!70!black, anchor=south] at %s {$v$};" % _fmt(V[0]))
        W = net[('W', (k + 3) % 4)]
        out.append("  \\node[blue, anchor=south east] at %s {$u_0'$};" % _fmt(W[2]))
        out.append("  \\fill (0,0) circle (0.6pt) node[anchor=north] {$w$};")
    out.append(extra)
    out.append("\\end{tikzpicture}")
    return "\n".join(out)

def tikz_triple(o, i, scale=None, show_cstar=True):
    """The three petals V_i, V_j, V_jj in the net (W_i W_j W_jj contiguous), the cut-edge lines, D, and c*."""
    from cstar import rotate_about, signed_side
    k = (i - 1) % 4; net = o.Z(k); j, jj = (i + 1) % 4, (i + 2) % 4
    Vi, Vj, Vjj = net[('V', i)], net[('V', j)], net[('V', jj)]
    Wi, Wj, Wjj = net[('W', i)], net[('W', j)], net[('W', jj)]
    uj, ujj, vj = Vj[2], Vj[1], Vj[0]; kj, kjj = o.ku[j], o.ku[jj]; kap = kj + kjj
    pts = np.vstack([Vi, Vj, Vjj, Wi, Wj, Wjj])
    if scale is None: scale = 6.0 / np.ptp(pts, 0).max()
    out = ["\\begin{tikzpicture}[scale=%.4f, every node/.style={font=\\tiny}]" % scale]
    for T, lab in ((Wi, "W_i"), (Wj, "W_j"), (Wjj, "W_{j+1}")):
        out.append("  \\draw[fill=fanblue!50, draw=black, line width=0.3pt] %s -- %s -- %s -- cycle;" % tuple(_fmt(q) for q in T))
        out.append("  \\node at %s {$%s$};" % (_fmt(T.mean(0)), lab))
    for T, lab in ((Vi, "V_i"), (Vj, "V_j"), (Vjj, "V_{j+1}")):
        out.append("  \\draw[fill=petalorange, draw=black, line width=0.3pt] %s -- %s -- %s -- cycle;" % tuple(_fmt(q) for q in T))
        out.append("  \\node at %s {$%s$};" % (_fmt(T.mean(0)), lab))
    # cut-edge lines and D
    d1 = (Vi[0] - uj) / np.linalg.norm(Vi[0] - uj); d2 = (Vjj[0] - ujj) / np.linalg.norm(Vjj[0] - ujj)
    L = 3 * np.ptp(pts, 0).max()
    out.append("  \\draw[dashed, gray] %s -- %s;" % (_fmt(uj - L * d1), _fmt(uj + L * d1)))
    out.append("  \\draw[dashed, gray] %s -- %s;" % (_fmt(ujj - L * d2), _fmt(ujj + L * d2)))
    out.append("  \\node[blue, anchor=north] at %s {$u_j$};  \\node[blue, anchor=north] at %s {$u_{j+1}$};" % (_fmt(uj), _fmt(ujj)))
    out.append("  \\node[red!70!black, anchor=south] at %s {$v_j$};" % _fmt(vj))
    if show_cstar:
        cand = [sg for sg in (1, -1) if np.linalg.norm(rotate_about(Vi[:1], uj, -sg * kj)[0] - vj) < 1e-7 * o.scale]
        if cand:
            sgn = cand[0]
            def R(X): return rotate_about(rotate_about(X, uj, sgn * kj), ujj, sgn * kjj)
            A = rot(sgn * kap); b = R(np.zeros((1, 2)))[0]; cs = np.linalg.solve(np.eye(2) - A, b)
            out.append("  \\fill[purple] %s circle (0.8pt) node[anchor=north] {$c^*$};" % _fmt(cs))
            m = (vj - cs) / np.linalg.norm(vj - cs)
            out.append("  \\draw[purple, thin] %s -- %s node[anchor=south] {$M$};" % (_fmt(cs - 0.2 * L * m), _fmt(cs + 0.6 * L * m)))
    out.append("\\end{tikzpicture}")
    return "\n".join(out)

if __name__ == '__main__':
    P = np.load(sys.argv[1]); v = int(sys.argv[2]); k = int(sys.argv[3])
    o = Octa(P, v); open(sys.argv[4], 'w').write(tikz_net(o, k))
