# Six-vertex proof attempt — incomplete

No complete proof of the six-vertex theorem was obtained.

## Octahedron candidate family

For every vertex v, let w be its opposite vertex. For each of the four neighbors u of w, cut the four edges incident to v and the edge wu. These are 24 distinct spanning trees, out of 384 total.

The exact counterexample query asserts a strictly convex octahedral realization and positive-area overlap for each of these 24 trees. It contains 257 assertions, 168 shared face-pair paths, and 27,933 arithmetic/Boolean DAG nodes. The solver process ended with exit code 137, without a SAT/UNSAT answer. A configured 60-second timeout did not yield a normal reported result. No proof certificate exists.

## A sufficient geometric condition

Let vw be a shortest surface path between opposite vertices. Such a path traverses two adjacent triangles vab and wab and crosses ab: it cannot cross an edge incident to its starting or ending vertex in its interior, because the corresponding edge segment is already a strictly shorter ambient straight path to the crossing point.

Write L=d_surface(v,w). Develop these two triangles across ab. If, for one endpoint u of ab,

    |wu| <= L and angle(uw, vw) at w <= curvature(w),

then the cut tree star(v) plus wu unfolds without interior overlap.

Reason: in the star unfolding based at v, the patch bounded by vu, uw, and the shortest path wv develops to an ordinary triangle. It is attached to the rest along uw. Detach along uw and attach along the other copy of wv. The triangle moves into the exterior circular sector at w of radius L and angle curvature(w). The two inequalities ensure containment in that sector. The star-unfolding sector theorem guarantees that the sector is disjoint from the rest of the original unfolding. The resulting cuts are exactly star(v) plus wu.

Reference for the exterior-sector theorem: Boris Aronov and Joseph O'Rourke, Nonoverlap of the star unfolding, Discrete & Computational Geometry 8 (1992), 219–250, Definition 8.1 and Theorem 9.1. https://link.springer.com/content/pdf/10.1007/BF02293047.pdf

The source-at-a-vertex and tied-shortest-path cases use the limiting version of star unfolding. This argument allows boundary contact. For a fully formal treatment those limiting cases should be explicitly written out.

UNPROVED: every convex octahedron admits opposite vertices and an endpoint satisfying the displayed sufficient condition. The two previously isolated nonsimplicial six-vertex types also remain untreated by this argument.

## Numerical exploration (not certificates)

Seed: 60907. Generate six independent Gaussian points, apply random diagonal affine scalings with entries 10**Uniform(-1.5,1.5), normalize the largest pairwise distance to one, and retain octahedral hulls. Of 21,934 attempts, 5,000 were retained.

All 5,000 had at least one successful cut in the 24-tree family; the minimum observed number of successful cuts was 15. All had at least one choice satisfying the sector condition. Restricting the sector condition to w of maximum curvature failed on 3 samples, so that restriction is not a justified proof strategy. The numerical overlap predicate uses tolerance 1e-10 on normalized inputs; small overlaps can be missed. Sampling is not exhaustive and does not establish the universal claims.

A separate differential-evolution search made 2,567 valid octahedral evaluations and did not find a failure of the sector condition; this also has no certification force.

## Files and reproduction

Dependencies: Python, numpy, scipy, networkx, sympy, z3-solver. The observed Z3 version was 5.1.0.0.

- sector_probe_large.py: reproduce the 5,000-sample numerical experiment.
- six_exact_probe.py: construct the exact 24-tree query and attempt solving it.
- unfolding.py: existing polynomial encoding dependency.
- six-nearstar.smt2: emitted query, runnable independently with an SMT solver supporting QF_NRA.

Run scripts from this directory. The exact query may require substantial memory; the recorded attempt did not finish normally.
