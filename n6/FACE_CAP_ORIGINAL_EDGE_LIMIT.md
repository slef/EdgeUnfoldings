# Why the new octahedron cap rule is not automatically an original-edge rule for every type

12 September 2026. A preserved limitation of the attempted further
simplification. The new octahedron rule is proved on its stated graph.
Applying it to a flat completion of a nonsimplicial type may cut an added
diagonal. The original whole six-vertex proof is therefore retained.

For the minus-edge completion, use opposite pairs (A,B), (C,Q), (D,P).
The added diagonal is CD. The following **abstract curvature assignment**,
in units of pi, satisfies positivity, each curvature below 2, and total 4:

    A=39461/20000, B=1/20, C=19/200,
    D=P=1881/2000, Q=19/20000.

A is largest. Between the two remaining opposite pairs, (C,Q) has the
larger curvature difference, so the new octahedron rule cuts the star at
C, followed by QA. That star includes the auxiliary diagonal CD. It
therefore does not give an original-edge net of the minus-edge graph.

For these numbers, none of the 14 original near-stars satisfies the face-cap
criterion, and neither of the old complementary-source gate pairs applies.
This was checked using exact fractions. An earlier coarse rational grid
had found no uncovered assignment; this example illustrates why that finite
check was not a proof of coverage.

This is **not a claimed realization by a convex minus-edge polyhedron**,
and it is not a counterexample to unfoldability or the completed proof.
It establishes only that positivity, the vertexwise 2*pi bound and total
curvature alone do not justify the proposed automatic transfer. More metric
information or a different selection argument would be needed. The existing
minus-edge proof supplies its own original-edge choices, and the prism has
its separate cap and angle switches.

The initial exact grid check and this explicit failed transfer are recorded
in [the preservation report](results/face-cap-original-edge-limit.json).
The original source-curvature proof, including projection E1, remains in
[TIDY_CORE.md](TIDY_CORE.md). The new [octahedron cap proof](OCTA_FACE_CAP_RULE.md)
can omit that step for its standalone existence argument.
