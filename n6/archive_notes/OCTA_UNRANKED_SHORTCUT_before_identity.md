# A further octahedron shortcut, not yet proved

12 September 2026. Retained from the proof-simplification review. This is an
optional research direction, not part of the written existence proof.

The [new face-cap rule](OCTA_FACE_CAP_RULE.md) chooses a sharpest vertex c,
then selects the more unequal of the other two opposite pairs. Its sharper
endpoint is the star source v; the other endpoint w is joined to c by the
fifth cut. The comparison of differences is a short, proved way to make
two required face-curvature sums at most 3*pi.

Could that comparison be omitted? The tempting stronger claim is:

> Choose either of the two opposite pairs not containing a sharpest vertex c.
> Orient it so kappa_v>=kappa_w. Then star(v)+wc always unfolds.

This has **not** been proved here. The lower face-cap bounds, half-fan
hypothesis and weighted slit threshold still hold. The upper face-cap
bounds need not hold, so the current Case A proof does not finish this
stronger rule. Failure of an upper bound is not failure of the unfolding.

## An exact example shows the missing implication

Use these integer coordinates, with their convex-hull octahedral facets:

| Vertex | x | y | z |
| --- | --- | --- | --- |
| 0 | 0 | 0 | 0 |
| 1 | 49 | -55 | -22 |
| 2 | -12 | 16 | 14 |
| 3 | 0 | -4 | 2 |
| 4 | 5 | -10 | -2 |
| 5 | 18 | -20 | -12 |

The [exact check](results/octa-unranked-cap-failure.verification.json)
certifies that c=1 is sharpest and kappa_5>=kappa_3. Thus the unranked
choice v=5,w=3 passes its proposed selection assumptions. Nevertheless

    kappa_0+kappa_4+kappa_5 < pi,

so the complementary blue face has

    kappa_3+kappa_1+kappa_2 > 3*pi.

The necessary premise of the current face-cap proof is therefore absent.
This is an actual metric example, not an abstract assignment of curvatures.
Its whole net still has all 28 face pairs independently certified safe;
see the [standalone certificate](results/octa-unranked-cap-failure.certificate.json).
The canonical larger-difference rule instead chooses v=2,w=4,c=1 and
passes its cap inequalities. The report records that comparison too.

This example refutes only the claim that the unranked choice automatically
passes the stated cap criterion. It does not refute the unranked unfolding
rule, or indicate any gap in the canonical rule's proof.

## Numerical investigation, kept outside the proof

A [bounded probe](results/octa-face-cap-shortcut-probe-20260912.json)
checked both choices on 80,000 floating-point-screened octahedra. Its nine
non-shared-vertex pair scores reported separation for both choices on all
samples. The canonical choice had a fan above pi in 121 samples and lay
outside the older high-source-or-all-low condition in 42,434 samples.
These are sample counts, not a count of proved geometric cases or a
coverage percentage. Absence of a sampled failure establishes no theorem.

The high-fan branch was also simplified to a small integer example and
checked exactly, separately from those floating results. It is included in
the [ten face-cap point/domain checks](results/octa-face-cap-rule.verification.json).
The more focused numerical search of the unranked choice is retained in
`results/octa-unranked-targeted-review-20260912.json`; any optimizer result
is only a proposal for exact follow-up. The scripts are preserved in
`archive_notes/proof-review-octa-*.py.txt`.

The shortest justified proof currently keeps the curvature-difference
comparison. A further shortening would need a new Case A separator for
these failed-cap choices, rather than more numerical successes.
