# The remaining types: an explicit map of sharp-vertex positions

12 September 2026. Written geometric consequences, pending independent
review. Sharp means curvature **at least pi**, including equality.
The all-at-most-pi theorem already covers both types when their maximum
curvature is at most pi. The counts here concern the remaining domain,
where at least one curvature is strictly greater than pi.

## Result

Both remaining original-face types have an original-edge unfolding whenever
**three vertices are sharp**. They also have one for most two-sharp-vertex
position patterns. The following table is an exhaustive positional ledger:

| Type | Exactly one sharp vertex | Exactly two | Exactly three |
| --- | --- | --- | --- |
| Minus-edge | 2/6 positions proved | 13/15 pairs proved | 20/20 triples proved |
| Prism with one diagonal | 0/6 entire positions proved | 11/15 pairs proved | 20/20 triples proved |

A zero here does not mean there are no proved examples or families. It means
that the whole continuous family with that precise sharp-vertex set has not
been proved by these arguments. These are counts of finite vertex positions,
**not fractions of shape space**. A positional class still contains arbitrary
edge lengths and angles; its being listed does not assert realizability of
every possible curvature assignment.

The full types remain open. The remaining complete positional obligations are:

- Minus, one sharp vertex: C, D, P, or Q.
- Minus, two sharp vertices: {C,P} or {D,Q}.
- Prism, one sharp vertex: any one of 0,1,2,3,4,5.
- Prism, two sharp vertices: {0,1}, {0,2}, {3,4}, or {4,5}.

Thus there are six remaining minus-edge position patterns and ten prism
patterns in this ledger. Symmetry relates several; the table keeps the
original labels so that every geometric case has an unambiguous place.
These are new targets, separate from the older T_P/T_Q failure-class count.

## Why there cannot be four sharp vertices

Each genuine convex vertex has strictly positive curvature, and the six
curvatures sum to 4*pi. Four curvatures at least pi would leave at most zero
for the other two vertices. Thus there are at most three sharp vertices.
This includes equality and uses no genericity or numerical assumption.

## Minus-edge: the covered pairs and the two-sharp-corner theorem

Labels are A=0, B=1, C=2, D=3, P=4, Q=5; the quadrilateral is ACBD.

If A or B is sharp, use that original degree-four source and choose a
maximum-curvature equator vertex c. All four fifth edges are original.
The maximum gives

    2*kappa_c+kappa_w >= 2*pi-kappa_v/2+kappa_w/2 > pi,

because kappa_v<2*pi and kappa_w>0. The high-source weighted-threshold
rule in OCTA_FLAT_HINGES.md therefore supplies an original-edge net.
This covers both single positions A/B and every pair containing either.

Among the other four vertices:

- {P,Q} is covered by source P and fifth edge DQ: Q is a sharp allowed
  endpoint, so the weighted threshold is automatic.
- {C,Q} is covered by source Q with sharp opposite C; the fan alone
  makes the threshold automatic. Similarly {D,P} uses source P.
- **{C,D} is covered by the new cofacial Case B rule.** Their total
  curvature is at least 2*pi. Hence kappa_A+kappa_B<2*pi, since P and Q
  still have positive curvature. Choose the less curved one of A/B as
  the fan w and the other as source v. Then kappa_w<pi. Choose C as
  route endpoint, so the remaining middle base is DQ. Its sharp D
  makes strict Case A impossible. COFACIAL_STAR_REDUCTION.md now proves
  the whole original-edge tree. Choosing D instead also works, using CP.

This proves the entire branch with both degree-three quadrilateral corners
sharp, including both equality boundaries. It does not require A or B to
be a globally sharpest vertex. The only two-sharp pairs not covered are
{C,P} and {D,Q}.

Every set of three sharp vertices contains a covered pair: the two uncovered
pairs are disjoint, so they cannot contain all three pairwise combinations
of any triple. Thus all twenty triple positions are covered.

## Prism: the covered pairs

The original degree-four sources are 1 and 3. Source 1 has opposite 5 and
allowed fifth endpoints 2,3,4. Source 3 has opposite 2 and allowed fifth
endpoints 0,1,5.

If a source is sharp and either its opposite or one allowed endpoint is
sharp, the high-source threshold is automatic. This covers

    {1,2}, {1,3}, {1,4}, {1,5},
    {0,3}, {2,3}, {3,5}.

PRISM_TWO_SHARP_ENDS.md covers {2,5} with its fixed two-pair tree.
Three further pairs use the new cofacial Case B theorem:

- **{2,4}:** if 5 is at most pi, use source 1, fan 5, route endpoint 2.
  The remaining middle base 34 contains sharp 4. If 5 is above pi,
  the sharp-end pair {2,5} supplies the other theorem.
- **{0,5}:** if 2 is at most pi, use source 3, fan 2, route endpoint 5.
  The remaining middle base 01 contains sharp 0. If 2 is above pi,
  use the two-sharp-end theorem.
- **{0,4}:** if 5 is at most pi, use source 1, fan 5, endpoint 4;
  its middle base 02 contains sharp 0. Otherwise, if 2 is at most pi,
  use source 3, fan 2, endpoint 0; its middle base 45 contains sharp 4.
  If both fan vertices are above pi, use the two-sharp-end theorem.

All these are original-edge trees. They cover eleven of the fifteen pairs,
leaving only {0,1}, {0,2}, {3,4}, {4,5}. The graph formed by these four
uncovered pairs has no triangle. Hence every three-vertex set contains a
covered pair, proving all twenty triple positions.

The preceding arguments for a covered pair remain valid when further vertices
are sharp: the fan-curvature alternatives explicitly cover both directions.
There is no assumption that the other four curvatures must be below pi.

## What the finite program certifies

`sharp_vertex_patterns.py` enumerates the 6 singletons, 15 pairs and 20
triples, and records a sufficient written argument for each proved class.
It respects the fan hypothesis: a vertex outside the specified sharp set
has curvature strictly below pi, whereas a vertex inside it is not silently
assumed below pi. The output is `results/sharp-vertex-patterns.json`.

This finite bookkeeping does not replace the geometric theorems. Those are
OCTA_FLAT_HINGES.md, COFACIAL_STAR_REDUCTION.md and PRISM_TWO_SHARP_ENDS.md.
Exact original-face examples and parameter families separately check their
hypotheses and the resulting full nets. No random count enters the proofs.
