# A tempting prism shortcut fails, even at the unique sharpest vertex

12 September 2026. An exact counterexample found during the simplification
review. This is a failure of one proposed selection rule, not of edge
unfoldability. The full five-tree proof and its angle rule remain valid.

The four cofacial routes use sources 1 and 3, the opposite corners of the
two quadrilateral faces. A tempting shorter rule is: choose the sharper
source, then try its two routes around its quadrilateral. The example below
shows that even choosing the **unique sharpest vertex of the entire solid**
does not make those two routes sufficient.

Keep the original faces A=021, B=0352, C=013, D=1254, E=143, F=345.
Here are integer coordinates:

| Vertex | x | y | z |
| --- | ---: | ---: | ---: |
| 0 | 200 | 0 | 0 |
| 1 | -1400 | 200 | 0 |
| 2 | 0 | 0 | 0 |
| 3 | 600 | 160 | 1000 |
| 4 | -180 | 98 | 550 |
| 5 | -5 | 4 | 25 |

The exact verifier checks strict convexity, every original facet, and that
vertex 1 has strictly greater curvature than each of the other five.
Nevertheless both its cofacial routes overlap:

| Cut tree | Exact outcome |
| --- | --- |
| star(1)+25 | Positive-area overlap of A and D |
| star(1)+54 | Positive-area overlap of D and E |
| star(3)+20 | All 15 original face pairs safe |
| star(3)+25 | All 15 original face pairs safe |
| T={02,12,25,35,45} | Both cap sums exceed pi; the cap rule selects T, whose 15 pairs are independently safe |

The first failure cuts 01,12,13,14,25. The second replaces 25 by 45.
The overlap claims concern the complete original quadrilaterals. They are
not artifacts of cutting an auxiliary diagonal or substituting a triangle
for a face.

The counterexample is also certified on a neighborhood with all nine
parameters varying: use the original prism chart centered at

    (-7, 1, -1/40, 1/50, 1/8, 4, 40, 1/20, 22),

with independent half-width 1/10^10 in each parameter. The same two nets
have positive-area overlap throughout this box, vertex 1 remains uniquely
sharpest, and both other-source nets and T remain safe. The point certificate
uses the displayed integer coordinates divided by 200, a similarity.

## What this changes, and what it does not

A complete original-edge rule must allow a change of source, a different
fifth edge, or another fallback. Our cap rule does exactly that: it selects
T here. This example does not refute the four cofacial routes taken together,
and it does not prove that the five-tree family is minimal. Those are
separate questions. It also does not refute the octahedron's sharpest-source
rule, which is permitted to choose a different fifth edge; here that would
be the original edge 35.

The discovery search tested 100,000 numerical shapes and found no failure
of all four cofacial routes. That absence proves nothing about their universal
sufficiency. The positive overlap statements above instead come from exact
outward rational interval certificates, checked against every edge axis
of each of the two convex faces.

## Reproduction and preserved evidence

Run `python3 -m n6.sharpest_cofacial`. The code independently reconstructs
and checks the point and parameter family; it does not trust the search.

* [Exact point, family, curvature order and all five outcomes](results/prism-sharpest-cofacial.verification.json).
* [First failed route, point](results/prism-sharpest-cofacial-failure-source-1-slit-2.certificate.json).
* [Second failed route, point](results/prism-sharpest-cofacial-failure-source-1-slit-4.certificate.json).
* [First failed route, nine-parameter box](results/prism-sharpest-cofacial-failure-source-1-slit-2-family.certificate.json).
* [Second failed route, nine-parameter box](results/prism-sharpest-cofacial-failure-source-1-slit-4-family.certificate.json).
* [Preserved numerical search](results/prism-four-candidate-review-probe-20260912.json).
* [The five-tree cap proof](PRISM_CAP_RULE.md) and [complete shorter proof](TIDY_PROOF.md).

This exact example limits a shortcut. It is not an independent review of
the universal five-tree geometric argument.
