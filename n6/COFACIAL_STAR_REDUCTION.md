# A shortest-path star fixes every face except one quadrilateral

12 September 2026. A geometric reduction, pending independent review.
It applies to the four cofacial star choices in either remaining type.
It is not a proof that those four choices include a successful whole net.

## General statement

Let v have degree four in a convex six-vertex polytope, and let w be the
sole other vertex not joined to v by an original edge. Suppose v and w
are opposite corners of an original convex quadrilateral Q, whose other
corners are c,d. Consider either original cut tree

    all four original edges at v, together with wc or wd.

Every pair of original faces other than Q has disjoint interiors in either
net. More strongly, their whole connected union has exactly the same
relative placement in a known nonoverlapping shortest-path star unfolding.
Consequently any overlap in either proposed original-edge net involves Q.
No curvature bound or curvature ranking is needed.

## Proof

The straight segment vw lies entirely in the original convex quadrilateral.
It is a shortest surface path: every surface path has length at least the
Euclidean distance |vw|, which this straight segment attains. Each of the
four original edges incident to v is a shortest path for the same reason.
Their interiors are disjoint. Cutting these five paths therefore gives the
classical shortest-path star unfolding at v, which is nonoverlapping.

For the reference theorem, see Kiazyk and Lubiw, *Star Unfolding from a
Geodesic Curve*, SoCG 2015, Definition 1 and Theorem 4. Their definition
explicitly allows the source to be a vertex. This is a new proof of the
Aronov--O'Rourke star-unfolding theorem:
[Published paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SOCG.2015.390)

The reference unfolding cuts Q along vw into triangles vcw and vwd.
Each triangle is a leaf attached to the rest along wc or wd: its two edges
at v are cuts. Remove these two leaf triangles. What remains is a connected
tree of the other original faces, in a nonoverlapping placement.

In the first proposed original tree, wc is cut and Q is attached along wd.
Its two boundary edges at v are still cut. Thus Q is again a leaf, and
removing it leaves exactly the same connected face tree, with the same
uncut hinges, as in the reference unfolding. The relative development of
that tree is unique up to a rigid motion/reflection. Its faces therefore
remain disjoint. The wd-cut option is the reflected argument.

The diagonal vw is used only in this comparison unfolding. It is not a
cut of the final original-edge net. We have not asserted that moving the
quadrilateral to either leaf position preserves its own nonoverlap with
the rest; that is precisely what remains to prove.

## Exact residual pairs for the minus-edge type

Use Q=ACBD and the original face labels

    0=ACBD, 1=ACP, 2=APQ, 3=ADQ,
    4=BDQ, 5=BPQ, 6=BCP.

There are 21 original face pairs. The theorem settles all 15 triangle/
triangle pairs. Four more Q/triangle pairs have a common uncut vertex on
their unique hinge path. Only the following two pairs remain in each tree:

| Source | Fifth cut | Remaining pairs |
| --- | --- | --- |
| A | BC | Q/ACP, Q/APQ |
| A | BD | Q/APQ, Q/ADQ |
| B | AC | Q/BPQ, Q/BCP |
| B | AD | Q/BDQ, Q/BPQ |

Thus **19 of 21 pair obligations are proved universally for each of these
four specified trees**. This is a pair count, not a percentage of shape space.
These are different trees from the older fixed-corner off-quadrilateral
T_P/T_Q pair, whose separate 7/28-class progress is unchanged.

The unrestricted union of all four cofacial choices is false: the exact
witnesses `minus-cofacial-*-failure.certificate.json` certify overlap for
each on the same original solid. Both off-quadrilateral vertices P,Q have
curvature above pi there. An original star at P with the fifth cut DQ
repairs the same solid, with separate exact all-pair verification. The
new reduction remains valid: all four failures involve Q.

## Exact residual pairs for the prism-with-one-diagonal type

Keep faces 0=021, 1=0352, 2=013, 3=1254, 4=143, 5=345.
There are 15 original face pairs. Each source has a different cofacial
quadrilateral; the theorem settles all ten pairs outside that quadrilateral.
Three further pairs have a common uncut vertex. The two residuals are:

| Source | Fifth cut | Movable quadrilateral | Remaining pairs |
| --- | --- | --- | --- |
| 1 | 52 | face 3=1254 | 3/0, 3/2 |
| 1 | 54 | face 3=1254 | 3/2, 3/4 |
| 3 | 20 | face 1=0352 | 1/2, 1/4 |
| 3 | 25 | face 1=0352 | 1/4, 1/5 |

Thus **13 of 15 pair obligations are proved universally in each tree**.
The pre-existing exact example in which both routes at one fixed source
fail is compatible with this reduction. It does not settle the four-tree
family or the sharper-source two-route conjecture.

## Why this is useful for the remaining proof

A test can now concentrate entirely on the quadrilateral that changes
place. It should record which of the two listed triangles that quadrilateral
hits, and how changing the source or its route changes that interaction.
The triangular part needs no new angle analysis. A failed sufficient
curvature test is still not an overlap; the residuals above are exact
geometric obligations.

The implementation `cofacial_star_reduction.py` independently checks the
original convex facets, the specified original cut tree, the cofacial
source, and the common-vertex paths. The theorem dependency is recorded
explicitly; it is not an interval arithmetic proof of the published theorem.

## A whole-net consequence: one remaining Case B is enough

Use a cofacial candidate above, with source v, its opposite w, the route
endpoint c, and the other quadrilateral corner d. Suppose

    kappa_w <= pi,       kappa_c >= pi.

These supply every local, finite-cut, and small-fan premise of the sharp-
slit reduction in ORIGINAL_EDGE_RULE.md. Of its two opposite-petal pairs,
one consists of two faces outside the cofacial quadrilateral. The inherited
star theorem above proves that pair without needing any no-wrap inequality.

There is only one opposite-petal triple left. If its middle base is xy,
its Case B condition is

    kappa_x+kappa_y >= angle(v in the middle triangle).

Under this one condition, the other opposite-petal pair is safe by the
already-proved Case B argument. Both opposite pairs are now safe, so the
finite-cut/boundary-entry reduction supplies the rest of the same whole net.
In particular, **a sharp vertex at either x or y suffices**, because its
curvature is at least pi and the middle triangle angle is strictly below pi.

The exact middle bases are:

| Type | Source / route endpoint | Remaining middle base |
| --- | --- | --- |
| Minus | A / C or B / C | DQ |
| Minus | A / D or B / D | CP |
| Prism | 1 / 2 | 34 |
| Prism | 1 / 4 | 02 |
| Prism | 3 / 0 | 45 |
| Prism | 3 / 5 | 01 |

This is a whole-net sufficient theorem, including equality in the fan,
sharpness and Case B conditions. It does not assert that the remaining
triple must always be in Case B. The proof combines premises of the same
physical net; it does not transfer a successful pair from a different slit.

The implementation `verify_case_B` checks this stronger conclusion. The
next consequences for entire sharp-vertex position patterns are recorded
in SHARP_VERTEX_PATTERNS.md. Their finite counts concern vertex positions,
not fractions of the continuous realization space.

## A further whole-net consequence in Case A

If the remaining triple is in Case A, CASE_A_WIDE_CONES.md now finishes
the net whenever one short cut side has apex angle <=(pi+theta)/2. In
particular, both-short triples and triples with both outer apex angles
nonobtuse are safe. `verify_case_A` checks this use on the original faces.
Exact points and six-parameter affine families of both remaining types
pass the new test while failing the earlier one-sided angle condition.
The still-unresolved geometric pattern has one long side and an obtuse
angle, above the new threshold, on the opposite short side.

## Dependency boundary: an infinite empty wedge is not available

Section 3.2 of the same 2015 paper explicitly reports that an earlier
claim of an entirely empty exterior wedge at a star-unfolding vertex was
false, and repairs a quasigeodesic-loop proof that used it. We use the
valid star nonoverlap theorem, not that refuted stronger claim. Lemma 6's
bounded or partially unbounded W-region is a different statement; it
does not license replacing that region by its whole angular cone.


## A lower-curvature route endpoint also works through the curvature gate

The preceding sharp-endpoint reduction holds under the more general pair
of assumptions kappa_w<=pi and kappa_c+kappa_w>=pi. The gate supplies
2*kappa_c+kappa_w>pi, both finite-cut budgets
kappa_a+kappa_c+2*kappa_w>pi and its reflection, and the small-fan budget
kappa_c+kappa_w>=pi-kappa_v/2. These are exactly the non-Case-A rows of
ORIGINAL_EDGE_RULE.md. Thus all local pairs, both finite cut edges, and
the remaining Case B branch are safe at this same slit. The star comparison
still removes the other opposite pair, since it has no curvature premise.
Consequently the same one-pair Case A test completes a cofacial candidate
under this curvature gate. Equality is included, and all auxiliary diagonals
remain uncut. This extension is used by MINUS_EDGE_PROOF.md.
