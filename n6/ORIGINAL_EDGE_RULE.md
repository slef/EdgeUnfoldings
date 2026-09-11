# Applying the octahedron rule to the last two original-face types

**Later completion in the same continuation:** [PRISM_EDGE_PROOF.md](PRISM_EDGE_PROOF.md)
and [MINUS_EDGE_PROOF.md](MINUS_EDGE_PROOF.md) close both whole types as written
research arguments, pending independent review. Any remaining-case count below
records this ingredient's earlier scope. The underlying theorem remains valid.


12 September 2026. New sufficient geometric theorem and an explicit residual
case reduction. These are written arguments depending on the existing
octahedron proof and flat-hinge audit; independent mathematical review is
still needed. Numerical searches are not proof premises. Neither remaining
combinatorial type is claimed complete.

## 1. The question is which part of the rule fails

Complete the original polygonal surface to the octahedron graph by adding
the unique permitted quadrilateral diagonals. These are bookkeeping hinges,
not allowable cuts. There are exactly **14 original degree-four-star-plus-one
trees for the minus-edge type**, and **6 for the prism-with-one-diagonal type**.
These are candidate counts, not a partition or percentage of shape space.

The earlier theorem accepts a candidate if its source curvature is at least
pi, or every curvature is at most pi, and its fifth edge wc satisfies
2*kappa_c+kappa_w>=pi. Its rejection says nothing about actual overlap.

There are two genuinely different obstacles to the naive adaptation:

* The globally sharpest vertex can have only three original edges.
* Even at an original degree-four source, the equator maximum can require
  an artificial fifth cut. Choosing the sharpest *allowed* endpoint instead
  can produce real overlap, as the exact failures in Section 5 show.

We therefore audit the individual inequalities of the proof, rather than
assume that rejecting the old source condition means the tree fails.

## 2. A curvature-budget theorem without a source ranking

Let the octahedral equator, starting at the physical slit, be (c,a,d,b).
The source is v and its opposite is w. All vertices are genuine vertices;
flat auxiliary hinges are allowed as in [OCTA_FLAT_HINGES.md](OCTA_FLAT_HINGES.md).
Suppose the following inequalities hold:

| Purpose | Sufficient condition |
| --- | --- |
| Through-fan separation | kappa_w <= pi |
| Local slit pairs and their boundary separation | 2*kappa_c+kappa_w >= pi |
| First finite-cut exclusion | kappa_a+kappa_c+2*kappa_w >= pi |
| Last finite-cut exclusion | kappa_b+kappa_c+2*kappa_w >= pi |
| First Case A no-wrap bound | kappa_v+kappa_a+kappa_d >= pi |
| Second Case A no-wrap bound | kappa_v+kappa_d+kappa_b >= pi |
| Small-fan opposite-petal contradiction | kappa_c+kappa_w >= pi-kappa_v/2 |

Then **star(v) plus wc is nonoverlapping**. There is no maximum-curvature
source or slit premise. All displayed equalities are included. If the five
cuts are original edges, this unfolds the original polygonal faces whole.

### Local pairs

The through-fan proof in Section 3 of [Lemma L](LEMMA_L_PROOF.md) works
whenever the fan curvature is at most pi, at every needed equator vertex.
The second row supplies the slit-edge separator from
[OCTA_SLIT_THRESHOLD.md](OCTA_SLIT_THRESHOLD.md), including its strict
separation of a flank petal from the opposite closed slit segment.
Thus the three local pairs are safe at this same physical slit.

### Finite cuts

Apply the neighboring-patch containment and equal-radius argument of
[LEMMA_F_CHORD.md](LEMMA_F_CHORD.md), Sections 1–3. It uses the local
premises just supplied, not the old source ranking. A crossing would imply

    kappa_a+kappa_c+2*kappa_w+2*mu < pi,

where mu is a strictly positive face angle. The third row contradicts
this strictly, even at equality. Reflection gives the fourth-row exclusion.
No claim that all six curvatures are below pi is used here.

### Opposite petals

There are two triples in the opened order: patches (0,1,2) and (1,2,3).
Their middle bases are ad and db. In Case A the only extra hypotheses of
[CASE_A_CONES.md](CASE_A_CONES.md) are

    nu_left+nu_middle <= pi+kappa_u+kappa_u',
    nu_right+nu_middle <= pi+kappa_u+kappa_u'.

Each left side is at most Gamma_v=2*pi-kappa_v. Rows five and six give
these bounds at the two respective middle bases. The planar equal-edge
distance-sum argument then excludes Case A. The base-cone branch needs no
curvature ranking.

In the small-fan branch, the finite-cut and local premises make the
auxiliary quadrilateral simple and trap the fourth patch. The strict local
boundary fact supplies the same contact audit as LEMMA_F_CHORD.md. The
remaining simple six-sided region would require

    nu_m > kappa_a+kappa_c+kappa_w

or its reflected version with b. But the convex-vertex cone inequality
gives nu_m<=pi-kappa_v/2<=kappa_c+kappa_w. Since kappa_a,kappa_b>0,
there is a strict contradiction. This handles equality in the last row.

### Whole net and original facets

The 19 shared-uncut-vertex pairs, three local pairs, two opposite-petal
pairs, and four remaining petal/fan pairs now follow in exactly the audited
order in LEMMA_F_CHORD.md. For the last four, the two finite-cut exclusions,
opposite-petal separation, and the surviving interior-hinge implication
exclude each possible boundary entry. The historically refuted unrestricted
hinge implication is not used.

All artificial diagonals stay uncut. Their two developed triangles rejoin
their original quadrilateral. A positive-area overlap of original faces
would give a triangle-interior overlap away from the finitely many diagonal
segments. Thus the resulting original-edge net is nonoverlapping.

## 3. A particularly simple sharp-slit rule

Suppose an original candidate has

    kappa_c >= pi,       kappa_w <= pi.

Then the local threshold, both finite-cut inequalities, and the small-fan
budget are automatic. It remains only to check

    kappa_v+kappa_a+kappa_d >= pi,
    kappa_v+kappa_d+kappa_b >= pi.                 (N)

If both hold, the original-edge net is proved safe. The sharp vertex is
the endpoint of the fifth cut; it need not be the four-cut source.

Even if (N) fails, this is a useful reduction: **only the two opposite-petal
pairs still need direct proof, and only their Case A branches can be open**.
For either pair, the actual weaker apex-angle inequalities displayed above
can replace its curvature bound. If its middle-curvature sum is at least
its middle apex angle, it is in Case B and is already settled. Thus a
remaining overlap must be in Case A and violate at least one actual
no-wrap inequality. A failed sufficient curvature sum alone is not an overlap.

Once the two opposite-petal pairs are safe, the same boundary-entry
arguments give all other pairs. This is a conditional reduction at the
same slit; it does not assert that a safe alternate slit automatically
supplies a missing premise here.

This tells us where to push next: try another original source or slit
against the remaining Case A pair. Configurations with no original
candidate having a low-curvature fan and a sharp slit require another
argument. The prism branch with both possible fan vertices sharp is now
settled by [PRISM_TWO_SHARP_ENDS.md](PRISM_TWO_SHARP_ENDS.md), using a
different original cut tree. The broader sharp-slit Case A step remains open.

## 4. Two explicit new families, outside the old source conditions

The exact examples use these integer coordinates:

| Vertex | Minus-edge example | Prism example |
| --- | --- | --- |
| 0 | (0,0,0) | (40,20,-20) |
| 1 | (20,20,0) | (20,40,-20) |
| 2 | (40,-20,0) | (0,0,0) |
| 3 | (-20,40,0) | (28,4,16) |
| 4 | (25,-5,-20) | (0,20,20) |
| 5 | (-5,25,-20) | (-20,-20,40) |

Faces are MINUS_FACES and PRISM_FACES in families.py. For minus, take
v=0,w=1,c=2; for prism, take v=3,w=2,c=5. In both examples every original
degree-four vertex has curvature below pi, while a degree-three vertex
has curvature above pi. Consequently **none of the old candidates meets
its source condition**. The new original-edge rule does apply.

These examples extend to independent ten- and nine-parameter chart boxes
of radius 1/1000, after the indicated fixed affine changes. The certificate
generator and verifier check all hypotheses throughout each closed box,
and independently check every original face pair. These are explicit
illustrations of the theorem, not premises of its universal argument.

## 5. An actual failure of the naive original-edge adaptation

Define the attempted deterministic rule precisely:

1. Choose the sharpest original degree-four vertex v.
2. Among original neighbors c of its opposite w, maximize kappa_c.
3. Cut star(v) and wc.

**This rule fails in both types.** Exact rational examples are retained in
`original-rule-*-selected-failure.certificate.json`. Their original facets,
strict source and allowed-slit rankings, and positive-area overlap are
independently checked. The selected tree is therefore a real failure,
not merely a rejected curvature test. Both same solids also have an
original-edge repair with a separate all-pairs certificate.

The minus witness selects source 5, opposite 2, allowed slit 1. The prism
witness selects source 1, opposite 5, allowed slit 2. Their useful equator
maxima require an artificial fifth edge. Keeping only the sharpest allowed
endpoint does not repair that restriction.

The floating search files are explicitly diagnostic, not proof or coverage.
They keep the random seed, integer projective data, sample counts,
tolerances, and numerical failures separately. The exact certificate
replays do not trust their floating scores or reported rankings.

## Reproduction and remaining scope

    python3 -m n6.original_edge_examples
    python3 -m unittest n6.tests.test_original_edge_rule

The selected-star family has 14 or 6 candidates; the new tests prove some
additional whole shape families and reduce sharp-slit failures to specific
Case A obligations. **There is still no proof that the union of the
original candidates always succeeds.** Full types remain 5/7. A fallback
covering every remaining shape, including equality and limiting regimes,
is the next mathematical obligation.
