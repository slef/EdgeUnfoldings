# Low curvature: safe local pairs imply a safe whole octahedral net

11 September 2026. Written conditional geometric theorem, with boundary
contacts treated below. Independent mathematical review is still needed.
Numerical surveys are not premises.

## Statement

Let every vertex of a convex octahedron have curvature at most pi. Choose
any source v, its opposite w, and any slit wc. In this particular net,
assume the three local pairs have disjoint interiors:

    V_k / V_(k-1),   V_k / W_(k-1),   V_(k-1) / W_k.

Then all six far pairs also have disjoint interiors, so the whole net is
nonoverlapping. Neither the globally sharpest source condition H nor the
maximum-curvature slit condition R is required.

Equivalently, under the all-low-curvature condition, a positive-area far
overlap forces at least one positive-area local overlap at that same slit.
This does not prove the original every-slit Lemma F: the premise may fail
at a different slit. It is a replacement for the older unrestricted
conditional far-fan implication only on the stated curvature family.
The historical counterexample has curvature greater than pi and lies
outside this family.

## 1. The finite cut edges are safe

The through-fan bound of Lemma L applies because kappa_w<=pi; it does not
require the chosen slit to satisfy R. Thus a distant petal can meet its
finite cut target only by extending backward across the gap, after
reflection if necessary.

Use a,w,p,M,P and the neighboring patch Q_m from LEMMA_F_CHORD.md.
The only local premise needed to trap Q_m in triangle(w,a,p) is the
relevant local mixed-pair safety, already assumed here. Shared-vertex
separation and the reflex-corner identity supply its other barriers.
Boundary contact is allowed in the closed containment.

The two equal cut-edge lengths give

    2*theta+2*delta+kappa_a < pi

for a hypothetical crossing. The all-low-curvature bound and the
neighboring blue-face angle inequality give the opposite strict bound,
exactly as in Sections 3-4 of LEMMA_F_CHORD.md. No curvature ranking is
used there. Both finite-cut conditions therefore hold.

## 2. The opposite-petal angle partition still applies

Case A's no-wrap bound follows from the all-low assumption rather than H:

    kappa_u+kappa_u' >= pi-kappa_v,
    pi+kappa_u+kappa_u' >= Gamma_v >= nu_i+nu_j.

This is the source-choice audit in OCTA_SOURCE_CHOICE.md. The apex-cone
argument closes Case A, and the base-cone branch has no ranking premise.
Only the small-fan-angle branch remains.

In that branch, the finite-cut condition and the assumed local pairs
make the quadrilateral Gamma=a,p,b,w simple for a point p inside a
hypothetical opposite-petal overlap. Its interior faces the fourth patch
Q_m, which cannot cross Gamma. The containment argument is the one in
LEMMA_F_CUT_REDUCTION.md and uses the local pairs, not their particular
R-based proof.

## 3. An auxiliary shrink handles boundary contact without R

Removing Q_m from Gamma gives the usual six-sided boundary walk

    a -> p -> b -> w -> c -> M -> a.

The R-based proof established strict separation of M from the opposite
slit edge wb. We cannot assume that stronger statement here. The point M
may touch wb, including its endpoint b, without a local interior overlap.

The other contacts are excluded as before. The slit copy c is strictly
inside Gamma: it is on a distinct radial direction from its radial sides,
and an intersection with ap or bp would place a boundary point of a safe
face strictly inside the other petal. The same observation excludes M
from the open segments ap and bp. M is not on wa, since the positive
patch corner at a is strictly below 2*pi and therefore its ray differs
from aw. The fourth patch meets Gamma along wa and possibly at M on wb.

If that last contact occurs, replace M by M_epsilon slightly toward an
interior point of triangle acM. Keep a,c,w and Gamma fixed. The smaller
orange triangle acM_epsilon is contained in the old one, and its new apex
is strictly inside Gamma. It cannot create a new boundary crossing.
For sufficiently small epsilon, the positive angular gap at a stays
positive. The gap at w is unchanged. The resulting six-sided region is
simple, so its ordinary angle sum applies.

This is an auxiliary planar perturbation of one triangle, not a claim
that the altered pieces realize a convex octahedron. In the angle identity,
replace the face angles at a,c,M by those of the smaller triangle, and
define the corresponding angle deficits at a,c by the same angle sums.
They converge to the original angles and curvatures. Taking epsilon to
zero gives the original identity even at contact:

    nu_m = kappa_a+kappa_c+kappa_w+gamma+delta_a+delta_b
         > kappa_a+kappa_c+kappa_w.

The strictness remains because p is an interior overlap point and its
angle gamma is strictly positive. No strict local clearance or general
position of the original solid is assumed.

## 4. The all-low bound replaces R in the final contradiction

The vertices w,c,a form the fourth blue face. Its three complementary
vertices have total curvature at most 3*pi, so

    kappa_a+kappa_c+kappa_w >= pi > nu_m.

The last strict inequality is just the nondegeneracy of the orange
triangle's angle at M. This contradicts the preceding identity. R is
unnecessary in this final step.

Both opposite-petal pairs are now safe. Each cut-side blue target has
all three boundary-entry routes excluded: its finite slit edge by
Section 1, its other radial edge by a shared vertex, and its equator
edge by the opposite-petal result. The two interior blue targets follow
from the valid interior-hinge reduction, with the local premises retained.
Together with the 19 shared-vertex pairs, all 28 pairs are accounted for.

The exact checker `low_far.py` independently verifies the all-low
curvature bounds, the selected tree, and all three local separating
witnesses on an explicit domain. Its whole-net conclusion invokes this
written conditional proof. Missing or unresolved local checks are not
accepted, and a failed sufficient check is not reported as an overlap.


## 5. The local-failure branch is nonempty even under H

The explicit integer-coordinate solid in `low_local_failure.py` has source
v=5, opposite w=3, equator (0,4,1,2), and slit c=2. Exact outward interval
checks verify every curvature is strictly below pi and v is globally
sharpest. Curvatures in vertex order, rounded only for readability, are
approximately (157.54,170.52,2.29,48.04,170.52,171.09) degrees.

Its local face pairs (3,4) and (3,7) have positive-area overlap. Every other
pair, including all six far pairs, is certified nonoverlapping. Thus this
is a counterexample to the stronger assertion that H makes *every whole
net* safe in the all-low family. It is not a counterexample to the original
far-only Lemma F: all its far pairs are safe. It also shows why one cannot
apply the conditional theorem at an arbitrary slit by silently importing
Lemma L from a different slit.

The slit is much less sharp than the other equator vertices, so R fails.
Changing to a maximum-curvature slit gives an independently certified
all-28-pair successful net of the same polyhedron. The failed local
certificate is a rejection regression test, not numerical evidence being
promoted to proof.

Replay `python3 -m n6.low_local_failure`. The checker reconstructs the strict
convex hull and tree, checks H and all-low curvature, checks both positive
area overlaps and all 26 safe pairs, and rejects incomplete pair lists.
