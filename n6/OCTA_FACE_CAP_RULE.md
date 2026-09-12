# A shorter octahedron existence proof: put the sharpest vertex at the slit

12 September 2026. A separate simplification found during the requested
review. This is a written research argument under self-audit, pending
independent review. The earlier sharpest-source theorem and all of its
proofs are preserved; the rule below chooses a different cut tree.

## The local geometric criterion

Write v,w for opposite vertices, c=u_0 for the slit endpoint, and
u_1,u_2,u_3 for the other equator vertices in cyclic order. Cut star(v)
and wc. Put

    S_+=kappa_w+kappa_c+kappa_(u_1),
    S_-=kappa_w+kappa_c+kappa_(u_3).

These are the curvature sums on the first and last blue fan triangles,
not sums of the triangles' interior angles.

**Face-cap criterion.** This same net has disjoint face interiors if

    (kappa_v>=pi or kappa_w<=pi),  2*kappa_c+kappa_w>=pi,
    pi<=S_+<=3*pi,  pi<=S_-<=3*pi.                    (C)

Here is its complete deduction from the geometric steps written out in
[TIDY_CORE.md](TIDY_CORE.md):

1. The stated source/fan alternative gives the half-fan bound. Together with the
   weighted slit threshold it proves the three local pairs and strict
   separation from the opposite finite slit segments.
2. A closed remote petal meeting a finite cut would give
   kappa_a+kappa_c+2*kappa_w+2*mu<pi, where a is u_1 or u_3 and mu>0.
   This contradicts the corresponding lower bound S_+>=pi or S_->=pi.
   Only the containment and sine-angle argument E2 is needed; the
   projection argument E1 and the source-curvature case split are omitted.
3. For an opposite-petal Case A with middle base u_1,u_2, the upper bound
   S_-<=3*pi gives
   kappa_v+kappa_(u_1)+kappa_(u_2)=4*pi-S_->=pi.
   Thus the source angle sum is at most pi plus those two base curvatures,
   exactly the condition that both outer apex angles are at most theta.
   The other triple uses S_+<=3*pi in the same way. Both Case A pairs
   are safe by the apex-cone proof.
4. The base-cone Case B already needs no source condition. In the small-fan
   pocket, the simple hexagon gives nu_0>S_+ (or S_- after reflection),
   contradicting the lower bound pi because nu_0 is a triangle angle.
   No intermediate obtuse-angle or high/low source argument is needed.
5. The four boundary checks finish the remaining petal/fan pairs. Together
   with the 19 shared-vertex pairs these settle all 28 pairs of this net.

This is a reorganization of proved geometric steps, not a numerical
inference or a new assumption that local pairs alone imply global safety.
All the containment, orientation and finite-edge premises in the cited
core are retained. Curvature and angle equalities are included. Flat uncut
auxiliary hinges are permitted, although only genuine octahedra are needed
for the existence statement below.

## A curvature-only selection that always meets the criterion

Choose a vertex c of largest curvature M and write m for the curvature
of its opposite vertex. The other two opposite pairs have curvatures
(A,a) and (B,b), labeled so A>=a and B>=b. Thus

    M+m+A+a+B+b=4*pi,   0<each curvature<2*pi.

There are two proposed openings:

| Fan w | Source v | Slit endpoint | Larger incident blue-face sum |
| --- | --- | --- | --- |
| vertex with curvature a | its opposite, with curvature A | c | U_1=M+a+B |
| vertex with curvature b | its opposite, with curvature B | c | U_2=M+b+A |

Choose the opposite pair with the **larger curvature difference**, using
its sharper endpoint as source v and its other endpoint as fan w. Equivalently,
choose the smaller of U_1,U_2, because

    U_1-U_2=(B-b)-(A-a).

The one identity needed to bound the selected cap is

    U_1+U_2=4*pi+M-m<6*pi,

since M<2*pi and m>0. Therefore the smaller U is strictly below 3*pi.
Ties in the two differences cause no difficulty: either proposal then has
the same U<3*pi. No case analysis of high fan curvatures is needed: the
orientation kappa_v>=kappa_w guarantees the half-fan hypothesis. If w is
at most pi it holds directly; otherwise v is also greater than pi.

For the chosen proposal, both blue-face sums are at most its U, so their
upper bounds in (C) hold. Every triple containing c has curvature sum
strictly greater than pi: otherwise M<pi, and the three complementary
vertices also have curvature below pi, making the total less than 4*pi.
This gives both lower bounds without a high/low case split.
Finally M>=2*pi/3 by the average curvature, so

    2*M+kappa_w >= 4*pi/3+kappa_w > pi.

Every premise of (C) is satisfied. All five cuts are original octahedron
edges. This proves existence of a nonoverlapping original-edge net for
every convex octahedron, by a rule involving only vertex curvatures.

## Why this version is shorter

The sharpest vertex is now the endpoint c of the extra cut, rather than
necessarily the source whose four incident edges are cut. Its large
curvature makes the local slit threshold automatic. Only the curvature differences of two opposite pairs
need to be compared, and the two face-cap sums coordinate the finite-edge
and opposite-petal arguments at the same opening.

For this existence proof, the geometric core needs the half-span
lemma with a source at least as sharp as its fan, the local separator,
finite-entry containment and sine inequality,
opposite-petal cone/pocket arguments, and the four final boundary checks.
It does **not** need the projection contradiction E1 or either source-
curvature case split. The original theorem about a sharpest source and a
maximum-curvature equator slit remains a stronger result about that
particular selection and is preserved. The present rule does not prove
that every slit works.

The curvature selection argument is valid for all six positive numbers
below 2*pi summing to 4*pi; it assumes no metric realization of arbitrary
such numbers. Actual convex octahedra supply the required curvatures and
opposite pairs. Exact coordinate examples check the selected nets
independently and are not the proof of this universal selection lemma.

The first draft restricted the fan itself to curvature at most pi and
selected a passing cap sum. It is preserved in
[the readable low-fan draft](OCTA_FACE_CAP_LOW_FAN_DRAFT.html), with its
code and exact examples in the [archive](archive_notes/octa-face-cap-low-fan/README.md).
The sharper-pole orientation removes that restriction and the extra
selection cases. An implementation on a parameter box may certify either
of the two proposals directly from (C), even if their difference ranking
changes inside the box; that is the same sufficient geometric criterion.

There is also a useful reading of the same budget. The smaller curvature
sums on the two petal triangles opposite c would be L_1=m+A+b or
L_2=m+B+a. The more unequal pole pair chooses the larger L, and
L_1+L_2=4*pi-M+m>2*pi. Thus both of those petals have curvature sum
above pi. The other petals contain c and already have that property.
The rule makes all four petals and the two blue triangles beside the slit
carry the curvature budgets needed by the geometric proof.

## Final review update: the difference comparison can also be removed

The [paired-pole theorem](PAIRED_POLE_RULE.md) now supplies the missing
wider Case A bounds from a positive identity. It proves the unranked
choice too, and simplifies the minus-edge graph. The complete cap proof
above remains correct; its former open-shortcut note and the preceding
version are preserved in archive_notes/OCTA_FACE_CAP_RULE_before_paired.md.
