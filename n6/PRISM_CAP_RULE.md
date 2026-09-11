# Five prism candidates, organized by the two cap curvatures

12 September 2026. A new simplification found during the requested proof
review. This is a written geometric argument under self-audit, pending
independent review. The earlier seven-candidate proof and all of its
material remain available in [PRISM_EDGE_PROOF.md](PRISM_EDGE_PROOF.md).

## A sufficient condition for the familiar two-pair tree

Keep the original faces

    A=021, B=0352, C=013, D=1254, E=143, F=345,

and the tree T={02,12,25,35,45}. Its only potentially overlapping pair
is B/D, by [the reference-star comparison](PRISM_ONE_PAIR.md). Define

    C_A=kappa_0+kappa_1+kappa_2,
    C_F=kappa_3+kappa_4+kappa_5.

These are sums of original vertex curvatures, not face angles. They obey
C_A+C_F=4*pi.

**Cap theorem.** If C_A>=pi and C_F>=pi, T is nonoverlapping. Both
equalities are included. In particular, T works whenever all six vertex
curvatures are at most pi: each cap's complement then sums to at most 3*pi.

Here is the proof. View B/D around either triangular cap, with apex p,
middle angle nu, outer quadrilateral apex angles lambda,rho, and sum K
of the two base curvatures. Because p has degree three,

    lambda+rho+nu=2*pi-kappa_p.

In Case A put theta=pi-nu+K. Then the exact identity is

    2*lambda+nu-2*pi-K = lambda-rho-(kappa_p+K),

and similarly with lambda and rho exchanged. The three curvatures on
the right sum to that cap's C. Each original convex quadrilateral has
0<lambda,rho<pi. Thus C>=pi makes both expressions strictly negative.
Equivalently, both outer angles are below (pi+theta)/2. The wider
Case A cone lemma therefore separates B/D in that view.

Both views' Case A branches are safe. Their central angle sums are
Sigma_A=pi-C_3+E_1 and Sigma_F=pi-E_1+C_3, so their sum is 2*pi.
Choose a view with Sigma>=pi. If it is Case B, the base-cone lemma
separates B/D; if it is Case A, the preceding argument does. Hence T
is a whole original-edge net. All cone arguments use the full original
quadrilaterals, not triangles standing in for them.

## What a failed cap condition forces

If the cap theorem does not apply, exactly one cap has curvature sum
below pi, and the other has sum above 3*pi. Reflect the labels if
necessary so

    C_A>3*pi, C_F<pi.

In particular kappa_3,kappa_4,kappa_5<pi. There are only two branches:

1. **kappa_2>=pi.** The existing sharp-fan switch applies. One of
   N=star(1)+25 and T is safe.
2. **kappa_2<pi.** Since kappa_1<2*pi,
   kappa_0+kappa_2=C_A-kappa_1>pi. Also
   kappa_0+kappa_1=C_A-kappa_2>2*pi. These imply every hypothesis
   of the existing curvature-gate switch. One of M=star(3)+20
   and T is safe.

For the reflected orientation exchange 0 with 4, 1 with 3, and 2 with 5.
The two alternatives become star(3)+25 or star(1)+54, respectively.
Reflection fixes T. Thus the complete fixed candidate family is

    T,
    star(1)+25, star(1)+54,
    star(3)+20, star(3)+25.

Every cut is an original edge. Neither flat auxiliary diagonal 05 or
24 is cut. This proves the five-candidate theorem, provided the two
switch lemmas and shared geometric core stand up to independent review.
For a given shape the cap rule requires at most two candidates: T and
one indicated near-star. It does not require trying all five on that shape.

## A concrete decision table

| Curvature situation | Candidates containing a complete net |
| --- | --- |
| Both cap sums at least pi | T alone |
| C_A>3*pi and kappa_2>=pi | star(1)+25, T |
| C_A>3*pi and kappa_2<pi | star(3)+20, T |
| C_F>3*pi and kappa_5>=pi | star(3)+25, T |
| C_F>3*pi and kappa_5<pi | star(1)+54, T |

The first row includes cap sum exactly pi; the high-curvature switch
includes end curvature exactly pi. No equality is discarded and no
curvature-preserving perturbation is assumed. The two switches provide
their own angle tests for selecting between their indicated near-star
and T; alternatively each of the two whole nets can be checked exactly.

The angle selection is particularly short after reflecting to C_A>3*pi.
If kappa_2<pi, choose star(3)+20 when F_3<=pi/2 and T otherwise.
If kappa_2>=pi, set K=kappa_3+kappa_4 and choose star(1)+25 when
K>=E_1, E_1<=pi/2, or 2*D_1+E_1<=2*pi+K; otherwise choose T.
These are precisely the closed sufficient tests and their proved fallback
in the two switches. Thus the angle rule chooses **one** successful tree
without first computing any planar overlap. The independent coordinate
checker remains useful for verifying explicit implementations and domains.

The previous seven-candidate theorem remains correct as a weaker statement.
Its two noncofacial near-stars are unnecessary for this new proof. We have
not proved that five is minimal, that the four cofacial stars suffice by
themselves, or that T works outside the sufficient cap condition. The saved
counterexamples to T are preserved and remain counterexamples to a fixed
tree, not to edge unfoldability.

A new [exact counterexample](SHARPEST_COFACIAL_FAILURE.md) also shows why
one cannot simply keep the two cofacial routes at the sharper source:
both can overlap even when that source is the solid's unique sharpest
vertex. The cap rule selects T on that example. The four cofacial routes
together are not refuted by it.

The underlying identity also gives a stronger optional angle-difference
test and a reusable three-face-source lemma. They are retained separately
in [CASE_A_CAP_BUDGET.md](CASE_A_CAP_BUDGET.md), so the main rule can stay
in its simpler curvature-only form.

## Sources and checking boundary

The two switches are [PRISM_SHARP_FAN_SWITCH.md](PRISM_SHARP_FAN_SWITCH.md)
and [PRISM_GATE_SWITCH.md](PRISM_GATE_SWITCH.md). Their shorter presentation,
including the exact identities used in the sharp-fan branch, is retained
in [TIDY_PROOF.md](TIDY_PROOF.md). The cone lemmas are proved in
[TIDY_CORE.md](TIDY_CORE.md), with the original longer arguments preserved.

Exact algebra checks the displayed cap identities over all original
face-angle sums. Exact coordinate-domain checks illustrate the cap test
and the selected candidates. Neither a successful numerical search nor
an optimizer's infeasibility status is a premise of the cap theorem.
