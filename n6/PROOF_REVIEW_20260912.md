# Review and simplification of the six-vertex proof

12 September 2026. Completed the requested 06:28–09:58 JST review session.
This is a further self-audit. Independent mathematical review and formal
verification remain outstanding. The original research material is retained.

## Completed review

The 3.5-hour session is complete and its heartbeat is paused. The separate
[streamlined manuscript](TIDY_PROOF.md) now uses the
[paired-pole theorem](PAIRED_POLE_RULE.md) for the octahedron and minus-edge
graph, and the five-candidate cap/angle rule for the prism with one diagonal.
The paired-pole identity removes both the comparison of different pole
pairs and the entire minus-edge source-switch exhaustion from this shortest
account. Every earlier argument and successive draft is retained.

No mathematical gap was identified in this self-review. This is not an
independent audit or formal verification. The main independent review
priorities remain the contact-containment and small-fan polygon arguments,
the new positive identity's geometric application, and the original-face
prism separators. The stronger every-slit lemmas and fixed-two-tree
conjecture are optional questions, not premises of the existence proof.

All 300 tests pass; 38 new selected nets have independent exact whole-net
replays. The original 59 research documents, 24 figures and 491 result
artifacts are unchanged. The readable overview, new proofs and preserved
drafts pass packaging and link checks. Work is committed on the separate
local branch codex/proof-review-tidy; no deployment was performed.

The detailed validation and successive checkpoints below are preserved,
including their earlier open questions and intermediate claims.

## Final validation — approximately 09:52 JST

The complete updated suite passed **300 tests in 342.348 seconds**.
The paired-pole report independently verifies all 38 selected nets, with
no unresolved choice in that explicit list. The earlier whole-suite
check passed 296 tests before the four paired-pole tests were added.
These are implementation, algebra and finite-domain checks, not a formal
verification of the universal geometry.

The final manual pass rechecked the wider-cone identity in both directions,
its positive link remainders, the automatic angle-sum premise, the closed
source-order case, and the use of uncut flat diagonals. The paired-pole
proof reuses the local, finite-contact, base-cone, pocket, boundary and
wider-cone lemmas; it does not assume the older source-selection conclusion.
For the minus graph, A/B are opposite degree-four vertices and every one
of their possible star-plus-equator cuts is original. No extra facet or
suppressed triangle is needed when the original quadrilateral is rejoined.

The full scientific suite, navigation and progress checks pass. Final
packaging also checks every overview evidence link and the standalone
reading pages, including the formatted preserved drafts. No full browser
visual inspection was performed after browser access was denied.

## Latest result — approximately 09:48 JST

A final exact positive identity gives a substantially shorter result:
[PAIRED_POLE_RULE.md](PAIRED_POLE_RULE.md). On an octahedron, fix any
opposite pair, choose its sharper endpoint as source, and use an equator
maximum for the fifth cut. The two wider Case A bounds follow from

    2*pi+K-2*lambda-nu=(kappa_v-kappa_w)+S+nu+2*rho,

and its reflection, where S is the sum of the fourth petal's two strict
base-angle link slacks. All terms on the right are nonnegative, and S,
nu and rho are strictly positive. Sixteen cyclic/reflected coefficient
expansions vanish exactly. The optimizer's negative feasibility margin
was only a discovery hint; the displayed identity is the proof.

The local, finite-contact, small-fan and final-boundary arguments then
complete the paired-pole theorem. If the source is below pi, either the
equator maximum is at least pi, or all six curvatures are below pi; both
supply the needed lower face budget. At a high source, E1 and the strict
source-angle bound supply the two contradictions. This includes equalities.

For the minus-edge graph, choose its opposite degree-four corners A,B.
Every resulting star edge and fifth cut is original, and the auxiliary CD
stays uncut. Thus the former source-switch exhaustion is unnecessary in
the shortest main proof. It remains intact in the preceding complete draft
and the original files. The new theorem also closes the unranked octahedron
shortcut investigated immediately beforehand; that investigation and its
then-open status are preserved in full.

The independent examples now replay **38 selected nets**: all three fixed
pairs on ten octahedral points/domains, seven earlier minus-edge examples
(including parameter families and equality), and the former upper-cap
failure. There are no unresolved uniform choices in that saved list.
All four new paired-pole tests pass. The preceding complete suite passed
296 tests; the new complete 300-test run is underway.

Preservation was rechecked against published master 6327f07: all 59 original
research Markdown documents, all 24 original figures and all 491 original
result artifacts are unchanged. The running continuation log is the stated
exception. No mathematical gap has been found in this self-audit, but the
new and old research proofs still need independent mathematical review.
No full browser visual inspection was performed after browser access was
denied. The work is saved locally on the separate review branch.

## Earlier checkpoints, retained in full

The entries below record successive stages and their then-current status.

## Current checkpoint — approximately 08:15 JST

The review remains active until 09:58 JST. The complete shorter account is
in [TIDY_PROOF.md](TIDY_PROOF.md) and [TIDY_CORE.md](TIDY_CORE.md).
The first complete draft is preserved in full as
[TIDY_PROOF_FIRST_REVIEW.md](TIDY_PROOF_FIRST_REVIEW.md); the entries below
record successive stages rather than replacing their earlier conclusions.

The principal additional result is the [prism cap rule](PRISM_CAP_RULE.md).
Let C_A and C_F be the sums of vertex curvature on the two triangular caps.
If both are at least pi, the fixed two-pair tree T works. Otherwise one is
below pi and the other above 3*pi, which forces exactly one of the two
existing switch lemmas. This reduces the fixed family from seven trees to
five, with **at most two candidates for a given shape**. Neither five-tree
minimality nor sufficiency of the four cofacial trees alone has been proved.
The original seven-tree proof and both failures of T are retained.

The identity behind this rule gives a reusable degree-three Case A lemma:
the two wider cone bounds are equivalent to |lambda-rho|<=C. This is an
equivalence of sufficient cone bounds, not an equivalence with nonoverlap.
Its stronger optional prism test is preserved separately in
[CASE_A_CAP_BUDGET.md](CASE_A_CAP_BUDGET.md). The gate switch also admits
two direct implications: a nonobtuse F_3 makes its near-star safe, and a
nonobtuse F_5 makes T safe. At least one is nonobtuse because these are
different angles in the same triangle.

The complete suite passed **284 tests in 295.848 seconds**: the 271 original
tests, seven initial tidy-proof audits, and six cap-rule tests. The cap
tests were rerun successfully after strengthening an exact curvature-band
deduction. Fifteen preserved points or parameter domains independently
certify one of the cap rule's selected original-edge nets, including all
four asymmetric branches and both old failures of T. These checks support
the implementation and stated finite domains; they do not machine-verify
the universal geometric argument. Navigation and progress checks pass.

### Fresh manual checks completed

* Reconstructed the finite-entry barrier, the projection and sine-angle
  inequalities, the strict local slit determinant, and the small-fan
  six-sided region. Checked the boundary contacts, orientation, angle ranges,
  and that none of these steps assumes its downstream conclusion.
* Checked that every cofacial use concerns a whole original quadrilateral.
  Auxiliary diagonals remain uncut and the source-corner cones contain
  the full convex faces. In T's two cap views, the three apex angles exhaust
  the original degree-three vertex; no missing incident face is suppressed.
* Rechecked the prior angular-span, patch-budget, two-pole, three-chain,
  local-gate, low-curvature far-pair, radial-cover, Case A length, support-
  triangle and intrinsic closure arguments. Their weaker hypotheses and
  narrower sufficient conclusions remain useful and are preserved.
* Read the interval, affine, polynomial and whole-face certificate checks.
  Rational bounds round outward; uncertain signs are rejected. Facet
  planarity is checked as an identity on a box, facet supports are strict,
  cut trees and common vertex copies are checked, and every required pair
  needs a witness. A solver's numerical status is not accepted as a proof.
* Rechecked the selected-slit versus arbitrary-slit distinction. The
  optional yellow Lemma F and Triple Lemma are stronger statements under
  H alone; the existence proof uses the proved selected H/R versions.
  The separate fixed two-tree minus-edge conjecture is also unchanged.

The published bounded-sector result is Theorem 9.1 of
[Aronov--O'Rourke](https://link.springer.com/content/pdf/10.1007/BF02293047.pdf),
with the disk sectors defined in Section 8.1. It does not supply an empty
infinite wedge. The original vertex-source star is covered by the cited
Kiazyk--Lubiw result. The dome step is also stated explicitly as Corollary 2
of [Pinciu](https://cccg.ca/proceedings/2007/01a4.pdf). The earlier direct
DiBiase thesis audit was read and its quantifiers rechecked; the thesis PDF
itself has not been rescanned in this session.

No mathematical gap has been identified in this self-audit so far.
Independent mathematical review remains necessary. The remaining time is
for further scrutiny and presentation, not for upgrading that review status.

### Discovery calculations retained, not used as proof premises

Four scratch searches are preserved as text in `archive_notes/proof-review-*`.
Linear optimization suggested shorter identities; their exact coefficient
expansions and written positive remainders are the proof, not optimization.
A later numerical search found no example with a low opposite cap and two
particular obtuse switch angles. Its results are saved in
`results/prism-double-obtuse-discovery-20260912.json`. They neither prove
impossibility nor justify dropping the sharp-switch identities. Sample
counts include parameter proposals, not certified distinct polyhedra.

## Further checkpoint — approximately 08:25 JST

The cap proof now states its deterministic angle rule explicitly. After
reflecting to C_A>3*pi, the low-end branch chooses M if F_3<=pi/2 and T
otherwise. The sharp-end branch chooses N if K>=E_1, E_1<=pi/2, or
2*D_1+E_1<=2*pi+K; otherwise the three identities force T. Thus a shape
needs no trial unfolding to select its tree. `prism_angle_rule.py` implements
these proved tests separately from the independent all-pairs replay; all
15 preserved domains pass the selected net check. The exact interval
implementation may reject an unresolved uniform box. This does not change
the mathematical pointwise rule or assert that every box admits one uniform
choice.

One reporting defect was found in `certify.py`: the arithmetic label was
hardcoded to 80 fractional bits even when a caller had selected a higher
precision. The report now reads the actual setting. This did not affect
any acceptance condition or outward bound; historical saved reports remain
unchanged. A regression check covers both 64- and 240-bit runs.

The dome dependency was additionally cross-checked against O'Rourke's
[2013 face-neighborhood paper](https://cccg.ca/proceedings/2013/papers/paper_22.pdf):
its introduction states the earlier dome theorem and Pinciu's extension
to edge neighborhoods. The counterexamples in that paper concern stronger
band or vertex-neighborhood proposals, not this dome dependency.

## A shortcut ruled out by a new exact example — approximately 08:30 JST

A fresh numerical probe of the four cofacial prism routes found a shape
where both routes at the sharper source failed. The rational simplification
now in `SHARPEST_COFACIAL_FAILURE.md` is checked independently: source 1
is the unique sharpest vertex of all six, but its routes through 2 and 4
overlap A/D and D/E, respectively. Both source-3 routes and T are safe.
These five outcomes and the strict source order also hold throughout a
nine-parameter box of half-width 1/10^10. Thus this is an exact negative
result about the tempting sharpest-source-only shortcut. It is no longer
merely a numerical candidate. It does not refute the four routes together
or show that five candidates are minimal.

The 100,000-shape numerical search found no failure of all four routes;
that absence establishes no universal statement. Its complete report is
retained. The cap rule chooses T on the exact counterexample before any
unfolding, and all 15 original face pairs are independently certified.

## Saved validation checkpoint — approximately 08:37 JST

The fresh full suite passed **290 tests in 330.481 seconds**. The packaged
overview has 241 resolving evidence links; its six standalone reading pages
have 72 resolving local evidence links and heading anchors. Full browser
visual inspection was not performed because browser access was denied;
these are static build and navigation checks. All 59 pre-review research
Markdown documents remain unchanged. The work is being saved on the separate
local review branch, with no push or deployment.

A further possible octahedron simplification is now being investigated:
use the largest-curvature vertex as the fifth cut's endpoint, and select
a low-curvature fan with two adjacent face-curvature sums in [pi,3*pi].
This would allow the existing finite-entry budget and pocket identity to
contradict the lower cap bounds directly, avoiding the projection branch
in a standalone existence proof. This prospective shortening is not yet
a replacement for the checked manuscript.

## Shorter octahedron proof completed — approximately 09:05 JST

`OCTA_FACE_CAP_RULE.md` now gives a complete separate existence argument.
Choose sharpest c, then the more unequal of the other two opposite pairs,
and cut the star at its sharper end plus the edge from its other end to c.
The source need not be the globally sharpest vertex. The two proposed upper
cap sums satisfy U1-U2=(B-b)-(A-a) and U1+U2=4*pi+M-m<6*pi, so the rule
chooses an upper sum below 3*pi. Every triple containing a maximum-curvature
vertex has sum above pi: otherwise that maximum and the remaining three
vertices would all be below pi, contradicting total curvature 4*pi. The
weighted slit test is automatic because the maximum is at least 2*pi/3.

The source is at least as sharp as its fan, which guarantees the half-fan
alternative (source>=pi or fan<=pi). Thus the same criterion also covers a
fan above pi; no extra selection branch is needed. The first low-fan draft,
its code, tests and nine certificate domains are retained in
`archive_notes/octa-face-cap-low-fan/`.

The lower cap bounds contradict the finite-entry budget and small-fan pocket
identity directly. The upper bounds are exactly the complementary source-
face budgets needed by the Case A apex cones. This standalone octahedron
argument therefore omits projection E1 and both source-curvature case splits.
The original stronger selected-source theorem remains unchanged and useful
in the full six-vertex proof. No dependence on the refuted unrestricted
interior-hinge reduction has been introduced.

All five new tests pass. They include every 1/6-grid curvature assignment
with six positive entries below 2 summing to 4 (28,897 assignments), ordered
and tied comparisons, an abstract high-fan branch, and actual metric cases.
The grid is only a finite algebra/selection check, not a realization claim
or the universal proof. All nine saved point/parameter domains pass the
canonical larger-difference choice and independent checks of all 28 face
pairs. The domains include regular ties, an exact pi curvature, an 18-coordinate
box crossing pi, and a new chosen source outside the former high-source-or-
all-low condition. The full suite previously passed 290 tests; these five
additional distinct tests bring the tested total to 295.

An attempted automatic transfer to the minus-edge graph was deliberately
not promoted. A coarse rational grid covered by original cap candidates
and old complementary gates concealed an exact abstract uncovered budget.
`FACE_CAP_ORIGINAL_EDGE_LIMIT.md` records it, with no metric realization
claim. It shows why a finite grid cannot replace the missing argument and
why auxiliary cuts must still be checked. The original whole proof remains
the main reference for those nonsimplicial choices.

## One fewer auxiliary point in the finite-cut argument — approximately 09:15 JST

The core now uses the first contact q itself, instead of moving to an
auxiliary interior point p. W0 and V0 meet closed V1 only at their common
a: the intervening face angles and curvature gap separate their closed
sectors. Thus aq remains a barrier even though it is on V1's boundary,
and M lies in triangle(a,w,q). With q=λP, 0<λ<=1, projection gives
e·q=λs cos(κa)<s, retaining the strict E1 contradiction. The sine argument
gives 2θ+2δ+κa<=π; using the strictly smaller face-angle link bound at c
then gives the same strict E2 budget.

This includes first contact at the apex P or the slit endpoint b, so the
corresponding closed remote petal misses the closed finite cut under each
stated application. No perturbation or interior-point adjustment is needed.
The old complete core draft is preserved as
`archive_notes/TIDY_CORE_before_contact.md`. The original proof files remain
unchanged. This strengthens one boundary conclusion; it does not change
the stated overall scope of disjoint face interiors with boundary contact
allowed, or assert a formal verification.

The fresh manual check examined both positive angular gaps at a, the first
contact on aP, q=b and q=P, the triangle's nondegeneracy, the half-plane
orientation and strictness of the closed link. Both obstruction inequalities
are unchanged, so the existing exact historical-entry check remains relevant.

## Final-pass refinements — approximately 09:30 JST

The through-fan step now stays entirely in the actual opening: the remote
patch contains ray wu_1 at angle omega_0, while the last cut copy has angle
Gamma_w. Reaching it through the fan would require span at least
Gamma_w-omega_0>Gamma_w/2, contrary to the half-fan lemma. Reflection
handles the other remote target. This removes the earlier explanation
through another opening; that paragraph is retained separately.

The canonical octahedron rule now has ten independently replayed point or
parameter domains. The new small-integer high-fan example has both selected
poles above pi, and passes all 28 pairs. All six current face-cap tests pass;
the full suite is to be rerun after these final additions.

A further optional shortcut was examined: omit the difference comparison
and use either remaining pole pair, oriented from sharper source to less
sharp fan. Both choices were numerically separated on 80,000 screened
samples, which proves no universal statement. An exact integer example
shows that the unranked choice can violate the current upper cap premise
while still having a safe whole net. Thus the proof cannot simply drop
that comparison. The unproved shortcut, its exact boundary, and the
numerical probes are kept separately in OCTA_UNRANKED_SHORTCUT.md.

The reading pages now include preserved versions of the low-fan and
interior-point drafts, with their relative links resolved from the original
n6 base. The review log itself also has a readable HTML page. The overview's
new current introduction explains the latest octahedron rule and five-tree
prism proof; its earlier seven-tree introduction is retained in collapsed
history. This is presentation and self-audit, not independent verification.

## Checkpoint: complete shorter draft, review continuing

At approximately 07:15 JST the separate exposition is complete end to end:
[TIDY_PROOF.md](TIDY_PROOF.md) gives the classification and original-edge
choices, and [TIDY_CORE.md](TIDY_CORE.md) supplies the geometric core and
planar separators. Readable HTML versions are linked from the overview.
No actual gap has been identified in this review so far. This is not an
independent review or formal verification of the proof.

The fresh reconstruction checks the following points explicitly:

* The finite-entry containment uses only shared vertices and the actual
  slit's local lemma. It does not assume opposite-petal safety.
* The small-fan overlap is below the middle base by two linear half-plane
  inequalities. The middle blue triangle suffices to exclude the wrong
  interior sector; its attached petal is unnecessary.
* The finite-cut and strict local boundary facts make the auxiliary curve
  and six-sided region simple. The orientation at the last slit copy fixes
  the complementary interior angle used in the angle sum.
* A single source-curvature contradiction now handles the small-fan pocket,
  just as a single obstruction handles finite entry.
* Four explicit target-boundary checks replace the historical interior-hinge
  dependency. The refuted unrestricted reduction is still retained.
* The original-face star comparisons keep exactly the same connected tree
  after removing the appropriate leaf faces. The reference diagonals are
  shortest paths, while every final cut remains an original edge.
* The prism's two cap views have complementary central angle sums. This
  gives one shared observation for both switches and the two-sharp case.
* Every equality threshold routes to a proved closed branch. Flat auxiliary
  hinges are handled directly, using the closed tangent link, not a presumed
  curvature-preserving perturbation.

There are two additional shortenings beyond the first draft:

1. An elementary complement-graph classification replaces a computational
   type enumeration in the main argument. After excluding a vertex joined
   to all others, the complement has only paths and cycles. Its eight
   possible component types reduce to the four remaining polyhedral graphs:
   three exclusions contain K_(3,3), and one has a two-vertex separator.
2. The three prism identities have shorter positive-remainder forms. The
   first two need only positive original angles and angles below pi; the
   last retains three strict link slacks and the obtuse-middle premise.
   Numerical linear optimization suggested the forms; exact coefficient
   expansion, not the optimizer's status, checks the identities.

Seven new tests pass. They check the graph list and its explicit exclusions,
the new minus and prism identities, half-fan spans at five exact points and
an 18-coordinate box crossing the source-curvature threshold, a rejected
reversal of the source condition, and the two necessary inequalities on the
historical actual finite-entry counterexample (whose other 27 pairs are
rechecked). See [the exact report](results/tidy-core-audit.verification.json).
These are algebraic/finite-domain checks, not a machine proof of the geometry.

The external dependencies were checked at their stated scope. Definition 1
and Theorem 4 of [Kiazyk--Lubiw](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SOCG.2015.390)
include the vertex-source star used here; their Section 3.2 also confirms why
an entirely empty infinite exterior wedge must not be assumed. The dome
result and definition are supported by [O'Rourke's treatment](https://www.science.smith.edu/~jorourke/Papers/PolyUnf0.pdf)
and the opening sections of [Demaine--Demaine--Uehara](https://erikdemaine.org/papers/ZipperDomes_CCCG2013/paper.pdf).
The latter's introductory six-vertex attribution to DiBiase is not being used
to validate the new proof or to override the repository's direct thesis audit.

The remaining time is for a second pass against the reconstructed manuscript,
focused on geometric containment, polygonal-face applicability, and exact
boundary assumptions, followed by presentation and packaging checks.

## Initial review notes, retained

The following entries record the first stage, including its then-open tasks.
The checkpoint above gives the current state of those tasks.

## Review objectives

1. Reconstruct the geometric dependencies without assuming that a completed
   status label is evidence of correctness.
2. Check the local separators, finite-cut containment, opposite-petal curve,
   original quadrilateral recovery, source switches, and equality cases.
3. Isolate a concise proof in a separate document and overview section.
4. Record any actual gap before shortening the presentation around it.

## Initial dependency audit

The central chain is: local safety and strict slit separation; finite-cut
exclusion; opposite-petal separation; remaining fan pairs; original-edge
candidate selection. The finite-cut exclusion uses local pairs and shared
uncut vertices, not an opposite-petal conclusion. Thus the claimed dependency
order is not circular. The topological containment steps still need a fresh
line-by-line exposition before this audit is complete.

The Case A cone proof uses positive base curvature gaps, equal copies of the
two cut-edge lengths, and bounds on the full outer apex angles. The one-sided
and wider bounds are separate sufficient criteria; failure is not overlap.
The basic distance-sum contradiction and the local slit determinant have
been rederived directly in this review.

## First shortening found: use the middle fan triangle itself

In the small-fan opposite-petal argument, the closed curve has vertices
a,p,b,w strictly below the middle base line. If its interior at w contained
the fan sector, shared-vertex separation would trap the middle fan triangle
itself. But that triangle has vertices on the middle base line, outside the
closed curve. This is already a contradiction. The extra step that also
traps the middle orange petal is unnecessary.

There is a direct coordinate proof that the overlap region is below the
base. With base endpoints (0,0),(ell,0), and central angles sigma,tau>0
with sigma+tau<pi, the two outer half-plane inequalities imply

    y < -ell*sin(sigma)*sin(tau)/sin(sigma+tau) < 0.

This replaces a picture-dependent location assertion by two linear
inequalities. The original argument is preserved in LEMMA_F_CUT_REDUCTION.md.
The shorter version will retain the actual finite-segment and local premises;
it does not restore the earlier false unrestricted hinge reduction.

## Status labels to clarify

Lemma F and the Triple Lemma have proved versions at the selected slit (H+R).
Their original forms under H alone quantify over arbitrary slits and remain
stronger open questions. The tidy existence proof must state the selected
versions explicitly and must not depend on their yellow universal forms.

## Third shortening: one identity replaces four minus-edge comparisons

In MINUS_COMPLEMENTARY_SOURCES.md, let K=kappa_D+kappa_Q and retain its
notation q_X, mu_X, nu_X, tau and theta_X=pi-nu_X+K. The two existing
angle-sum identities imply the stronger single identity

    theta_A+theta_B
      = (q_A+mu_A)+(q_B+mu_B)+(K+q_C+tau).

The last parenthesis is strictly positive. Therefore at least one source
X has q_X+mu_X<theta_X, which immediately makes both its positive outer
angles smaller than theta_X. This replaces all four pairwise comparisons
in the main exposition. The original comparisons remain correct and are
preserved. The two Case B alternatives and both cofacial gates must still
be checked before using this Case A identity.

## Second shortening: one finite-entry obstruction

TIDY_CORE.md combines the high-source projection proof and the low-curvature
equal-radius proof into one lemma. A hypothetical finite entry forces both
kappa_v<pi and kappa_a+kappa_c+2*kappa_w+2*mu<pi. Under the allowed source
condition (source at least pi, or all vertices at most pi), the first forces
the all-low situation and the second contradicts Gauss--Bonnet. The cofacial
gate instead contradicts the second directly. No original proof is removed.
The derivation has been checked against the flat-hinge and equality premises;
the remaining topology is still being reconstructed explicitly.

## Open items in this review

* Finish the independent reconstruction of the auxiliary polygon and its
  turning-angle identity, including all contacts and flat auxiliary hinges.
* Recheck the three prism switching identities and all branch hypotheses.
* Find which intermediate lemmas can be omitted from the main exposition
  while retaining links to full proofs and all historical alternatives.
* Assemble and validate the separate tidy proof and updated overview section.

## Fourth shortening: one half-fan bound replaces the local case table

Under kappa_v>=pi or kappa_w<=pi, every flattened patch's full angular
span at w is strictly below Gamma_w/2. For a convex patch this is the
face-angle link bound. For a reflex patch, the old cosine-law calculation
gives gamma<=alpha when the original pole angle is nonobtuse; the closed
link gives alpha<Gamma_w/2. If that pole angle is obtuse, gamma<pi/2,
and the source hypothesis forces Gamma_w>=pi. This is written out in
TIDY_CORE.md, with flat hinges and equality in curvature included.

Adding the bounds for the two flank patches excludes the through-fan
route directly. The separate one-sided spherical-link estimate is not
needed in this shorter proof. Its original statement and proof are kept.
