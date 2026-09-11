# Review and simplification of the six-vertex proof

12 September 2026. In progress during the requested 06:28–09:58 JST session.
This is a further self-audit. Independent mathematical review and formal
verification remain outstanding. The original research material is retained.

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
