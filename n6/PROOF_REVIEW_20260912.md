# Review and simplification of the six-vertex proof

12 September 2026. In progress during the requested 06:28–09:58 JST session.
This is a further self-audit. Independent mathematical review and formal
verification remain outstanding. The original research material is retained.

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
