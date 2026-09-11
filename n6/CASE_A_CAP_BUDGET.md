# A three-face source turns the wider cone bounds into an angle difference

12 September 2026. A reusable consequence retained from the simplification
review. This is a written planar argument, pending independent review.
It is not a theorem that arbitrary larger polyhedra unfold.

Use the Case A setup of [TIDY_CORE.md](TIDY_CORE.md): a middle triangle
has source angle nu, its two base vertices have total curvature K, and
theta=pi-nu+K lies in (0,pi). The two outer convex faces have full
source-corner angles lambda,rho. Suppose these three angles exhaust the
incident face angles of the original source p, as happens when p has
degree three. Then

    lambda+rho+nu=2*pi-kappa_p.

Set C=kappa_p+K, the curvature sum of the middle triangle's three vertices.
The two wider-cone inequalities are exactly

    2*lambda <= pi+theta  <=>  lambda-rho <= C,
    2*rho    <= pi+theta  <=>  rho-lambda <= C.

Consequently **|lambda-rho|<=C is sufficient** for the two outer faces
to be disjoint in this Case A configuration. The angle-sum premise of the
wider-cone lemma is automatic, because
lambda+rho=2*pi-kappa_p-nu<2*pi-nu+K=pi+theta.
The strict distance-sum argument supplies a short side, so both wider
angle bounds suffice without a separate length test. Equality is allowed.

The equivalence concerns these two sufficient cone inequalities, not
nonoverlap itself. If the angle-difference test fails, the finite faces
may still be disjoint and other separators may apply.

Since the original convex-face angles satisfy 0<lambda,rho<pi, the
simpler curvature-only condition **C>=pi** implies the angle-difference
test strictly. This is the short cap argument used in the prism proof.

## A stronger optional prism test

For T in [PRISM_CAP_RULE.md](PRISM_CAP_RULE.md), the two views have
outer angles B_2,D_2 and B_5,D_5, respectively. Therefore the sufficient
condition can be sharpened to

    C_A >= |B_2-D_2|,   C_F >= |B_5-D_5|.

If both hold, both views' Case A branches are safe. Their complementary
central angle sums then supply a safe Case B view if necessary, proving
the same whole tree T nonoverlapping. The shorter main proof keeps the
more easily stated C_A,C_F>=pi condition; this stronger version is
preserved for future work.

At most one of the two optional inequalities can fail: failure requires
that cap's sum to be below pi, while the complementary cap sums above
3*pi and automatically passes. This gives a precise necessary pattern
for an actual failure of T, rather than a count inferred from samples.

Outside the prism, the argument remains a conditional Case A separator
whenever the equal edge copies, actual curvature gaps and three-face
source hypothesis hold. It supplies no general method for arranging
those premises in a larger polyhedron.
