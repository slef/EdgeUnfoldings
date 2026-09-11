# Case A: use the actual shortfall and overshoot

12 September 2026. Written planar lemma, pending independent review.

The wider angle condition in CASE_A_WIDE_CONES.md is not automatic even
with a low fan and a sharp slit. The exact point in
`results/case-A-low-fan-wide-failure.certificate.json` proves that limit:
its fan curvature is below pi and its slit curvature above pi, but the
short-side angle exceeds (pi+theta)/2. Every face pair in its net is
nevertheless independently certified nonoverlapping.

The missing information is how much one edge falls short compared with
the other edge's overshoot. Keeping that information gives the following
exact separating-line criterion.

## A criterion for the two full apex cones

Use the Case A notation of CASE_A_CONES.md. Define

    A = ell*sin(beta) - s*sin(theta),
    B = s'*sin(theta) - ell*sin(alpha).

Thus A=(L-s)*sin(theta) is the left shortfall and
B=(s'-R)*sin(theta) is the right overshoot, both on a common positive
scale. The strict distance-sum lemma gives **A>B**. Either quantity can
be negative. In the difficult left-short/right-long case both are positive.

The source curvature identity gives lambda+rho<pi+theta, as established
in CASE_A_WIDE_CONES.md. Under that hypothesis, either row below supplies
a separating line and hence proves the two entire convex outer faces safe:

| Candidate boundary direction | Exact sufficient inequality |
| --- | --- |
| Left: if lambda<=theta | A>=0 |
| Left: if lambda>=theta | A*sin(lambda) >= B*sin(lambda-theta) |
| Right: if rho<=theta | B<=0 |
| Right: if rho>=theta | A*sin(rho-theta) >= B*sin(rho) |

The two expressions agree in sign on their common angle boundaries.
All equalities are allowed. These tests concern the full unbounded apex
cones: failing them does not by itself mean the finite faces overlap.

## Proof

Put e at direction pi+alpha, f at direction pi-beta. The known displacement
of the copied apices P,Q is

    sin(theta)*(Q-P) = -A*e+B*f.

The left apex cone and the reversed right apex cone have a convex sum
whose boundary directions are

    lo = min(pi+alpha-lambda, pi-beta),
    hi = max(pi+alpha, pi-beta+rho).

Its width is strictly below pi. If both angles exceed theta this is the
identity lambda+rho-theta<pi; if just one does, the width is that angle;
if neither does, the width is theta. No circular interval is silently
replaced by its complementary sector.

For lambda<=theta, lo=f and the determinant of f with the scaled
displacement is -A*sin(theta). For lambda>=theta, lo=e-lambda and that
determinant is

    -A*sin(lambda)+B*sin(lambda-theta).

If either is nonpositive, Q-P is on or outside the lower boundary of the
cone sum, so the line parallel to that boundary separates the translated
cones. Computing the determinant of the displacement with hi gives
B*sin(theta) when rho<=theta, and
-A*sin(rho-theta)+B*sin(rho) otherwise. This proves the other two rows.

Conversely, the two full apex cones can have intersecting interiors only
if the displacement is strictly inside this cone sum, meaning both
applicable determinant tests have the opposite strict sign. This is the
standard Minkowski-difference condition, proved here by the explicit two
boundary directions. A boundary contact does not allow face-interior
overlap.

## The wider bound and the remaining target

When A>0 and B>0, A/B>1. If lambda<=(pi+theta)/2, then
sin(lambda-theta)<=sin(lambda), recovering the earlier wider theorem.
For a larger lambda, the required ratio can still be only slightly above
one. The exact low-fan example above has enough shortfall to pass this
actual length comparison even though its wider angle bound fails.

For a cofacial original candidate with sharp slit and low fan, apply these
tests to its one remaining quadrilateral/triangle opposite pair. If either
separator holds, the whole original net follows from the already-proved
star comparison and sharp-slit reduction. For a general octahedral
sharp-slit candidate, both opposite-petal triples must be checked.

What remains unproved is that a permitted original choice must always
supply these inequalities, or that the finite faces remain separated when
both cone tests fail. Neither the angle-only condition nor finite random
sampling resolves this issue.
