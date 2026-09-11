# Case A: a wider angle bound from the strict distance-sum inequality

12 September 2026. Written geometric proof, pending independent review.
This strengthens CASE_A_ONE_SIDED.md; it is not a numerical inference.

## Statement

Use the notation of CASE_A_CONES.md: theta=alpha+beta<pi; s,s' are
the two copied cut-edge lengths; L,R are their distances to the cut-ray
intersection. The equal-length middle triangle proves

    s+s' < L+R.                                      (1)

Let lambda,rho be the full angles of the two convex outer faces at their
copied source apices. Assume, in addition to the Case A setup,

    lambda+rho < pi+theta.                           (2)

Either of the following now suffices for disjoint face interiors:

    s <= L  and lambda <= (pi+theta)/2;
    s' <= R and rho    <= (pi+theta)/2.               (3)

Equality in the two comparisons in (3) is included. Unlike the previous
bound theta, the new angle bound is always greater than pi/2. Therefore
**two nonobtuse outer apex angles suffice in every Case A instance**
satisfying (2), without any source or fan curvature bound.

## Proof

The case lambda<=theta is already proved by CASE_A_ONE_SIDED.md. Suppose
theta<lambda<pi, and s<=L. Write

    e = unit vector at angle pi+alpha,
    f = unit vector at angle pi-beta,
    g = unit vector at angle pi+alpha-lambda.

The left apex cone starts along g and ends along e. The reversed right
apex cone starts along f and ends along the direction pi-beta+rho.
Since lambda>theta, g precedes f. Both cones lie counterclockwise from g
in a sector of width

    lambda + max(rho-theta,0) < pi,                 (4)

where (2) supplies strictness when rho>theta. Thus det(g,z)>=0 on both
the left cone and the reversed right cone. All points of the left face
are in the nonnegative half-plane based at its apex P; all points of the
right face are in the nonpositive half-plane based at its apex Q.

The same sine-rule decomposition gives

    Q-P = (s-L)e + (s'-R)f.

Put a=L-s>=0 and b=s'-R. Equation (1) gives b<a. Hence

    det(g,Q-P) = -a*sin(lambda)+b*sin(lambda-theta). (5)

If b<=0, this is strictly negative: a and -b cannot both be zero,
and both sines are strictly positive. If b>0, use

    sin(lambda)-sin(lambda-theta)
      = 2*cos(lambda-theta/2)*sin(theta/2) >= 0,

which follows exactly from lambda<=(pi+theta)/2. Since b<a, (5) is
strictly negative again. The line through P parallel to g therefore
strictly separates the two faces. Reflection proves the other condition.
The already-proved lambda<=theta case handles its possible line contact.

At least one of s<L or s'<R holds by (1). If both outer angles obey
the larger bound, choose a short side. In particular, two angles <=pi/2
obey it strictly. No assumption about the other edge being long is needed.

## Why the angle-sum condition is automatic in the octahedron reduction

For three consecutive petals, let nu be the middle apex angle and tau
the fourth apex angle at the same original source v. Put
kappa=kappa_u+kappa_u'>0. Then

    lambda+rho = 2*pi-kappa_v-nu-tau,
    pi+theta   = 2*pi-nu+kappa.

Their difference is kappa_v+tau+kappa>0. Thus (2) always holds, even
without a sharp source or a low fan. Flat, uncut auxiliary diagonals are
allowed. In the cofacial original-face reduction, the quadrilateral's
angle at v equals its triangular petal's angle at v, and the entire
convex quadrilateral lies in that same apex cone. The proof applies to
the original quadrilateral itself.

The spherical-link bound 2*lambda<Gamma_v and 2*rho<Gamma_v gives a
convenient further sufficient condition:

    kappa_v+kappa_u+kappa_u' >= nu.                 (6)

Indeed Gamma_v=2*pi-kappa_v <= 2*pi-nu+kappa=pi+theta.
This replaces the earlier sufficient bound with right-hand side pi by
the actual middle face angle nu, which is strictly smaller. A condition
using only curvatures is

    3*kappa_v + 2*kappa_u + 2*kappa_u' >= 2*pi,

because nu<pi-kappa_v/2. These are sufficient conditions, not converses.

## What this leaves open

There is another immediate complete branch: **a nonobtuse middle apex**.
Write the strict containment as M=a*u+b*u'+t*p*, where a,b,t>0 and
a+b+t=1. Then

    p*-M = (a/t)(M-u)+(b/t)(M-u').

If the middle apex angle nu<=pi/2, the dot product
(M-u).(M-u')=s*s'*cos(nu) is nonnegative. Consequently both
(M-u).(p*-M)>0 and (M-u').(p*-M)>0. Expanding the two squared
distances gives L>s and R>s'. Both sides are short, so the preceding
theorem applies. Equality nu=pi/2 is included and the length inequalities
remain strict.

A remaining Case A overlap must have exactly one long cut edge. On the
other, short side, the outer apex angle must be strictly greater than
(pi+theta)/2, hence strictly obtuse. If both edges are short, (2) ensures
at least one of the two apex angles is below the larger bound and (3)
applies. Thus **both-short Case A is universally safe**.

Moreover, the middle apex must be obtuse as well. A possible failure
therefore requires **two adjacent obtuse face angles at the same source**:
the middle angle and the outer angle on the short side. In particular,
if the source has at most one obtuse incident face angle, both Case A
triples in every one of its four opened orders are safe. This statement
only settles the opposite-petal Case A branches; local and Case B premises
still have to be supplied for a whole net.

This is a sharper necessary pattern for failure. It can actually occur
with a low fan: `results/case-A-low-fan-wide-failure.certificate.json`
certifies every rejected wider-test inequality on one exact sharp-slit
octahedron. Its whole net remains nonoverlapping. The stronger actual
length comparison in CASE_A_LENGTH_SEPARATORS.md proves the relevant
pair safe. The high-fan Case A overlap example is separately certified in
`results/case-A-high-fan-failure.certificate.json`; it has the same
obtuse-short-side pattern but a real overlap. Thus the pattern alone
decides neither overlap nor nonoverlap.
