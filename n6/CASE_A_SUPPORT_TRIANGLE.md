# Case A: the containing triangle gives a stronger angle bound

12 September 2026. Written planar proof, pending independent review.
This is a further sufficient condition; it does not complete either whole type.

Use the Case A geometry from CASE_A_CONES.md and the automatic source
angle identity lambda+rho<pi+theta from CASE_A_WIDE_CONES.md. Recall

    theta=alpha+beta<pi,
    L=ell*sin(beta)/sin(theta), R=ell*sin(alpha)/sin(theta).

The middle apex M is strictly inside triangle uu'p*. Either condition
below suffices to separate the two entire outer apex cones:

    s<=L  and 2*lambda <= pi+theta+alpha;
    s'<=R and 2*rho    <= pi+theta+beta.

Compared with the earlier common bound (pi+theta)/2, the allowed angle
on the left increases by alpha/2, and on the right by beta/2. Equality is
included. A bound at least pi is automatic since a convex face angle is
strictly below pi.

## The extra information in the containing triangle

Consider the difficult left-short/right-long case. Write a=L-s and
b=s'-R>0. Convexity of distance on triangle uu'p* first gives R<ell:
otherwise the distance from u' to every point of this triangle is at
most R, contrary to s'>R. Now consider the convex function

    f(X) = (ell-R)*|uX| + L*|u'X|.

Both coefficients are positive. At u and p* its value is L*ell.
At u' it is ell*(ell-R), strictly less than L*ell because the ray
triangle has L+R>ell. Since M is a strictly positive convex combination
of all three vertices, convexity gives

    (ell-R)*s + L*s' < L*ell.

Rearranging yields the stronger shortfall-to-overshoot comparison

    a/b > L/(ell-R) > 1.                         (1)

This uses only the containing triangle, not the actual location of M.
It strengthens the earlier a>b inequality. Reflection gives the other side.

## Turning (1) into a separating line

If lambda<=theta, the old one-sided separator applies. Otherwise the
actual-length separator in CASE_A_LENGTH_SEPARATORS.md requires

    a*sin(lambda) >= b*sin(lambda-theta).        (2)

Both sines are positive. Since R<ell,

    2*alpha+beta < pi,
    K=L/(ell-R)=sin(beta)/(sin(theta)-sin(alpha)) > 1.

On theta<lambda<pi, the ratio

    sin(lambda-theta)/sin(lambda)=cos(theta)-cot(lambda)*sin(theta)

is strictly increasing. Direct sine-difference identities give its value
K at

    lambda_0 = pi/2 + alpha + beta/2
             = (pi+theta+alpha)/2 < pi.

Therefore lambda<=lambda_0 and (1) imply (2), strictly. If the other side
is not long, then a>=0 and b<=0 already make (2) hold, with strictness
from the distance-sum inequality. The case lambda<=theta was handled
separately, including possible boundary contact. Reflection completes
the theorem.

## Exact illustration and scope

The exact low-fan, sharp-slit octahedron in
`results/case-A-low-fan-wide-failure.certificate.json` has, for illustration,

    theta about 15.240 degrees, alpha about 10.366 degrees,
    lambda about 98.503 degrees.

It fails the former angle bound of about 97.620 degrees but satisfies
the containing-triangle bound of about 102.803 degrees. The exact phase
checker certifies the inequality; these displayed decimals are not proof.
Its actual ratio a/b is about 1.036, while the purely triangular lower
bound L/(ell-R) is about 1.025. The stronger actual-length test remains
available beyond this sufficient angle condition.

For a source with a sharp fifth-cut endpoint and low fan, this can replace
the remaining opposite-petal Case A check. A cofacial original candidate
needs only its one residual opposite pair. No argument yet proves that
one permitted original candidate must satisfy these inequalities.
