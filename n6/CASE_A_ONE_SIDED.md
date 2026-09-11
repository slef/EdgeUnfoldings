# A one-sided separator in Case A

12 September 2026. A planar strengthening of CASE_A_CONES.md. This is a
written proof, not a numerical inference. It also applies when either
outer face is a convex polygon, using its full angle at the copied apex.

## Statement

Use the Case A setup: the middle triangle has base u,u', apex M, and base
angles phi,psi. The outer faces have copied apices P,Q with

    |uP|=|uM|=s,       |u'Q|=|u'M|=s'.

Their cut rays make angles alpha=phi+kappa_u and beta=psi+kappa_u' with
the base, where both curvature gaps are strictly positive. Assume

    theta=alpha+beta<pi.

Let p* be the intersection of those two rays, and put

    L=|up*|=ell*sin(beta)/sin(theta),
    R=|u'p*|=ell*sin(alpha)/sin(theta),   ell=|uu'|.

Let lambda and rho be the full apex angles of the left and right outer
faces. Each lies in (0,pi). Then either of the following suffices for
disjoint interiors of the outer faces:

    s <= L and lambda <= theta;                       (left)
    s' <= R and rho <= theta.                         (right)

Equality in either comparison is included. The other apex angle need
not be bounded by theta. A strictly short edge gives strict separation;
at equality a separating line may be shared.

## Proof by a single linear functional

Put u=(0,0), u'=(ell,0). Define the unit vectors

    e=(cos(pi+alpha),sin(pi+alpha)),
    f=(cos(pi-beta),sin(pi-beta)).

Their oriented angular difference is theta in (0,pi), so they form a
basis. The same sine-rule calculation as in CASE_A_CONES.md gives

    Q-P=(s-L)*e+(s'-R)*f.                            (1)

Assume the left condition. Let h be the coefficient of e in this basis.
The left face lies in the apex cone at P with direction interval
[pi+alpha-lambda,pi+alpha]. Because lambda<=theta, that whole interval
lies between the directions f and e; hence h(x-P)>=0 on the left face.

The reversed right apex cone has directions
[pi-beta,pi-beta+rho]. Its width rho is below pi, so every direction there
has nonnegative h, whether or not rho<=theta. Consequently every point y
of the right face satisfies h(y-Q)<=0. Equation (1) now gives

    h(y-P)=h(y-Q)+h(Q-P) <= s-L <= 0.

The faces lie in opposite closed half-planes of the line h(x-P)=0. If
s<L the half-planes are strictly separated. If s=L the possible common
set is a line, which cannot contain an interior point of either
nondegenerate convex face. Thus there is no positive-area overlap.
The right condition is the reflected proof using the coefficient of f.

## Relation to the earlier proof

The equal-cut-length distance-sum lemma proves that s>=L and s'>=R
cannot both hold. At least one edge is strictly short. The older theorem
bounded both apex angles by theta, so it automatically bounded whichever
side was short. The present result only needs the angle bound on a short
side, which can be checked directly from the original edge lengths.

In particular, any remaining Case A overlap must fail both one-sided
conditions. For every side whose cut edge is at or before p*, that
side's apex angle must be strictly greater than theta. This is sharper
than merely knowing that one of the two no-wrap bounds fails.

This is a sufficient separator, not a necessary characterization of
nonoverlap. Its failure alone does not prove overlap. It does not yet
prove that the sharp-slit family always passes one side.
