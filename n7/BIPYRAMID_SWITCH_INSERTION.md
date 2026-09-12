# Growing the seventh vertex with finitely many safe slit changes

**13 September 2026 · A proved insertion family.** Start with a pentagonal
pyramid, insert a pole at zero curvature in its base, and move it out to
its final position. Under the supporting-plane condition below, a simple
rule supplies a safe edge unfolding throughout. It can change its one
extra slit; at most **20** parameter values need consideration for a
pentagonal equator.

An exact integer example has three inward patches at the end, keeps the
inserted vertex least curved throughout, and changes its selected slit
**exactly once**, near $t=0.0467332513$.

[Explore the insertion in 3D](bipyramid-switch-demo.html) ·
[Overview](index.html#bipyramid) · [Supporting-plane proof](BIPYRAMID_SOURCE_PLANE.html)

## A version of the curvature-zero idea that can be proved {#family}

Let a convex polygon $U$ lie in a plane, and let a convex bipyramid have
poles $q,p_1$ on opposite sides. Let $c$ be the intersection of the segment
$qp_1$ with the polygon's plane. It is strictly inside $U$: every ring
edge supports both pole fans, so the intersection is on the interior
side of every polygon edge.

Keep $q$ and $U$ fixed, and set

$$p(t)=c+t(p_1-c),\qquad 0\le t\le1.$$

Assume the plane through $q$ perpendicular to $qp_1$ supports the solid
at $q$:

$$(u_i-q)\cdot(p_1-q)\ge0\qquad\text{for every ring vertex}. \qquad(1)$$

**Theorem Finite-Switch Insertion.** For every $t>0$, cut the star at
$q$ and the edge from $p(t)$ to a maximizer of

$$d_i(t)=|qu_i|+|p(t)u_i|.$$

The resulting edge net is safe. The selected slit can be kept constant
between at most $m(m-1)$ parameter values for an $m$-vertex equator.
At a tie, either maximizing slit is safe. Thus an insertion with five
ring vertices needs at most 20 possible change values.

The pole axis may be tilted relative to the base. This extends the earlier
[aligned-pole insertion](BIPYRAMID_ALIGNED.html#morph), which retained
one fixed slit in its entire family.

## Why every intermediate solid and net are valid {#proof}

For $t>0$ the prescribed two pole fans are exactly the faces of a convex
bipyramid. For each moving face, the supporting determinants of the other ring
vertices scale linearly with $t$ from zero, with the strict signs at
$t=1$. Its determinant against the fixed pole $q$ is affine in $t$
and has the same strict sign at both endpoints, including the base
triangle at $t=0$. For each fixed face, the moving pole stays strictly
on its interior side by convexity of that half-space. All triangles are nondegenerate because $c$ lies
strictly inside the polygon.

The vectors $p(t)-q$ are positive multiples of $p_1-q$. Therefore (1)
holds with the moving pole for every $t$, and the
[Source Plane theorem](BIPYRAMID_SOURCE_PLANE.html#rule) proves the
selected net safe pointwise throughout the interval.

At $t=0$ the new marked point $c$ has zero curvature. Its fan triangles
reassemble the original undivided polygonal base, and the two copies of
the formal slit coincide. The net is the ordinary safe edge-star
unfolding of the six-vertex pyramid; no extra cut through its base is
needed in that limiting solid.

The inserted curvature is nondecreasing. Its normal cones are nested as
the point moves away from $c$: if a normal supports the moving point at
time $t_1>0$, its dot product with $p_1-c$ is nonnegative, and it still
supports that point at every later time. Their spherical areas are the
vertex curvatures. Conversely, old normal cones shrink as the hull grows,
so old curvatures do not increase. In particular, if the inserted vertex
is least curved at $t=1$, it is least curved throughout this insertion.

## Why only finitely many slit changes are needed {#switch-bound}

Write $s_i=|qu_i|$ and $A_i(t)=|p(t)u_i|^2$. Every $A_i$ is a
positive quadratic polynomial with the same quadratic coefficient.

A tie between $d_i$ and $d_j$ says

$$\sqrt{A_i(t)}-\sqrt{A_j(t)}=s_j-s_i=\delta.$$

If $\delta=0$, this reduces to the linear equation $A_i-A_j=0$,
unless the two functions are identical. If $\delta\ne0$, every tie
satisfies

$$(A_i-A_j-\delta^2)^2=4\delta^2 A_j.$$

This polynomial has degree at most two because $A_i-A_j$ is affine.
When it is not identically zero, there are at most two candidate values.
Squaring can add candidates but cannot remove a real tie.

If the polynomial is identically zero, the positive square roots are
analytic on the interval. Factoring the squared identity shows that one
of their signed sums or differences is identically $\delta$ or
$-\delta$. Either the desired difference is identically $\delta$, or
it never equals it; positivity excludes isolated intersections with a
wrong sum branch. Identically tied vertices can always use a fixed index.
Thus every nonidentical pair contributes at most two tie values.

There are $\binom m2$ pairs. Between all those candidate values the
maximizing index cannot change, proving the bound $2\binom m2=m(m-1)$.
This bounds the number of possible changes, not the numerical effort
needed to decide exact algebraic comparisons in a particular implementation.

## The exact three-inward example {#example}

The ring and poles are the following integer points:

| Vertex | Coordinates |
| --- | --- |
| $u_0$ | $(300,2,0)$ |
| $u_1$ | $(84,96,0)$ |
| $u_2$ | $(-300,-2,0)$ |
| $u_3$ | $(-297,-17,0)$ |
| $u_4$ | $(-192,-77,0)$ |
| $p_1$ | $(-52,13,-69)$ |
| $q$ | $(32,29,164)$ |

The final patch pattern is FCFFC, canonical BBCBC: three inward patches
in a two-plus-one arrangement. The inserted pole has strictly smaller
curvature than every other vertex at the endpoint, and hence throughout
the full insertion by the preceding monotonicity proof.

The [exact certificate](results/bipyramid-switch-insertion.json) covers
$[0,1]$ with **128 closed intervals**. On each it proves that only
$u_0,u_2$ can maximize $d_i$ and that $d_0-d_2$ is strictly increasing.
Exact opposite signs at the endpoints and at the displayed rational
bracket prove a unique tie:

$$0.04673325129897420<t_*<0.04673325129988371.$$

The decimal endpoints above are outward rounded from the stored rational
bracket. Use slit $u_2$ before this tie, and $u_0$ after it. Both are safe
at the tie itself. Three independent exact whole-net checks cover the
rational points immediately before and after the bracket, and the target.
Safety for **all** parameters comes from the written family theorem and
its exactly verified hypotheses, not from those three checks or from
slider frames.

The change is in the rule's maximizing slit. It does not assert that the
old tree starts overlapping at the tie, nor that switching is necessary
for the existence of an unfolding. The illustration shows two safe nets
on either side of a combinatorial cut change.

## Scope {#scope}

This proves a complete insertion family, including an explicit minimum-
curvature example. It does not yet handle every pentagonal bipyramid or
every minimum-curvature insertion. The old failure examples and earlier
proofs are retained. Whole counts remain 7/15 bipyramid patch classes and
10/34 seven-vertex graph types.
