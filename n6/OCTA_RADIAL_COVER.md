# Two elementary ways to certify each shortest-path patch

**Theorem.** Choose opposite vertices v,w of a strictly convex octahedron,
with curvature at w at least 120 degrees. For each strictly convex two-face
patch Q=w a v b, suppose at least one of the following holds:

1. One of |wa|,|wb| is at most the straight 3D distance |wv|.
2. Its face angles omega at w and nu at v satisfy omega+2*nu<=360 degrees.

The octahedron has a nonoverlapping edge unfolding with cuts consisting of
the four edges at v and one edge at w. Different patches may use different
conditions. Nonconvex patches, and patches with a straight corner, need no
test: they cannot carry a shortest path between v and w.

This proves a sufficient geometric family, not that every octahedron meets
the conditions. The sharper vertex w is the **sector vertex**; the four-cut
source is its opposite v. This distinction matters when comparing the result
with the proposed rule that makes four cuts at a sharpest source.

## Why these two tests have the same consequence

Choose a shortest surface path from v to w. The finite reduction in
[GEODESIC_SECTOR.md](GEODESIC_SECTOR.md) puts it inside a strictly convex
patch w a v b. Flatten that patch, and call the path length L.

The first test is immediate: the straight 3D chord is no longer than any
surface path, so |wu|<=|wv| in 3D implies |wu|<=L.

For the second test, suppose both |wa| and |wb| exceed L. In triangle wva,
let x_a and y_a be its angles at w and v. The longer side wa has the larger
opposite angle, giving y_a>pi-x_a-y_a, or x_a+2*y_a>pi. The same argument
at b gives x_b+2*y_b>pi. Adding gives omega+2*nu>2*pi, contradicting the
second test. Thus at least one of wa,wb is no longer than L. Equality is
allowed in either test.

Choose such an endpoint u. The direction of wu differs from the shortest
path direction by an angle gamma inside the face angle omega. The convex
vertex cone inequality, together with kappa_w>=120 degrees, gives

    gamma <= omega <= pi-kappa_w/2 <= kappa_w.

We have both sector conditions: |wu|<=L and gamma<=kappa_w. Start with the
star unfolding from v and move the cut from the shortest path to wu. The
moved triangle fits in the empty exterior circular sector at w, proving
nonoverlap. The external sector theorem, the vertex-source limit, and tied
shortest paths are detailed in GEODESIC_SECTOR.md.

## The earlier curvature and length theorems fit inside this one

The short-edge-cover theorem uses the first test at every possible patch.
The weighted curvature theorem uses the second test: if K=kappa_w,
J=kappa_v, and K+2J>=360 degrees, then

    omega+2*nu <= 3*pi-K/2-J <= 2*pi.

The local test is more flexible because it uses the actual face angles.
It can hold even when the two pole curvatures do not satisfy that global
bound. It can also replace a chord comparison that is too conservative.

## A previously uncovered asymmetric family is now covered

The small integer example in [OCTA_REMAINING_FAMILIES.md](OCTA_REMAINING_FAMILIES.md)
was certified outside the earlier zero/one-patch, weighted-curvature, and
short-edge-cover criteria. It has two nonconvex patches at its sharpest
vertex, so that complete patch regime remains open.

Taking w=0 and v=1 in that example, all four inequalities omega+2*nu<=360
degrees hold. The largest left side is about 357.22 degrees; this decimal
only explains the clearance. Rational interval signs establish the result.
The stronger local theorem therefore covers this example.

The saved certificate goes further: all 15 coordinates of vertices 1 through
5 may vary independently by 1/10000, while
vertex 0 stays fixed. Exact interval checks certify the radial-cover
hypotheses and, independently, one fixed successful cut tree throughout
that continuous family. This is a local family in the asymmetric case,
not a proof for all asymmetric octahedra.

```sh
python3 -m n6.radial_cover n6/results/radial-cover-asymmetric-family.certificate.json
python3 -m n6.polycert verify n6/results/radial-cover-asymmetric-family.certificate.json --bits 240
```

The checker compares 2*nu with 2*pi-omega using exact angle products; both
angles lie strictly between zero and a full turn. An unresolved interval
comparison is never accepted as a proof. The written theorem includes exact
equalities even when a particular interval representation cannot decide one.

The full octahedron theorem and the general fixed-sharpest-source rule remain
open. This result excludes no additional whole switching class; the current
count is now 2 excluded and 47 open out of the original 49 classes. The
smaller historical target used the false far-fan reduction; this theorem
does not use it.


## An exact limit to this stronger criterion

The integer example in `results/radial-cover-insufficient.certificate.json`
fails this mixed test at every vertex of curvature at least 120 degrees.
At each such vertex, the exact checker finds a strictly convex patch whose
spokes both exceed the 3D chord and whose weighted face-angle sum exceeds
360 degrees. It has two opposite nonconvex patches at its sharpest source.
An independent successful-net certificate still verifies all 28 pairs.

```sh
python3 -m n6.radial_cover --audit-failure n6/results/radial-cover-insufficient.certificate.json
python3 -m n6.polycert verify n6/results/radial-cover-insufficient.certificate.json --bits 240
```

This does not refute the full surface-path sector condition. The two local
bounds can both be too conservative. A separate numerical pilot found two
such candidates among 30,000 shapes; neither a sample count nor failure of
a sufficient test is evidence against edge unfoldability.
