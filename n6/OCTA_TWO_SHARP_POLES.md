# A curvature test for an opposite pair

**Theorem.** Let w be the sharper of two opposite vertices v,w of a strictly
convex octahedron. Write K=kappa_w and J=kappa_v. If

    K + 2*J >= 2*pi   (360 degrees),

then the octahedron has a nonoverlapping original-edge unfolding. A shortest
path between the poles determines a successful tree: cut the four edges at v
and a suitable edge from w.

This is a complete geometric proof for the stated family. It does not claim
that every octahedron has an opposite pair satisfying the test.

The slightly more general sufficient hypotheses used by the proof are
K>=2*pi/3 and K+2*J>=2*pi, without requiring K>=J. The sharper-pole formulation
implies K>=2*pi/3 automatically, because K+2*J<=3*K.

## The radial bound is forced by two face-angle bounds

Choose a shortest surface path from v to w. It crosses one equator edge ab
inside the two-face patch Q=w a v b. Denote its length by L. Write omega for
the angle of W at w, and nu for the angle of V at v. The shortest-path finite
reduction, including ties, is proved in [GEODESIC_SECTOR.md](GEODESIC_SECTOR.md).

Each incident face angle is at most half the full face angle at that vertex.
Indeed, on the unit sphere, the direct arc between its edge directions is no
longer than the route through the other incident edge directions. Therefore

    omega <= pi-K/2,    nu <= pi-J/2,
    omega + 2*nu <= 3*pi-K/2-J <= 2*pi.

**At least one of wa,wb has length at most L.** Suppose instead that both
exceed L. In the flattened triangle wva, write x_a for its angle at w and
y_a for its angle at v. The side wa is longer than wv, so its opposite angle
y_a exceeds the angle at a. The triangle-angle sum gives

    x_a + 2*y_a > pi.

The same comparison in triangle wvb gives x_b+2*y_b>pi. The diagonal wv lies
inside the convex patch, so x_a+x_b=omega and y_a+y_b=nu. Adding the strict
inequalities yields omega+2*nu>2*pi, a contradiction.

This argument accepts |wu|=L. It does not infer a length inequality from
numerical tests, and it does not require the original equator to be planar.

## Converting the shortest cut to an original edge

Choose an endpoint u with |wu|<=L. The angle gamma between the shortest path
and wu is inside the face angle omega at w. Since K>=2*pi/3,

    gamma <= omega <= pi-K/2 <= K.

Thus the two exterior-sector replacement conditions hold:

    |wu| <= L,    gamma <= kappa_w.

Start with the star unfolding from v: cut its four shortest edge paths to
neighbors and the chosen shortest path to w. Replacing the latter by the
original edge wu moves a triangle into the empty exterior circular sector
at w. Its two non-w vertices have radii L and |wu|, and its angle at w is
gamma. These radius and angle bounds put the whole moved triangle inside
the sector. The resulting cuts are exactly star(v) together with wu.
The net is nonoverlapping.

The exterior-sector result is Aronov–O'Rourke, Section 8.1 and Theorem 9.1:
[Nonoverlap of the Star Unfolding](https://link.springer.com/content/pdf/10.1007/BF02293047.pdf).
Their theorem treats the star unfolding together with its exterior circular
sectors. The vertex-source and tied-shortest-path limits are detailed in
GEODESIC_SECTOR.md. Boundary contact is allowed throughout.

## Some immediately recognizable covered families

- Both poles have curvature at least 120 degrees. Either orientation works:
  each pole can serve as the sector vertex, and the other as the four-cut source.
- The sharper pole has curvature at least 180 degrees and its opposite at
  least 90 degrees.
- The sharper pole has curvature at least 240 degrees and its opposite at
  least 60 degrees.
- The sharper pole has curvature at least 270 degrees and its opposite at
  least 45 degrees.

These examples lie on the same inequality boundary; they are not separate
proofs or equal portions of the remaining research.

## Consequence: every centrally symmetric octahedron

In a centrally symmetric octahedron, opposite vertices have equal curvature.
Choose a vertex of maximum curvature, at least 120 degrees because the six
curvatures sum to 720 degrees. Its opposite has the same curvature. The
weighted test is satisfied, and the theorem applies.

Thus **every centrally symmetric convex octahedron has an edge unfolding**.
This includes every nonsingular affine image of the regular octahedron,
however stretched or skewed. The four-choice rule at a sharpest source is
also proved for this family, since the two equal-curvature poles may exchange
roles in the argument. This is a written proof, not a conclusion from a sample.
No claim of historical novelty is made for this special family.

## Scope relative to the other proof routes

This settles another explicitly defined geometric family. In the asymmetric
case, its successful source may be the less sharp pole. It is therefore not
an additional whole class excluded from the 49-class analysis that fixes the
sharpest source. That count is now 2 excluded and 47 open after the independent hinge audit.

The all-convex-patch proof remains valid. Subsequent independent
[patch-budget proofs](OCTA_PATCH_BUDGET.md) settle existence under H for
all configurations with at most two bad patches and for three with mixed
directions, allowing the four-cut source to move between poles. Three bad
patches with a common direction remain open in general. The fixed-source
one-patch claim is still unproved after the far-fan audit. The sufficient conditions should
be checked directly, without treating sample frequencies as coverage of the
whole realization space.

## Exact replay

The arithmetic checker certifies K>=120 degrees and K+2J>=360 degrees
without inverse trigonometry, using angle products and rigorous interval
signs. Inconclusive equalities are rejected, never treated as proved. The
written theorem itself includes the equality boundary. Central symmetry is
checked as a polynomial identity, so its proof does not depend on numerically
choosing among tied maximum curvatures.

```sh
python3 -m n6.curvature_pair n6/results/curvature-pair-two-opposite.certificate.json
python3 -m n6.curvature_pair --central n6/results/central-octahedron-family.certificate.json
python3 -m n6.polycert verify n6/results/central-octahedron-family.certificate.json --bits 192
```

The last two commands verify symmetry and a successful fixed net on an
illustrative nine-parameter box. That box is centered on the opposite pairs
±(2,3,20), ±(10,1,2), ±(1,-10,4), with independent coordinate variations
of ±1/10000 in the three positive representatives. The universal theorem
is not restricted to that box.
