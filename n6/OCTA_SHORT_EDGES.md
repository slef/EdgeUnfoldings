# A short-edge test that guarantees an octahedron unfolding

This sufficient theorem gives further **whole geometric families**, including
parts of the two- and three-nonconvex-patch regimes. It does not close any of
those regimes in full, nor any additional whole simultaneous-failure class.

## The test uses original lengths and flattened patch corners

Choose a vertex w of curvature at least 2*pi/3 (120 degrees), and let v be its
nonneighbor. Such a w always exists among six vertices, since total curvature
is 4*pi. Write D=|wv| for the Euclidean distance between these two original
vertices. The segment wv is used only for a length comparison; it is not a cut.

Call a neighbor u **short** when |wu|<=D. Flatten the four pairs of faces
beside the equator edges, as in OCTA_CONVEX_PATCHES.md.

**Sufficient hypothesis:** every strictly convex patch has at least one short
equator endpoint. Patches with an inward or straight corner can be ignored
in this test: their pole-to-pole diagonal is not an interior two-face path.

**Conclusion:** the octahedron has a nonoverlapping original-edge unfolding.
A specific algorithm is:

1. Among the four flattened patches, find a shortest valid straight path
   from v to w. Its crossed equator edge is ab.
2. Choose a short endpoint u of ab.
3. Cut the four original edges at v and the original edge wu.

The sector vertex w is the sharp vertex here. The four-cut vertex v is its
opposite. This is a different sufficient rule from the proposal that insists
on making the four cuts at the sharpest vertex.

## Proof

The shortest-path argument in [GEODESIC_SECTOR.md](GEODESIC_SECTOR.md) shows
that every shortest surface path between v and w lies in one of the four
two-face patches and crosses its equator edge in the relative interior. Its
length L is at least the Euclidean chord length D. Its patch is strictly
convex: an inward corner makes the pole diagonal miss the edge, while a
straight corner makes it pass through an intermediate vertex. A shortest
surface path cannot pass through a vertex of positive curvature.

By the hypothesis, choose u on this patch with |wu|<=D<=L. This supplies the
radial inequality needed for the exterior-sector replacement.

Let Omega=2*pi-kappa_w be the full face angle at w. Each face angle omega_i
is at most the sum of the other three: on the unit sphere, the direct arc
between its edge directions is no longer than the route through the other
directions. Hence omega_i<=Omega/2=pi-kappa_w/2. Since kappa_w>=2*pi/3,

    omega_i <= pi-kappa_w/2 <= kappa_w.

The shortest path lies within W_i, so the angle gamma between it and wu is
at most omega_i. Thus gamma<=kappa_w as well.

Both required inequalities now hold: |wu|<=L and gamma<=kappa_w. Start with
the star unfolding from v, using its four shortest edge paths to neighbors
and the chosen shortest path to w. Replace the latter cut by wu: the freed
triangle, with radii L and |wu| at w and angular extent gamma, rotates into
the empty exterior sector at w. Its disk and angular bounds keep it inside
that sector. The resulting cuts are precisely those in step 3.

The exterior-sector assertion is Aronov–O'Rourke, *Nonoverlap of the Star
Unfolding*, Section 8.1 and Theorem 9.1 (journal pp. 237–240, PDF pp. 19–22).
Their theorem proves nonoverlap of the star unfolding together with its
exterior circular sectors. The vertex-source and shortest-path tie limits
are detailed in GEODESIC_SECTOR.md. Boundary contact is allowed throughout.
[Primary paper](https://link.springer.com/content/pdf/10.1007/BF02293047.pdf).

This is a corollary of that theorem plus the stated original-length test,
not a new proof of the general star-unfolding theorem.

## A simpler sufficient version

It is enough that every equator edge has a short endpoint, without inspecting
patch corners. Equivalently, any long edges from w have nonadjacent endpoints
on the four-cycle. In particular, three short neighbors suffice.

Another immediate case: w and its opposite v realize the Euclidean diameter
of the six vertices, and kappa_w>=2*pi/3. Then every incident edge at w is
short. Neither the required curvature at a diameter endpoint nor the general
short-edge-cover condition has been proved automatic.

## Scope and exact checks

`n6.sector_cover` checks the original strictly convex octahedral facets, the
curvature threshold, every relevant flattened corner, and squared original
length inequalities using rational outward intervals. It then invokes this
written sufficient theorem. It is not formal verification of the theorem.
An independent all-pairs certificate checks any displayed individual net.

The five saved examples below pass the sufficient test, including examples
with two adjacent, two opposite, and three nonconvex patches. They do not
establish that every shape in those regimes passes it.

```sh
python3 -m n6.sector_cover n6/results/short-edge-three.certificate.json
python3 -m n6.polycert verify n6/results/short-edge-three.certificate.json --bits 192
```

The condition is not universal. In particular, the exactly checked
`sector-three-patch-radial-failure` example has four edges from its sharpest
vertex longer even than its two-face surface path, so none is short. The
original four-choice rule still succeeds on that example.
