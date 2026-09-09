# Convex patches: a complete case and a class exclusion

Timed session, 9 September 2026. **The whole octahedron case remains open.**
The convex-patch existence and all-convex-case results below are geometric proofs.
**Audit correction:** the proposed one-nonconvex-patch whole-net proof is
withdrawn pending a replacement for the false far-fan reduction; see
[HINGE_AUDIT.md](HINGE_AUDIT.md).
They use the same four cuts at v and one cut at its opposite vertex w.

## What a convex patch means

Flatten the adjacent faces W_i=w u_i u_{i+1} and V_i=v u_i u_{i+1} along
their common equator edge. Their union Q_i is a simple planar quadrilateral,
in the order w, u_i, v_i, u_{i+1}. The two triangles lie on opposite sides
of their shared edge. This does not require four coplanar vertices on the
original polyhedron.

The corners at w and v_i are triangle angles, strictly below pi. Thus a
nonconvex patch has its reflex corner at exactly one equator endpoint.
Write

    e_i = angle at u_i in W_i + angle at u_i in V_i,
    f_i = angle at u_{i+1} in W_i + angle at u_{i+1} in V_i.

The patch is convex precisely when e_i<=pi and f_i<=pi. A straight corner
is included as convex. A convex patch lies entirely within the angular wedge
of W_i viewed from w. Consequently its petal V_i cannot overlap any other
fan triangle, in any opening Z_k. Two petals whose patches are both convex
also cannot overlap: their fan wedges have disjoint interiors.

## A nonconvex corner forces an increase of a common metric quantity

Define the broken boundary length

    d_i = |wu_i| + |vu_i|.

**If Q_i is reflex at u_i, then d_i<d_{i+1}. If it is reflex at u_{i+1},
then d_{i+1}<d_i.** These inequalities compare original edge lengths; the
positions of the developed copies of v do not affect them.

Proof. In the first case, the reflex vertex u_i lies strictly inside the
triangle with vertices w, v_i, u_{i+1}. The function

    g(x)=|x-w|+|x-v_i|

is convex. At w and v_i it equals L=|w-v_i|, and at u_{i+1} it equals
d_{i+1}>L, by the strict triangle inequality. Writing the interior point u_i
as a convex combination gives g(u_i)<d_{i+1}. But g(u_i)=d_i. The other
case is the same argument with the equator endpoints exchanged.

This also proves a limited fact about the maximum-d opening: neither flank
can lean into its angular gap. It does not exclude meeting around the other
side of the fan, and must not be promoted to a complete proof of that rule.

## At least one of the four patches is convex

**Every strictly convex octahedron has at least one convex Q_i for each
choice of opposite vertices v,w. No sharpest-vertex hypothesis is needed.**

At a shared equator vertex u_i, the corner angles of Q_{i-1} and Q_i sum to
the full face angle there:

    f_{i-1}+e_i = 2*pi-curvature(u_i) < 2*pi.

They therefore cannot both be reflex at u_i. If every patch were nonconvex,
their four reflex corners would have to occupy four different equator
vertices. But a vertex maximizing d_i cannot be reflex in either adjacent
patch: the preceding lemma would require a larger neighboring d. There are
only three other vertices available, a contradiction.

Equivalently, the only two assignments of four distinct reflex corners are
the two cyclic orientations. The associated strict inequalities would be
d_0<d_1<d_2<d_3<d_0, or the reverse. The checked case report enumerates these
assignments; the distance lemma explains why neither is geometrically possible.

The conclusion can be strengthened to at least one **strictly convex** patch.
If a corner is exactly pi, its vertex lies on the segment from w to v_i,
so d_i=|wv_i|<d_{i+1} still holds. Two corners at least pi at the same
equator vertex are still forbidden by positive curvature. The same argument
therefore rules out four patches each having a corner at least pi.

A constructive refinement: at least one of the two patches next to a vertex
minimizing d_i is strictly convex. Otherwise both would have to be reflex at that same
minimum vertex, contradicting its positive curvature.

### Original failure class 20 is impossible

This class requires the following four local mixed overlaps:

| Opening | Required overlap |
| --- | --- |
| Z_0 | V_3 with W_0 |
| Z_1 | V_0 with W_1 |
| Z_2 | V_1 with W_2 |
| Z_3 | V_2 with W_3 |

Each petal would overlap a fan triangle other than its own, so each of the
four patches would have to be nonconvex. The preceding theorem excludes
this. The reflected pattern is the other labeled member of the same class.
This exclusion is valid even without H.

Together with the earlier opposite-route exclusion of class 49, this leaves
**47 open classes out of the original 49 sufficient classes**. The earlier
49-to-24 reduction depended on the now-refuted far-fan lemma and is withdrawn.

## A complete proof when all four patches are convex

**If all Q_i are convex, every one of the four Z_k is nonoverlapping.**
Each patch lies inside its own fan wedge. The four wedges have disjoint
interiors because their total angle at w is below 2*pi. Within each patch,
the two triangles lie on opposite sides of their shared edge. All face pairs
are therefore safe. This conclusion does not need H.

**Recognizable corollary.** Every convex octahedron whose eight triangular
faces are nonobtuse has such an unfolding at every source and every opening.
Each equator corner of a two-face patch is then a sum of two angles at most
90 degrees, hence is at most 180 degrees. All four patches are convex and
the theorem applies. Right angles are included. This gives a simple rule
for that complete family: choose any vertex, cut its four edges, and cut
any edge from its opposite vertex. It is not restricted to regular or
centrally symmetric shapes.

## The one-nonconvex-patch argument has a remaining step

Assume H and let Q_i be the only nonconvex patch. The proposed choices are
Z_(i+2) and Z_(i+3). Both have convex flanks, so all three local pairs are safe.
One opposite-petal pair consists of convex patches and is safe. The other
pair uses the two different routes; the opposite-route switching proof makes
it safe in at least one of the two choices.

This establishes **local and opposite-petal safety in one common net**.
The last step previously invoked the conditional far-fan reduction. That
lemma is now exactly refuted without H; its H-specific replacement remains
unproved. Therefore whole-net safety in this regime is **open**, rather than
a complete theorem. The displayed one-patch example retains its independent
all-28-pairs certificate. Its success is not a proof of the entire regime.

## A five-part geometric division

Since four nonconvex patches are impossible, the remaining possibilities,
up to cyclic symmetry, are:

| Nonconvex patches | Status for a sharpest apex |
| --- | --- |
| None | Proved: every opening works |
| One | Partial: local and opposite-petal pairs can be made safe; far-fan step open |
| Two, adjacent | Open |
| Two, opposite | Open |
| Three | Open |

These are five geometric regimes, not five equal amounts of effort or five
equal fractions of shape space. They are a different view of the problem
from the 49 original simultaneous-failure classes. The two denominators must not be
combined into a completion percentage.

## Exact examples and the numerical survey

The checker in `n6.convex_patches` uses outward rational bounds to establish
the convex original facets, maximum apex curvature when required, and the two corner sums
of every patch. Five saved integer-coordinate examples establish that all
five listed regimes are nonempty; their displayed successful nets also have
independent all-pairs certificates. The examples in the four open regimes
do not establish their universal unfoldability.

The separate seed-6090942 survey classified 5,000 numerical shapes: 676 had
zero nonconvex patches, 1,906 one, 1,348 two adjacent, 976 two opposite, and
94 three. The all-convex theorem is a proof for all shapes satisfying
its hypotheses. The one-patch whole-net claim is no longer counted as proved. These sample frequencies are not global coverage estimates.

```sh
durer_small_n/.venv/bin/python -m n6.convex_patches --samples 5000 --examples
python3 -m n6.convex_patches --verify n6/results/octa-patches-one.certificate.json
python3 -m n6.polycert verify n6/results/octa-patches-one.certificate.json --bits 192
```

The two exact replay commands need only the standard library. Their reports
check the explicit examples' hypotheses and nets; the universal lemmas above
are written mathematical proofs with the stated dependencies.

## A three-patch sector shortcut is exactly false

The shortest-path theorem in GEODESIC_SECTOR.md implies that with three
nonconvex patches, the remaining patch carries the unique two-face route
between the poles. This does not make the sector radial inequality automatic,
even when its sector vertex is globally sharpest. The exact integer example
in `results/sector-three-patch-radial-failure.certificate.json` has three
nonconvex patches, but all four edges from its sharpest vertex are longer
than the valid two-face path through the remaining patch. The sector test
fails. A separate all-pairs certificate proves its original four-choice net
successful. This rules out the proposed sufficient-condition shortcut, not
edge unfoldability or the three-patch geometric regime.

```sh
python3 -m n6.convex_patches --verify n6/results/sector-three-patch-radial-failure.certificate.json
python3 -m n6.sector_audit n6/results/sector-three-patch-radial-failure.certificate.json
python3 -m n6.polycert verify n6/results/sector-three-patch-radial-failure.certificate.json --bits 240
```

A separate sufficient result in [OCTA_SHORT_EDGES.md](OCTA_SHORT_EDGES.md)
covers further families in the open regimes, by checking short original
edges against the pole-to-pole chord length. It does not settle an entire
remaining regime or exclude another whole failure class.
