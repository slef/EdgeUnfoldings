# Lemma F reduces to the two slit-side fan pairs

11 September 2026. This is a geometric reduction, **not a proof of Lemma F**.
It uses the now-proved [Lemma L](LEMMA_L_PROOF.md). The two remaining tests
are different from the opposite-petal tests in the old, refuted reduction.

## Statement

Let `v` have maximum curvature among all six vertices (H), and open the fan
at a maximum-curvature equator vertex `u_k` (R). In this selected net, it
suffices to prove

```
V_(k+2) does not overlap W_k,
V_(k+1) does not overlap W_(k-1).
```

These are the two distant orange petals against the blue triangles on the
two sides of the slit. If both pairs are safe, **all 28 face pairs are safe**.
Conversely a nonoverlapping net clearly passes these two tests.

Thus the selected-net unfolding claim is equivalent to these two tests.
The original, stronger Lemma F concerns every slit under H; this reduction
uses R and does not settle that stronger statement.

Of the six far pairs, four are now conditionally eliminated: two opposite
petal pairs by the new argument below, then two interior-fan pairs by the
surviving [interior-hinge reduction](HINGE_AUDIT.md). None of these four has
become an unconditional universal pair theorem. The unconditional count
remains **22/28**, with **two direct tests sufficient for the other six**.

## The new direction of implication

Consider the last three fan triangles, and use indices

```
k=i-1, j=i+1, h=i+2, m=i-1  (modulo 4).
```

The entire fan order is `W_m,W_i,W_j,W_h`. The opposite petals are `V_i,V_h`;
the relevant slit-side pair is `V_i,W_h`. Write

```
a=u_i, u=u_j, u'=u_h, b=u_k (last slit copy),
b'=u_k (first slit copy),
kappa_back = kappa_a+kappa_b+kappa_w.
```

The claim to prove is

> If `V_i` and `V_h` overlap, then `V_i` and `W_h` overlap.

Reflection of the whole developed net gives the other pair. It preserves
the selected physical slit and the curvature hypotheses; it does not move
the slit to another vertex.

The [complete angle partition](CASE_PARTITION.md) already excludes the
opposite-petal pair in Case A and in the base-cone regime. It remains to
consider `Sigma=sigma+tau<pi`. Here sigma and tau are the two sums of blue
face angles at the endpoints of the middle base `uu'`.

Put `u=(0,0)`, `u'=(ell,0)`, the middle orange petal above the base and its
blue triangle below. Let A be the line `ua`, and C the line `u'b`. Their
outward half-planes, away from w, intersect in the wedge Omega beyond
`X=A intersect C`. Every potential opposite-petal overlap lies in Omega.
Both rays `u -> a` and `u' -> b` point strictly below the base. This remains
true when either far vertex is beyond X.

## A closed curve forces the fourth patch inside

Suppose, for contradiction, that the two orange petals have positive-area
overlap but the slit-side pair `V_i,W_h` is safe. Choose a point p strictly
inside both petals, avoiding the finitely many lines through the other
vertices. Form the four-segment curve

```
Gamma: a -> p -> b -> w -> a.
```

This curve is simple:

* The open segment `ap` is inside `V_i`. It cannot meet the open radial
  segment `bw`, since any such point is inside `V_i` and on the boundary of
  `W_h`, forcing positive-area overlap with `W_h`.
* The open segment `bp` is inside `V_h`. It cannot meet the open radial
  segment `wa`: that radial segment is an edge of `W_m`, and Lemma L
  excludes `V_h/W_m` overlap.
* The two segments ending at p intersect only at p by its generic choice;
  the two radial segments intersect only at w. The same face-separation
  arguments exclude an extra intersection at the other endpoints.

Let Q be the region inside Gamma. All four vertices of Gamma are strictly
below the middle base, so Q is below that line too. Notice that this uses
only the half-plane below the base, **not** the stronger claim that Q lies
in the triangle `uu'p`. The latter claim needed the old near-X restriction.

At w, Q contains one of the two sectors between `wa` and `wb`. It cannot
contain the sector occupied by `W_i,W_j,W_h`. Otherwise the interior of
`W_j` is in Q: its boundary cannot cross Gamma, by the shared-vertex wedge
lemma. Its attached petal `V_j` also cannot cross Gamma, by the same lemma,
and is therefore inside Q. But `V_j` is above the base, a contradiction.

Consequently Q contains the other sector, occupied near w by `W_m` and the
slit gap. The whole fourth patch `W_m union V_m` is inside Q. To check this
containment, every possible crossing of Gamma is excluded either by a
shared uncut vertex or by Lemma L:

| Fourth-patch face | Against `V_i` | Against `V_h` | Against the radial parts |
|---|---|---|---|
| `W_m` | Shared vertex a | Lemma L | Fan wedges |
| `V_m` | Shared vertex a | Lemma L | Shared vertex a; Lemma L against `W_h` |

No opposite-petal theorem or far-fan reduction is used in this step.

## The angle identity gives a contradiction

Remove the fourth patch from Q. The remaining region has boundary

```
a -> p -> b -> w -> b' -> v_m -> a.
```

It is the same six-sided region used in the historical two-apex argument.
The preceding containment proof establishes it even when a far vertex is
past X, provided the relevant slit-side fan pair is safe. Let gamma be its
interior angle at p, and let

```
delta_a = angle(p,a,v_i),
delta_b = angle(p,b,v_h).
```

Then gamma is positive and both deltas are nonnegative. For clarity, the
six interior angles are

```
at a:    kappa_a + delta_a,
at p:    gamma,
at b:    2*pi - angle_b(W_h) - angle(p,b,u'),
at w:    kappa_w,
at b':   2*pi - angle_b'(W_m) - angle_b'(V_m),
at v_m:  2*pi - nu_m.
```

Their sum is `4*pi`. At the physical slit vertex b, the four original face
angles sum to `2*pi-kappa_b`. Also
`angle_b(V_h)=angle(p,b,u')+delta_b`. Substituting gives

```
nu_m = kappa_back + gamma + delta_a + delta_b > kappa_back.
```

The positive curvature gaps at a and w, the strict local separation from
Lemma L, and the generic interior choice of p exclude collapsed sides of
this region. A far vertex equal to X causes no change: no division by its
distance from X, nor strict near-X condition, has been used.

But R and Gauss--Bonnet give
`4*pi <= kappa_v+4*kappa_b+kappa_w`. The convex-vertex cone inequality gives
`nu_m <= pi-kappa_v/2`. Hence

```
kappa_b+kappa_w-nu_m >= (kappa_v+3*kappa_w)/4 > 0,
```

so `kappa_back>nu_m`, a contradiction. This proves the implication.

## Finish the reduction, not the whole theorem

If the two slit-side fan pairs are safe, the implication and its reflection
exclude both opposite-petal overlaps in the only remaining angle branch.
Case A and the base-cone proof cover all other branches, including equality.
Lemma L is already available at this same slit. The surviving interior-fan
reduction then excludes the two other far-fan pairs. Along with the 19
shared-vertex pairs, every pair is accounted for.

This argument reverses the useful direction of the old reduction: the
dangerous cut-side blue triangles are the tests we keep, rather than tests
we incorrectly discard.

## A further solved small-angle subcase

In `Sigma<pi`, suppose the slit-side far vertex b is at or before X along
the ray `u' -> b`. Then all three vertices of `W_h` are on w's side of A
or on A. Since `V_i` is beyond A, A itself separates `V_i` from `W_h`.
The implication above therefore also separates the opposite petals.

This includes the old two-apex branch, but is stronger: **the other far
vertex a may be beyond X**. The newly isolated small-angle obstruction
requires the *slit-side* far vertex to pass X. Passing X is necessary in
this branch, not sufficient for overlap; the saved
[apex-entry example](results/caseB-apex-entry.verification.json) passes it
and still unfolds successfully.

What remains is a universal proof that neither distant petal overlaps its
slit-side blue target under H and R. The reduction does not prove that
claim, and does not assert that the above small-angle classification
exhausts the configurations of those two fan-pair tests.

## Exact replay and scope

`far_pairs.py` independently checks the convex hull, original cut tree, H,
R, and exactly two separating-edge witnesses. Its whole-net conclusion uses
the written geometric theorems above. It does not trust a saved success flag
and does not silently accept incomplete or duplicate pair lists.

```
python3 -m n6.far_pair_examples
python3 -m n6.far_pairs n6/results/far-pair-apex-entry-family.certificate.json
```

The examples are the existing apex-entry point and 11-coordinate box,
the 18-coordinate radial box, and the large-curvature-sum point. Separate
all-28-pair certificates agree on these exact regions. This simplifies
their proof certificates; **it does not enlarge the certified domains**.
The diagram `figures/lemma-F-two-pairs.svg` identifies the targets on an
illustrative octahedron. Neither the drawing nor numerical surveys is a
premise of the universal reduction.
