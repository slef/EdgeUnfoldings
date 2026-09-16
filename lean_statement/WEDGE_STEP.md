# The wedge step: precise geometry and current Lean boundary

This isolates the step in Stephen Kiazyk's 2014 thesis, Chapter 2,
pp. 18–19, Figure 2.7. It does not claim that the full star theorem is proved.
No new theorem about polyhedra is assumed.

The later journal presentation is Kiazyk-Lubiw (2016), Section 2,
pp. 1023-1025, especially Lemma 2 and Figure 4. The precise comparison
and remaining geometric prerequisites are in
[KIAZYK_2016_REVIEW.md](KIAZYK_2016_REVIEW.md).

## What must happen at one tree edge

Write `W` for the current region and `K` for the next kite. There are two
operations: rotate the arms about the current root, obtaining `V`, then
move the root across `K`, obtaining `W'`. The required relations are

```
W ⊆ V,       V ∩ interior K = ∅,       W' = V ∪ K.
```

They give both preservation of everything already enclosed and exclusion
of the next kite before it is added. Boundary contacts are permitted.

## Rotation, by looking at one circle at a time

Let the root be the origin, the common inner-leg length be `d > 0`, and
let `γ` be the outer-leg angle. Put `τ = π - γ`. The range
`π/2 ≤ γ ≤ 3π/2` says `cos τ ≥ 0`.

For a circle of radius `ρ ≥ d`, the distance along an outer ray from its
elbow to that circle is exactly

```
t = sqrt(ρ² - d² sin² τ) - d cos τ ≥ 0.
```

The corresponding angular displacement from the inner leg is
`f(ρ) = arcsin(t sin τ / ρ)`. For `ρ < d`, set `f(ρ) = 0`.
The ray meets the circle only once. These are proved, rather than assumed,
in `travel_spec`, `ray_circle_unique`, and `outer_arm` in
[WedgeRotation.lean](SixVertexUnfolding/Geometry/WedgeRotation.lean).

If the two inner legs have unwrapped directions `l` and `u`, with the
chosen region swept counterclockwise from `l` to `u`, the circle section
is the angular interval

```
[l + f(ρ), u - f(ρ)].
```

Moving `l` downward and `u` upward enlarges this interval at every radius.
An interval of negative length is empty; an interval spanning a full turn
covers the entire circle. Thus this argument also handles the rays meeting
and the chosen region becoming bounded or having a bounded complement.
`rotate_arms` proves this containment for `polarRegion`.

## Root movement and exclusion, in Cartesian coordinates

Put the two source images at `(0,h)` and `(0,-h)`, with `h > 0`.
The old and new roots are `(r,0)` and `(q,0)`, with `r < q`.
The upper outer ray has direction `(a,b)` and the lower one is reflected.

The kite has the exact horizontal sections

```
|y| ≤ h,
r(h - |y|) ≤ hx ≤ q(h - |y|).
```

`kite_eq_triangles` proves that these inequalities describe the union of
the two actual convex-hull triangles. `interior_kite` proves that strict
inequalities give its ordinary planar interior, including the shared base.

The two outward conditions are

```
hb - ra ≥ 0,       hb - qa ≥ 0.
```

Each is a dot product between the outer-ray direction and the direction
from its root to the upper source image. These conditions follow from the
appropriate outer-leg angle lying between `π/2` and `3π/2`;
`outward_of_angle_range` checks the Cartesian calculation.

[WedgeRootMove.lean](SixVertexUnfolding/Geometry/WedgeRootMove.lean) defines
the whole region by its horizontal sections, with explicit cases for
diverging rays, a bounded region, and a bounded complement. Its main
theorem `root_step` proves

```
region(q) = region(r) ∪ kite(r,q),
Disjoint region(r) (interior (kite(r,q))).
```

The angle accounting in the thesis is precisely what keeps both outward
conditions available: if the accumulated source angle is `σ` and the next
kite angle is `α`, then `σ + α ≤ π` keeps `π/2 + σ` and
`π/2 + σ + α` in the permitted interval.

## The two descriptions are now identified

The rotation theorem uses `polarRegion`; root movement uses `region`.
Their equality is proved in
[WedgeCoordinates.lean](SixVertexUnfolding/Geometry/WedgeCoordinates.lean).

In the Cartesian coordinates above, put

```
d = sqrt(r² + h²),
θ = the direction of (-r,h), with 0 < θ < π,
a = r cos γ - h sin γ,
b = -r sin γ - h cos γ.
```

The checked identity, stated entirely in terms of the explicit definitions, is

```
z ∈ region h r a b
  ↔ z - point r 0 ∈ polarRegion d γ θ (2π - θ).
```

`exists_arm_coordinates` supplies the required polar coordinates from
`h > 0`; their existence is not an extra assumption.

The proof does more than compare boundary rays. `WedgeLevel` defines a
continuous function whose nonpositive set is precisely `region`.
`WedgeCircleZeros` locates all its zeros on each semicircle, and
`WedgeCircleSigns` uses continuity and the signs at the horizontal axis
to identify the included arc. Reflection handles the other semicircle.
This includes circles wholly inside or outside the region and all threshold
equalities. The earlier numerical comparison is no longer the only check
of this identity: the identity itself is now a Lean theorem.

## A complete planar step

[WedgeStep.lean](SixVertexUnfolding/Geometry/WedgeStep.lean),
`ArmCoordinates.rotate_and_move`, now proves all three relations at the
top of this note in a single theorem.

Let `Θ` be the new root's direction to the upper source image and `D` its
distance to that image. The theorem `kite_apex_angle` proves

```
α = angle (r,0) (0,h) (q,0) = Θ - θ.
```

With `θ ≤ l`, `u ≤ 2π - θ`, and `γ + α ≤ 3π/2`, the rotated wedge avoids
the next kite's ordinary interior, and moving the root adds exactly the
closed kite. The result has polar parameters

```
root = (q,0),   radius = D,   outer angle = γ + α,
inner directions = Θ and 2π - Θ.
```

Thus the step returns a wedge in the same form needed for iteration. The
outer rays remain fixed; a positive rescaling of their direction vectors
does not change the region. These facts are all proved in Lean.

## Application at an actual nonvertex junction

[JunctionWedgeStep.lean](SixVertexUnfolding/Geometry/JunctionWedgeStep.lean)
now proves the three required relations for any distinct incoming and
outgoing edges of an actual junction fan. The empty-gap order supplies
the unwrapped inequalities. Explicit rigid motions place the outgoing
kite in the Cartesian frame and transport the resulting sets back. The
angle increment equals the actual metric model's source angle.

The cumulative angle budget is now checked for every simple cut-tree
path in [CutTreePathBudget.lean](SixVertexUnfolding/Geometry/CutTreePathBudget.lean).
All five original nonsource cone inequalities are proved from actual
small-link coverage and nonexpanding angular arcs; see
[CONE_BUDGET.md](CONE_BUDGET.md). The step still takes an explicit outer
angle, which the global induction must identify with its accumulated sum.

Successive junction frames are now compatible, including reflections, and
the returned wedge is exactly the next incoming wedge. The first-kite
containment, finite region iteration, and final exclusion are also checked;
see [WEDGE_CHAINS.md](WEDGE_CHAINS.md).

Still open are the global cut surface, application over the complete
surface partition, original-vertex internal junctions, and transfer to
whole original faces. See [STAR_NEXT.md](STAR_NEXT.md).
