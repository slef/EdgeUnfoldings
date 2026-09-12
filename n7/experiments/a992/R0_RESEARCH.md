# R0 continuation: from an obtuse angle to one proved pair

12 September 2026. The positive result is in
[A992_R0.md](../../A992_R0.md). The geometry and exact identity there, not
any experiment below, prove the E/135 obligation throughout R0.

## Routes investigated

R0 makes both angles at 0 in E = 036 and F = 046 obtuse. A tempting stronger
claim was that the hinge line 36 in Right separates E from all three residual
faces. Varying only base vertices 1 and 5 while keeping a known local Left
failure fixed found apparent violations of that supporting-line claim; Right
still worked in those examples. The 42,000 attempted extensions included
7,313 valid numerical shapes. The best violating parameters and all three
Right pair scores are retained. This is a failed separator shortcut, not a
counterexample to the two-attachment conjecture.

The E/135 pair reduces to the five-vertex triangular bipyramid on 0, 1, 3,
5, 6. This suggested the stronger local statement that an obtuse pole angle
in a petal prevents it from meeting the opposite fan triangle. The first
14,000-sample experiment found no robust violation; the corresponding
unrestricted-petal search found apparent overlap at its second sample.
A second search concentrated on the difficult inward-at-6 configurations,
using positive barycentric relations to keep the two poles on opposite
sides of the equatorial triangle. It found no robust violation in 52,000
samples. Very small scores in these runs are inconclusive. These findings
motivated the theorem; they did not prove it.

Several stronger planar claims were not used: a single fixed edge line need
not separate the triangles; an enclosing-cone comparison can leave an
angular overlap even when the finite triangles remain disjoint; and a
Thales semicircle over a hinge is not automatically empty of the rest of
an arbitrary fan. No empty-sector property for arbitrary star unfoldings
was assumed. The published truncation route in the earlier notes remains
separate and incomplete.

## The successful proof step

A comparison triangle 056 can be attached along 56. Shared-vertex fan
arguments already separate it from E and 135. If E met 135 in the narrow-fan
branch, the comparison triangle would be trapped in the triangle bounded
by vertex 1, vertex 6, and an overlap point. Its copy M of vertex 0 has
exactly the same distance from 6 as E's copy P.

An important detail is that the line from 1 through the overlap point meets
the **open edge** 6P. That intersection may occur after the chosen overlap
point on the ray. The proof does not need it to precede that point, or need
the overlap point itself to be closer to 6 than P. This avoids an incorrect
finite-distance assumption that would have excluded valid configurations.

The sine comparison forces `2 theta + 2 delta + kappa_6 < pi`. A linear
exploration of the angle constraints suggested the positive contradiction.
After eliminating the auxiliary variables, it is simply

`2 theta + 2 delta + kappa_6 - pi`
`= (Gamma_6 - 2 angle_6(136)) + (2 angle_0(036) - pi)`
`  + 2 angle_3(036) + 2 delta > 0`.

This uses the triangle angle sum and the definition of the vertex angle
sum. The coefficient checker `python3 -B -m n7.r0_identity` uses exact
integers and does not invoke a linear optimizer. The geometric proof also
checks the convex auxiliary hull, all shared-vertex paths, containment,
strictness, and the equality case at an angle of 90 degrees.

A new original A992 example was independently rounded to rational
parameters and certified with outward rational intervals. It has Left
overlap, R0 membership via the cone theorem, an inward-at-6 Right patch,
and a fan angle at 1 below pi. Its independent Right separators cover all
three residual pairs on that shape. Replay it with `python3 -B -m
n7.r0_examples`; this finite certificate is not a universal proof premise.

## What remains

E/Q and E/235 remain open in R0; all three R6 implications remain open.
The next natural target is E/235. Its path can be localized by replacing P
with the quadrilateral 1256, leaving six vertices. Removing vertex 4 gives
an auxiliary hull with original supporting triangles 023, 036, 135, 136,
235 and base 1256, plus triangle 026. The cut-star at 3 is available in that
auxiliary hull, but the Right attachment is a different tree. Do not infer
Right's safety from the mere existence of a star unfolding.

The nearest-point observation is also worth retaining: both obtuse angles
at 0 imply that 0 is the unique Euclidean closest point of Q to 6. Every
direction into the convex Q from 0 is a nonnegative combination of its two
boundary directions toward 3 and 4; each has strictly negative dot product
with 6−0. Expanding squared distances proves the claim. This is a spatial
constraint for the E/Q problem; by itself it does not separate their
unfolded copies.
