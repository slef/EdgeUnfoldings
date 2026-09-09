# A half-turn fan handles one bad patch or two adjacent bad patches

9 September 2026, continuation after the boundary audit.
**These are geometric proofs for explicit subfamilies. The general
octahedron and the fixed sharpest-source rule remain open.** The subsequent
[two-pole argument](OCTA_ONE_PATCH.md) proves the entire one-patch family
when one pole is globally sharpest. This argument does not use the refuted far-fan reduction or a
shortest-path theorem.

## The rule in ordinary terms

Choose opposite vertices v,w. Flatten each pair of triangles sharing an
equator edge, producing four patches Q0,...,Q3. Call a patch bad when it has
an inward corner. Exchanging v and w does not change which patches are bad.

**Theorem.** Suppose there is just one bad patch, or two bad patches next
to each other. If either pole has curvature at least 180 degrees, the
octahedron has a nonoverlapping edge unfolding of the star-plus-one-edge
form.

Use the pole of curvature at least 180 degrees as w, the center of the
uncut fan. Cut all four edges at the other pole v. The remaining fan has
total angle at most 180 degrees, leaving a gap of at least 180 degrees.
Choose the fifth cut by the table below. It puts each troublesome patch
where the large gap prevents it reaching a nonadjacent patch.

This often places the four cuts at the **less sharp** pole. It proves an
edge unfolding for the stated family, not the user's fixed sharpest-source
conjecture. There is no additional sharpest-vertex assumption.

## Notation and an elementary cone bound

Indices are cyclic modulo four. Use the notation of
[OCTA_CONVEX_PATCHES.md](OCTA_CONVEX_PATCHES.md):

    W_i = w u_i u_(i+1),   V_i = v u_i u_(i+1),   Q_i = W_i union V_i.
    omega_i = angle of W_i at w,   kappa = curvature at w.

Order the equator so the fan develops counterclockwise. A bad patch has
exactly one reflex equator corner. It leans **forward** if that corner is
u_(i+1), and **backward** if it is u_i. Let F_i or B_i, respectively, be
its angular extension beyond its blue triangle, viewed from w. The unused
extension is zero. Both extensions are zero for a convex patch, including
one with a straight corner.

For a bad patch its reflex vertex lies strictly inside the triangle formed
by the other three vertices. Thus its entire angular cone at w is the
angle of that outer triangle, strictly smaller than pi. In particular,

    forward:  omega_i + F_i < pi;
    backward: omega_i + B_i < pi.

This is a bound on the entire two-face patch, including its blue triangle.
It therefore treats the cut-side far-fan pairs directly.

## Which pairs actually need a check

Two successive patches sharing an **uncut** radial edge cannot overlap:
their four triangles develop around the same equator vertex and occupy
consecutive wedges whose total is 2*pi minus that vertex's positive
curvature. Within a patch its two triangles lie on opposite sides of their
base. Neither observation requires convexity of the patches.

Consequently only the two opposite patch pairs and the two patches beside
the slit need a further check. For the opening Z_k at w-u_k, a sufficient
angular separation test is the following six inequalities:

    F_k     + B_(k+2) <= omega_(k+1)
    B_k     + F_(k+2) <= omega_(k-1) + kappa
    F_(k+1) + B_(k-1) <= omega_(k+2)
    B_(k+1) + F_(k-1) <= kappa + omega_k
    B_k     + F_(k-1) <= kappa
    F_k     + B_(k-1) <= omega_(k+1) + omega_(k+2).

To verify the test, start the developed fan at angle zero and assign Q_i
the interval [theta_i-B_i, theta_i+omega_i+F_i]. For each opposite pair,
the first four inequalities leave a nonnegative gap along both circular
routes between its intervals. The last two do the same for the flank
patches. These intervals have width below pi; the two gaps ensure their
interiors are disjoint, even if an interval crosses angle zero. Boundary
contact is permitted. Together with the shared-vertex observation, this
checks every pair of faces. These are the same sufficient wedge tests
explored in the older `durer_small_n/wedge.py`; the new step is proving
them automatically in the following regimes.

## One bad patch: a weaker condition also suffices

Suppose Q_i is the only bad patch.

| Direction | Fifth cut | Sufficient inequality |
| --- | --- | --- |
| Forward | w-u_(i+2) | F_i <= omega_(i+1) + kappa |
| Backward | w-u_(i+3) | B_i <= omega_(i-1) + kappa |

Substitution in the six inequalities leaves just the displayed nonzero
condition; all others have zero on the left. This proves the rule.

There is a useful test involving only original face angles. For a forward
patch, put S=omega_(i+2)+omega_(i-1). Since the four omega angles sum to
2*pi-kappa, the condition is equivalent to

    (omega_i+F_i) + S <= 2*pi.

The first parenthesis is strictly below pi by the cone bound. Hence **S<=pi
is sufficient**. For a backward patch use S=omega_(i+2)+omega_(i+1).
This gives a larger provable family than the curvature threshold alone.
One may test either pole as fan center, keeping the same physical two
equator edges and reversing the cyclic labeling when the poles are exchanged.

If kappa>=pi, the whole fan angle is at most pi, so either specified
two-angle sum is less than pi. This proves the one-patch part of the theorem.

The two-angle test is **not automatic**, even with v globally sharpest.
The saved `half-fan-angle-limit` example has one forward bad patch but
omega_2+omega_3>pi and nu_2+nu_3>pi. Exact interval signs, not the search
that found the example, certify this limitation. It still has a successful
edge unfolding. Failure of this sufficient test does not refute the
weaker extension inequality above, or any unfolding conjecture.

## Two adjacent bad patches: three direction cases

Rotate the labels so the bad patches are Q_i,Q_(i+1). They cannot be
forward then backward: that would put both reflex corners at u_(i+1),
requiring more than 2*pi of face angle there. The other three possibilities
have explicit openings:

| Directions of Q_i, Q_(i+1) | Fifth cut |
| --- | --- |
| Forward, forward | w-u_(i+2) |
| Backward, backward | w-u_i |
| Backward, forward (leaning away from each other) | w-u_(i+3) |

Here is a direct substitution proof. Relabel i=0. In the forward-forward
case with k=2, the only nonzero left sides in the six tests are F0, F1,
and F1; their right sides are omega1+kappa, kappa+omega2, and kappa.
In the backward-backward case with k=0 they are B0, B1, and B0, with
right sides omega3+kappa, kappa+omega0, and kappa. In the backward-forward
case with k=3 they are F1 and B0, with right sides omega2+kappa and
kappa+omega3. Every extension is strictly below pi, and kappa>=pi.
All these tests therefore hold. The other tests have zero left sides
and positive right sides. This proves all three cases, including the
boundary kappa=pi.

In fact these substitutions only need each nonzero extension to be at
most kappa. The stated curvature threshold is a simple way to guarantee
that without measuring the developed extension.

## Exact replay and scope

`n6.half_fan` verifies the hypotheses and the table's selected original
edge tree on an explicit point or parameter region. Unknown interval signs
are rejected. Separate `n6.polycert` certificates check all 28 face pairs
of the examples without invoking this mathematical argument.

The theorem includes straight corners in the good patches and exactly
180-degree pole curvature. Strict convexity of the original octahedron's
facets and vertices is retained. It establishes further subfamilies of
the one-patch and adjacent-two-patch regimes. This half-fan argument alone
does not settle those regimes in full; the two-pole argument now closes the
one-patch existence family under H. Neither excludes another entire original fixed-source
failure class: the conservative count remains **2 excluded, 47 open**.

**Subsequent extension:** [OCTA_PATCH_BUDGET.md](OCTA_PATCH_BUDGET.md)
removes the half-turn restriction for adjacent bad patches under H,
using the sum of the extensions seen from both poles. It also proves
opposite two-patch configurations and mixed directions with three bad
patches. Three with a common direction remain open. The present half-fan
theorem retains the benefit of requiring no globally sharpest pole.

```sh
python3 -m n6.half_fan n6/results/half-fan-adjacent-family.certificate.json
python3 -m n6.polycert verify n6/results/half-fan-adjacent-family.certificate.json --bits 240
python3 -m n6.half_fan n6/results/half-fan-angle-limit.certificate.json --audit-two-angle-failure
```
