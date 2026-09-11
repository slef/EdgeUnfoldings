# Lemma F: the remaining obstruction must enter through the slit gap

11 September 2026. **Proved reductions and sufficient subcases; the general
selected-slit claim remains open.** No numerical search is a proof premise.

Assume H (v has maximum curvature among the six vertices) and R (the slit
u_k has maximum curvature among the four equator vertices). All indices
below are modulo four. Let c_first and c_last be the two developed copies
of u_k. The fan is ordered W_k,W_(k+1),W_(k+2),W_(k+3).

## 1. Two line segments, instead of two triangle pairs

The entire selected net is nonoverlapping if and only if

```
(w,c_first) misses the interior of V_(k+2),
(w,c_last)  misses the interior of V_(k+1).             (S)
```

Here the parentheses denote open, finite segments. Touching a petal's
boundary is allowed. This is a strengthening of the test reduction in
[LEMMA_F_CUT_REDUCTION.md](LEMMA_F_CUT_REDUCTION.md), not an assertion that
the tests always pass.

**Proof, one side.** Use the last triple in that proof, with i=k+1,
h=k+3, a=u_i, b=c_last. Its hypothesis that V_i/W_h is safe was used to
exclude an intersection of the interior segment ap with bw. The second
condition in (S) supplies exactly that exclusion. It also excludes b being
inside V_i, since then points of the open segment near b would be inside.
The endpoint w cannot be inside V_i: a neighborhood would meet the fan
face W_i to which V_i is attached. Lemma L supplies the other exclusions.

Thus the same simple curve a,p,b,w,a, fourth-patch containment, and hexagon
angle contradiction prove V_i/V_h safe when the fan-angle sum is below pi.
The existing Case A and base-cone arguments prove it in the other branches.
This step requires only the second condition of (S), not the first.

Now V_i cannot enter W_h through any of W_h's three open edges:

* The slit edge wb is excluded by (S).
* The other radial edge is shared with W_(k+2). A point of this edge in
  the interior of V_i would give positive-area V_i/W_(k+2) overlap, which
  is excluded by their shared uncut vertex u_(k+2).
* The equator edge is shared with V_h, whose interior has just been
  proved disjoint from V_i.

V_i has interior points outside W_h, close to the midpoint of its own
equator edge. That midpoint lies strictly within W_i's angular wedge,
disjoint from W_h's wedge. If V_i also had an interior point inside W_h,
a generic segment inside the convex triangle V_i would cross an open edge
of W_h. It can be chosen to avoid the three vertices; all such crossings
were excluded. Hence V_i/W_h is safe.

Reflection proves the first pair. The earlier two-pair reduction now gives
the whole net. Conversely, a point of either open slit segment inside its
remote petal has a small disk inside that petal; part of the disk lies
inside the adjoining blue triangle. This is a positive-area overlap.
Therefore whole-net safety implies (S). All implications include boundary
contact and equality, without assuming a general position for the solid.

In particular, each of the two conditions separately proves its cut-side
fan pair and its corresponding opposite-petal pair safe under H and R.

## 2. Lemma L already excludes entry through the fan

Write omega_i for the angle of W_i at w and kappa_w for the slit gap.
For the flat patch Q_i=W_i union V_i, let B_i and F_i be its nonnegative
angular extensions before and after its blue wedge, as viewed from w.
They are zero unless Q_i has an inward corner at u_i or u_(i+1),
respectively. A flat patch has at most one inward corner.

Place w at the origin, the first slit ray at angle zero, and unwrap the
fan counterclockwise to angle Gamma=2*pi-kappa_w. Then V_(k+1)'s angular
range is contained in

```
[omega_k-B_(k+1),
 omega_k+omega_(k+1)+F_(k+1)].                         (1)
```

This is an ordinary unwrapped interval: the petal is strictly separated
from w by its equator line. If the patch is convex it stays in its blue
wedge. If it has an inward corner, its outer triangle with vertex w has
angle less than pi and contains the patch, giving (1).

Section 3 of the [complete Lemma L proof](LEMMA_L_PROOF.md) works at every
opening under the pole comparison kappa_v>=kappa_w. Apply that through-fan
bound at opening u_(k+1), without changing the selected net or invoking R
at a different vertex. Patch extensions and omega values are invariant
under this change of frame. It gives

```
F_(k+1)+B_k <= omega_(k+2)+omega_(k+3),
```

strictly if either extension exists. Consequently the upper endpoint in
(1) is strictly less than Gamma: V_(k+1) cannot reach the last slit ray
by extending forward through the intervening blue fan.

The same ray also has angle -kappa_w. Thus its only possible entry into
V_(k+1) is backwards, across the first blue wedge and the slit gap. An
interior intersection requires

```
B_(k+1) > omega_k+kappa_w.                            (2)
```

Reflection gives the necessary condition for the other remote petal:

```
F_(k+2) > omega_(k+3)+kappa_w.                        (3)
```

The intervals in question have width less than pi, so no additional
multiple-turn copy of the cut ray can occur. Equality in the opposite of
(2) or (3) puts the ray on an angular boundary; it does not meet the
petal interior.

## 3. New proved sufficient families

Combining the segment reduction with the angular argument proves:

> Under H and R, the selected net unfolds whenever
> B_(k+1)<=omega_k+kappa_w and
> F_(k+2)<=omega_(k+3)+kappa_w.

This is a geometric sufficient condition on the entire shape family, not
an exact certificate for just one coordinate box. Each inequality alone
settles the corresponding cut-side fan and opposite-petal pair.

Some useful subcases follow immediately:

1. **Direction alone can suffice.** If Q_(k+1) is convex or leans forward,
   B_(k+1)=0 and its test is proved. If Q_(k+2) is convex or leans backward,
   F_(k+2)=0 and its test is proved. If both descriptions apply, the whole
   selected net is proved safe.
2. **The past-X branch is smaller.** In the small-fan-angle branch, the
   earlier proof covers a slit-side endpoint at or before X. Even past X,
   the remote petal's pair is now proved safe unless that petal leans
   toward the slit gap and exceeds (2) or its reflection. Passing X and
   pointing into the outer wedge are insufficient to create an overlap.
3. **Same-direction patches leave one test.** If every nonconvex patch
   leans backward, all F_i vanish. Only (w,c_last)/V_(k+1) remains to
   check. If Q_(k+1) is convex, even that test is automatic. The reflected
   statement holds when every lean is forward. This applies in particular
   to the remaining three-patch, common-direction pattern; it does not
   settle its last test.
4. **A pole-angle sufficient condition.** The through-fan bound applied
   at u_(k+2) gives B_(k+1)<omega_k+omega_(k+3) whenever B_(k+1)>0.
   Thus kappa_w>=omega_(k+3) suffices for (2) to fail. Reflection gives
   kappa_w>=omega_k for the other test. If both endpoint blue angles are
   at most kappa_w, this selected net works. In particular kappa_w>=2*pi/3
   suffices, by omega_i<=pi-kappa_w/2. This does not enlarge the earlier
   existence theorem for that curvature range; it specifies this net.

## 4. What is still open

We have **not proved** that the two angular bounds always hold under H/R.
They are a promising stronger target. If either fails, the finite segment
may still miss the petal: the ray might meet it only beyond its endpoint.
That is a distance question, and (S), not the stronger ray claim, is the
necessary-and-sufficient target.

For small-angle Case B, after reflection if needed, a remaining obstruction
requires all of: slit-side endpoint past X, backward remote patch,
B_(k+1)>omega_k+kappa_w, and entry before the endpoint of the cut edge.
The general far-fan problem must also be checked outside the small-angle
branch. We do not identify the entire Lemma F problem with Case B alone.

The unconditional count remains 22/28 pairs. Neither the full octahedron
theorem nor the stronger every-slit Lemma F is established here.

## 5. Exact finite-segment / ray replay

`cut_rays.py` checks the hull, H, R, and cut tree, then develops only the
two target petals and their slit edges. For a counterclockwise petal edge
A -> B, a point x(t)=w+t(c-w) is strictly inside its half-plane exactly when

```
c_e+t*d_e>0,
c_e=det(B-A,w-A), d_e=det(B-A,c-w).
```

The three inequalities are linear in one real variable t. The checker uses
outward rational intervals for c_e,d_e. For t>=0, replacing them by their
upper bounds gives necessary inequalities for entry. If these relaxed
strict intervals have empty intersection with 0<t<1, (S) is proved. It
also checks t>0, the optional stronger ray condition. An unresolved check
is not reported as a collision or a proof.

The four saved examples are replayed against their independent all-28-pair
certificates. The boxes are the existing 11- and 18-coordinate families;
this replay does not enlarge their domains. Tests include the old exact
cut-edge crossing with H absent, genuine radial-only separation, and
boundary touching, to distinguish a finite segment from an infinite ray.

```
python3 -m n6.cut_ray_examples
python3 -m n6.cut_rays n6/results/cut-rays-apex-entry-family.certificate.json
```

## Exploratory record, separate from the proofs

The initial attack used 1,500 random octahedra as starting candidates,
then 12 hill-climbing restarts of 1,600 steps each, maximizing violation
of the two proposed angular bounds. Every retained value was negative;
the closest unpenalized value was approximately -0.000979 radians.
One retained restart violated a search guard, illustrating the need to
inspect near-degeneracy. These are floating-point outcomes only, not a
coverage certificate, error bound, or proof of either inequality.

The coordinates and settings are retained in
[the search record](results/cut-ray-angular-search.json). Reproduce with
`python -m n6.cut_ray_search --output /tmp/cut-ray-search.json` in the
scientific environment. Any apparent violation must be independently
rationally certified before it can refute the conjecture.
