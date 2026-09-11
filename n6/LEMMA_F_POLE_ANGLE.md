# A pole-angle theorem for the remaining Lemma F cut segments

**Subsequent completion, 11 September:** [the equal-length argument](LEMMA_F_CHORD.md)
completes the selected H/R octahedron proof. Earlier open-case counts in this
note describe the investigation at that stage. The every-slit Lemma F and
full n=6 theorem remain open; the new research proof awaits independent review.


11 September 2026. **Geometric proof of a complete selected-net family.**
The full, every-slit Lemma F and the general octahedron remain open.
Numerical searches are not premises of the proof.

## The result

Assume H: v is a maximum-curvature vertex of a strictly convex octahedron.
Let w be its opposite vertex, and choose a maximum-curvature equator vertex
u_k for the slit (R). Cut star(v) together with w-u_k.

**Theorem.** This selected net is nonoverlapping if both of the following
applicable tests hold:

* If Q_(k+1) leans backward, then angle(w,v,u_(k+1)) <= pi/2.
* If Q_(k+2) leans forward, then angle(w,v,u_(k+3)) <= pi/2.

The angles are in the **original three-dimensional solid**, at v, between
the pole diagonal and the indicated incident edge. A test is unnecessary
when its patch does not lean in the indicated direction. Each test separately
proves its cut-segment condition and corresponding pairs in
[LEMMA_F_CUT_RAYS.md](LEMMA_F_CUT_RAYS.md).

**Half-turn curvature corollary.** If kappa_v >= pi (180 degrees), the
selected net always works. In this entire source-curvature branch, all
28 face pairs are proved safe. Ties in H/R and equality kappa_v=pi are
included. This is not a claim about all four slit choices.

## 1. A hypothetical crossing traps the neighboring patch

Treat the last slit segment; reflection treats the first. Write

```
i=k+1, m=k,
a=u_i, c=the first slit copy of u_k,
b=the last slit copy of u_k,
P=the developed apex of V_i, M=the developed apex of V_m.
```

The earlier through-fan proof excludes reaching wb through the interior
of the blue fan. Thus a hypothetical interior intersection of V_i with
the open segment wb requires Q_i to lean backward at a. Its extension
must exceed omega_m+kappa_w. In particular

```
0 < omega_m+kappa_w < pi,
```

because the outer angle of a nonconvex patch at w is less than pi.

The reflex vertex a lies strictly inside the outer triangle with vertices
w,u_(i+1),P. Subdividing this outer triangle at a gives W_i, V_i, and
triangle w,a,P. A ray from w that reaches V_i on the backward side
therefore first crosses the open edge aP. Call that first point q.
If the finite cut segment meets V_i's interior, q is strictly before b.
Since q lies in the open edge aP, |aq|<|aP|.

Choose p on the ray, just beyond q, still in the interior of V_i and
strictly before b, with

```
|ap| < |aP| = |aM| = |av| =: s.                       (1)
```

Let T be the closed triangle w,a,p. Its interior angle at w is the short
sector omega_m+kappa_w containing W_m and the slit gap. The entire
neighboring patch Q_m=W_m union V_m must be in T:

* W_m starts inside this sector near w. It cannot cross ap, since every
  open point of ap is inside V_i, which is disjoint from W_m by their
  common uncut vertex a. Its rays do not cross wp, and wa is its boundary.
* V_m is attached along the open equator edge ca, inside T. It cannot
  cross ap, since V_i and V_m also share the same uncut copy of a.
* It cannot cross wp: this is a subsegment of the last slit edge wb,
  and Lemma L excludes V_m/W_(k+3) overlap. An interior point of V_m on
  the open edge would force positive-area overlap with that blue triangle.
* It cannot cross wa. The corner of Q_m at a is f_m, and the full angle
  at a gives f_m+e_i=2*pi-kappa_a. Since e_i>pi, f_m<pi. Hence Q_m has
  no inward corner at a and stays on W_m's side of line wa.

These noncrossing arguments imply containment, not merely boundary
disjointness: each face has an interior point inside T, and a generic
segment from there to any proposed outside interior point would cross
an open side of T. A segment can avoid the three vertices. Boundary
touching does not allow a triangle's interior to pass through a vertex.
Consequently M is in T.

Only Lemma L and shared-vertex separation were used in this containment
step. No opposite-petal or far-fan nonoverlap was assumed.

## 2. A supporting line makes that containment impossible

Put r=|aw|. First suppose the flat angle at M between Ma and Mw is
nonobtuse:

```
(a-M) dot (w-M) >= 0.                               (2)
```

Let e=(M-a)/s be the unit vector from a toward M. Condition (2) is
equivalent to

```
e dot (w-a) <= s.
```

But e dot (a-a)=0<s and, by (1), e dot (p-a)<=|ap|<s.
Every point of triangle T therefore has projection less than s, except
possibly w itself if its projection equals s. The point M has projection
exactly s and is not w: M and w lie on opposite sides of the equator
edge ca. Thus M cannot lie in T, contradicting the containment just proved.

This also proves the **stronger, directly checkable version** of the theorem:
the corresponding angle in the flattened neighboring patch may be used
instead of the original pole angle. It need not be nonobtuse at every
developed apex in the net, just this specific neighboring copy M.

The simpler sufficient length condition s>=r follows too, since
(M-a) dot (w-a)<=sr<=s^2. Its failure does not imply an overlap.

## 3. The original pole angle implies the flat condition

Let D=|wv| in the original solid and t=|wM| in the developed patch Q_m.
The corner f_m at a was proved strictly below pi. On the unit sphere
centered at a, the triangle inequality through the edge direction ac gives

```
angle(w,a,v) <= angle(w,a,c)+angle(c,a,v) = f_m < pi.
```

The cosine law therefore yields t>=D. If beta=angle(w,v,a)<=pi/2,
the cosine law in the original pole triangle gives

```
r^2 <= s^2+D^2 <= s^2+t^2.
```

The last inequality is exactly (2), by the cosine law in triangle w,a,M.
The previous contradiction excludes the cut-segment crossing. Reflection
proves the other test. The selected-slit cut-segment equivalence, with its
H/R hypotheses retained, then excludes all 28 face pairs.

## 4. Why a source curvature of at least 180 degrees suffices

The spherical-link bound from Section 1 of
[LEMMA_L_PROOF.md](LEMMA_L_PROOF.md) applies at v. The direction toward
its nonneighbor w lies strictly inside the link. For every incident edge
va, it gives

```
2*angle(w,v,a) < Gamma_v = 2*pi-kappa_v.
```

If kappa_v>=pi, every such pole angle is strictly less than pi/2. Thus
both applicable tests of the theorem hold, regardless of the inward-patch
pattern. Lemma L already supplies the three local pairs at the selected
slit. The argument above completes the six far pairs on this entire
curvature branch.

This gives an original-edge unfolding for every octahedron with a vertex
of curvature at least pi: choose a globally sharpest vertex, whose
curvature is also at least pi, and then the maximum-curvature equator slit.

## 5. A quarter-turn gap also handles obtuse pole angles

There is a second way to finish an applicable cut test. Put
delta=omega_m+kappa_w in the last-cut notation above. If r>=s, the circle
centered at a of radius s is contained in the closed half-plane through w
facing a. Its only possible point on the boundary line is w, when r=s.
The developed apex P is on this circle and is not w. Its backward angular
extension B_i is therefore strictly less than pi/2. The through-fan route
was already excluded. Consequently **delta>=pi/2 and r>=s exclude the
cut segment**, including equality in either hypothesis. Reflection gives
the first-cut version with delta=omega_(k+3)+kappa_w.

If the original pole angle beta is obtuse then r^2>s^2+D^2, so r>s.
Thus an obtuse original angle still causes no difficulty when the blue
angle plus gap is at least 90 degrees. Each target may use either this
quarter-turn argument or the nonobtuse projection argument; the two
targets need not use the same proof.

For delta in (0,pi/2), the circle gives a sharper sufficient condition
s<=r*sin(delta): the cut ray misses the disk's interior, hence it cannot
cross the open edge aP into V_i. Tangency gives only boundary contact.
This refinement is a written sufficient test; the checker below currently
implements the simpler quarter-turn version.

## 6. The precise remaining branch

A counterexample to the selected-net rule must now satisfy all of:

1. 2*pi/3 <= kappa_v < pi; hence every vertex has curvature below pi.
2. One of the two remote patches leans toward its slit gap and reaches
   the corresponding cut ray, as in LEMMA_F_CUT_RAYS.md.
3. At the relevant reflex equator endpoint a, the original pole angle
   angle(w,v,a) is obtuse. The spherical-link bound narrows it to
   pi/2 < angle(w,v,a) < pi-kappa_v/2 <= 2*pi/3.
4. The corresponding angle at the neighboring developed apex M must
   still be obtuse; flattening must not have made (2) true.
5. The blue angle plus gap is strictly below pi/2, and s>r*sin(delta).
6. The petal must enter the finite segment before its endpoint.

These are necessary conditions, not an assertion that their joint domain
is nonempty. The low-curvature family is partly covered by the nonobtuse-angle
and quarter-turn tests; its universal remaining obtuse, acute-gap branch is open.

Exchanging the poles is not an automatic completion: although one of the
two angles in triangle v,w,a is nonobtuse, the new source may fail H.
In particular the Case A no-wrap premise of the whole-net reduction must
not be transferred to that source without a separate argument.

The universal count over all selected shapes remains 22/28. Within the
new half-turn-curvature family it is 28/28. Original Lemma F asks for every
slit under H; this proof retains R and does not settle that statement.

## Exact checking

`far_projection.py` verifies strict convexity, the original cuts, H/R,
and the relevant corner directions. It then proves either the source
half-turn curvature condition or one nonobtuse dot product per necessary
test. The original angle uses only the coordinate expression

```
(w-v) dot (a-v) >= 0.
```

The stronger flat test is obtained by developing only Q_m. All signs use
outward rational intervals. An undecided sign remains unresolved. The
whole-net conclusion uses the written proof above; independent all-28-pair
replays check the saved examples on their stated coordinate domains.

Run `python3 -m n6.far_projection_examples` for four exact replays: a
three-common-direction point above 180 degrees; a point below 180 degrees;
an 18-coordinate box of independent half-width 1/10000 about that point;
and a point whose original and neighboring flat pole angles are both
obtuse, repaired by the quarter-turn argument. All 28 face pairs also
have independent certificates on each of these domains. The last point
refutes universality of the nonobtuse sufficient test, not Lemma F.
