# Lemma L is proved when the slit-plus-fan curvature is at most pi

11 September 2026 JST. This is a geometric proof for an entire angular
branch, not a conclusion drawn from numerical examples. **Subsequent completion:** [LEMMA_L_PROOF.md](LEMMA_L_PROOF.md) also proves
the complementary branch and finishes Lemma L.

## Statement

Let v,w be opposite vertices of a nondegenerate convex octahedron. Choose
an equator vertex u with maximum curvature among the four equator vertices.
Cut the four edges at v and the edge wu. If

    sigma := kappa_u + kappa_w <= pi,

then all three local pairs at the slit are nonoverlapping. The source v
does not need to be globally sharpest for this result. Thus it applies,
in particular, under both selection rules of Lemma L.

The [curvature gate](LEMMA_L_CURVATURE_GATE.md) already excludes meeting
through the intervening fan in this branch. The missing part was to handle
an inward petal reaching across the slit. A line through its own cut edge
vu separates it from the entire opposite patch, even when no separating
line through w exists.

## Notation and the curvature estimate supplied by the slit rule

Relabel the opening as u0=u, with first patch Q0=W0 union V0 and last patch
Q3=W3 union V3. Their angles at the two copies of u are e and f, so

    e+f = 2*pi-kappa_u.

All six vertex curvatures are positive and less than 2*pi. Since u is
maximum among the four equator vertices, Gauss--Bonnet gives

    4*kappa_u >= 4*pi-kappa_v-kappa_w > 2*pi-kappa_w.

In particular,

    2*kappa_u+kappa_w > pi.

The proof below only needs the weaker inequality 2*kappa_u+kappa_w>=pi.
This is useful if applying it with a different slit-selection rule.

## First dispose of angularly separated configurations

At most one of e,f can exceed pi, because e+f<2*pi. If neither does, there
is no extension across the slit, so the curvature gate proves all local
pairs safe. Straight corners are included here.

By reflection we may therefore suppose e>pi. Put rho=e-pi. Let B>0 be
the first patch's angular extension across its slit ray. The small triangle
with vertices w,u,V0's apex gives

    0 < B < rho < pi-kappa_u.

The last patch cannot extend across its slit ray. If B<=kappa_w, the two
patch cones are angularly separated across the slit as well; equality
allows a shared direction but no positive-area overlap. All local pairs
are safe in that case.

It remains to consider B>kappa_w, hence

    0 < kappa_w < rho < pi-kappa_u.

This also implies sigma<pi, so the boundary sigma=pi has already been
handled without this final case.

## The two copies of u lie on opposite sides of the candidate separator

Set w=(0,0), put the first copy A of u at (r,0), and the last copy at

    A' = r*(cos(kappa_w), -sin(kappa_w)),  r=|wu|>0.

The first petal's apex P lies at

    P = A + s*d,
    d = (cos(rho), -sin(rho)),  s=|uv|>0.

This follows from the reflex patch angle e=pi+rho at A. The first petal
V0 lies in the closed left half-plane of the oriented line A->P: its third
vertex is strictly to the left, because the two triangles of Q0 are glued
on opposite sides of their common base.

We claim the other copy A' lies strictly to the right of that line. Indeed,

    det(d,A'-A) = -2*r*sin(kappa_w/2)*cos(rho-kappa_w/2).

The sine factor is positive. Since rho>kappa_w,

    0 < rho-kappa_w/2
      < pi-kappa_u-kappa_w/2
      <= pi/2.

The final inequality follows from 2*kappa_u+kappa_w>=pi. The strict
inequality before it comes from f>0, so it also covers equality in that
weaker curvature hypothesis. Thus the cosine is positive and the determinant
is strictly negative, as claimed.

## The entire opposite patch stays to the right

Viewed from A', the whole last patch Q3 lies in the sector of angle

    f = pi-kappa_u-rho < pi

between its edge toward w and its edge toward the last petal apex P'.
Both triangles W3,V3 contain A', so this sector contains both entire faces,
including the case when Q3 is inward at its other equator corner.

Measured from the positive x axis, its boundary directions can be lifted to

    direction(A'->w)  = -pi-kappa_w,
    direction(A'->P') = -rho-sigma.

Relative to d, of direction -rho, this is the interval

    [rho-pi-kappa_w, -sigma].

Its lower endpoint is greater than -pi because rho>kappa_w. Its upper
endpoint is below zero because sigma>0. The endpoints have the stated
order because their difference is f>0. Consequently every nonzero vector
from A' into Q3 lies strictly to the right of a line parallel to d.

We already proved A' itself strictly right of the line A->P. Adding those
vectors puts every point of Q3 strictly right of A->P. But V0 lies left of
that line. Therefore **V0/W3 and V0/V3 are both nonoverlapping**.

The third local pair V3/W0 is safe by the curvature-gate reduction: Q3 has
no extension across its slit ray, and the gate excludes the other route.
Reflection gives exactly the same conclusion when the last patch is inward
at the slit. This completes the proof of all three pairs for sigma<=pi.

## What this changes, and what it does not

- The whole branch sigma<pi is now proved, including configurations where
  the two faces have overlapping angular directions around w.
- The equality branch sigma=pi remains proved by the curvature gate.
- For sigma>pi, the across-slit route is excluded, but the route through
  the fan is now excluded by the complete Lemma L proof.
- This small-sum result initially closed two of three curvature branches.
  The subsequent complete proof changes the current universal local count
  to **3/3** over all selected octahedra.
- The full octahedron and n=6 theorem remain open. Local safety does not
  prove the opposite-petal or far-fan obligations of Lemma F.

The older radial example and its 18-coordinate neighborhood are now inside
this universal local theorem. Their exact separating-line checks illustrate
the proof, while their independent all-pairs certificates still establish
whole-net safety only on the specified coordinates or box.
