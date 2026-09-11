# One nonconvex patch: two prescribed nets, with the poles exchanged

**Subsequent completion, 11 September:** [the equal-length argument](LEMMA_F_CHORD.md)
completes the selected H/R octahedron proof. Earlier open-case counts in this
note describe the investigation at that stage. The every-slit Lemma F and
full n=6 theorem remain open; the new research proof awaits independent review.


9 September 2026, continuation after the hinge audit.

**Theorem.** Choose a globally sharpest vertex v of a strictly convex
octahedron and let w be its opposite vertex. If exactly one of their four
two-face patches is nonconvex, the octahedron has a nonoverlapping edge
unfolding. Two explicitly prescribed cut trees suffice: one cuts the four
edges at v, the other cuts the four edges at w.

This settles the **existence** of an edge unfolding for the one-bad-patch
family under H. It does **not** restore the old assertion that one of the
four nets cutting the star of v must work. That stronger assertion remains
open. The proof below uses the full patch cones and never invokes the
refuted far-fan reduction.

## The two cuts to try

Use cyclic equator labels u0,u1,u2,u3. Rotate or reverse them so the unique
bad patch is Q0, and its inward corner is u1. The other equator endpoint
u0 is its convex corner. The vertex opposite that inward corner is u3.

The two candidate trees are:

    A: cut all four edges at v, and the edge w-u2;
    B: cut all four edges at w, and the edge v-u2.

In the usual counterclockwise labeling, if the bad patch Q_i leans
forward, these are star(v)+w-u_(i+2) and star(w)+v-u_(i+2). If it leans
backward, they are star(v)+w-u_(i+3) and star(w)+v-u_(i+3). Thus both
trees use the same equator vertex for the fifth edge: the vertex opposite
the bad patch's **convex** equator corner.

Flatten the bad patch by itself. Its inward corner lies inside the triangle
formed by its other three vertices w,u0,v'. Write delta and eta for that
outer triangle's angles at w and v', and e for its angle at u0. Hence

    delta + eta + e = pi,      delta, eta, e > 0.

Let omega_i be the original face angle at w in W_i, and nu_i the face
angle at v in V_i. Define

    S_w = omega_2 + omega_3,   S_v = nu_2 + nu_3.

The direct angular-separation proof in [OCTA_HALF_FAN.md](OCTA_HALF_FAN.md)
gives the following sufficient tests for the **entire nets**, including
the cut-side blue triangles:

    A is safe if delta + S_w <= 2*pi;
    B is safe if eta   + S_v <= 2*pi.

For A this is the one-forward-patch test after substituting
delta=omega_0+F_0 and the total fan angle 2*pi-curvature(w). For B,
exchange the poles and reverse the ring. The bad patch then leans backward;
the corresponding two-angle sum still uses the same physical equator
edges u2-u3 and u3-u0. This yields precisely tree B above.

## Why the two tests cannot both fail

Suppose, for contradiction, that both tests fail. Since delta and eta are
less than pi, their failures force

    S_w > pi,   S_v > pi.

Each S is only part of its pole's total face angle. Thus **both poles have
curvature less than pi**.

Adding the two failed tests and using delta+eta=pi-e gives

    S_w + S_v > 3*pi + e.

Now add the angles of the four original triangles W2,V2,W3,V3 on the
other side of the equator. Their total is 4*pi. Their angles at v and w
sum to S_v+S_w. Their four angles at u3 comprise that vertex's complete
face angle tau_3. The remaining angles are e_2 at u2 and f_3 at u0,
both positive. Therefore

    S_w + S_v + tau_3 + e_2 + f_3 = 4*pi.

The preceding strict inequality implies

    tau_3 < pi - e - e_2 - f_3 < pi.

So **u3 has curvature greater than pi**, while both poles have curvature
less than pi. In particular u3 is sharper than v, contradicting H.
At least one of A and B therefore passes its sufficient angular test and
is a nonoverlapping original-edge net. Equality in a test is accepted:
it can cause boundary contact, which is allowed.

This is an angle-sum contradiction, not an inference from numerical
searches. It also does not infer that an overlap occurs merely because a
sufficient test fails: simultaneous actual failure of A and B would force
both sufficient tests to fail, which has just been excluded.

## A weaker curvature hypothesis

The argument only needed that u3 could not be sharper than both poles
while having curvature above pi. It consequently also proves the same
two-tree result if **either pole has curvature at least curvature(u3)**,
or if **curvature(u3)<=pi**, without global sharpness. For a backward bad
patch the comparison vertex is again the equator vertex opposite its
reflex corner. The globally sharpest-pole theorem is the immediate case
relevant to the user's proposed strategy.

## What changes in the proof status

- The zero-patch family retains its stronger result: every opening works.
- The one-patch family under H now has a complete **two-pole existence
  proof**. Its **fixed sharpest-source** four-choice statement is still open.
- The later [patch-budget theorem](OCTA_PATCH_BUDGET.md) now treats all
  two-patch arrangements and mixed directions with three bad patches
  under H. Three bad patches sharing a common direction remain open.
- The conservative original fixed-source target is unchanged: **49
  classes, 2 excluded, 47 open**. A theorem allowed to exchange the cut
  source cannot be counted as excluding one of those classes.

The result can overlap the earlier curvature/sector families. It supplies
a complete proof for this named patch regime and an explicit two-tree
algorithm. It does not provide a percentage of the whole shape space
covered or a new complete six-vertex combinatorial type.

## Replay the exact illustrations

```sh
python3 -m n6.one_patch n6/results/one-patch-A.certificate.json
python3 -m n6.one_patch n6/results/one-patch-B.certificate.json
python3 -m n6.polycert verify n6/results/one-patch-A.certificate.json --bits 240
python3 -m n6.polycert verify n6/results/one-patch-B.certificate.json --bits 240
```

The first two commands certify the hypotheses and sufficient cone tests.
The latter two independently check all 28 face pairs. Both candidates
happen to succeed on this example; the universal theorem only guarantees
at least one. The exact `half-fan-angle-limit` example shows that the
simpler two-original-angles test can fail in both orientations. Its outer
triangle cone tests still pass, as the separate `one-patch-angle-limit`
certificates verify. This distinguishes the proved rule from that stronger,
false shortcut.
