# The conditional far-fan reduction is false as stated

**11 September continuation:** the [new cut-side reduction](LEMMA_F_CUT_REDUCTION.md)
retains the two slit-side fan tests. Under H and R, their safety implies
opposite-petal safety; the valid interior-fan result below then finishes the
net. This is a different implication and does not restore the refuted claim.

9 September 2026, timed-session audit. **This is an exact counterexample to
an older supporting lemma, not to the sharpest-source unfolding rule.**
The new curvature, central-symmetry, and sector-family proofs do not use it.
A subsequent [two-pole proof](OCTA_ONE_PATCH.md) now settles the one-patch
existence family under H; it allows the four cuts to move to the other
pole and does not restore the older fixed-source claim.

## What the old argument claimed

In a four-slit net, suppose the three face pairs beside the slit do not
overlap. The draft then claimed that a petal meeting a far fan triangle
must meet the petal attached to that triangle. That would reduce the nine
unresolved face pairs to three local and two opposite-petal pairs.

The first step is valid: a petal cannot properly cross an **interior** radial
hinge when local pairs are clear. The next step overlooked a boundary edge.
The first and last fan triangles each have a radial edge at the slit, which
is cut, not an interior hinge. A petal can enter through that edge. The
interior-hinge argument does not stop it.

## A small integer-coordinate witness

Use v=0, w=1, and equator u0=2,u1=3,u2=4,u3=5:

    v =(    0,   0,    0)    w =(  -89,-179, 150)
    u0=( -595, 494, -131)    u1=(  295,-283,  90)
    u2=(-7440,5883,-1376)    u3=(-1166, 992,-271).

The original faces are W_i=w u_i u_(i+1) and V_i=v u_(i+1) u_i. Cut the
four edges at v and the edge w u0. Rational interval verification proves:

- All eight listed triangles are strictly supporting facets of the convex
  octahedron.
- **V2 overlaps W0 with positive area.**
- **All other 27 face pairs are nonoverlapping.** In particular, all three
  local pairs and both opposite-petal pairs are clear.
- Vertex u2 is strictly sharper than the selected source v. Thus this
  witness does **not** satisfy H.

The source has about 8 degrees of curvature; a different vertex has about
356 degrees. Those rounded values are explanatory only. Exact signs verify
the strict curvature ordering, the overlap, and the safe pairs.

A second certificate uses four cuts at the sharper vertex and a different
fifth edge. It proves a successful original-edge net for this same solid.

```sh
python3 -m n6.hinge_audit n6/results/hinge-boundary-counterexample.certificate.json
python3 -m n6.polycert verify n6/results/hinge-boundary-alternative.certificate.json --bits 240
```

## What must be corrected

The unrestricted conditional lemma is refuted. A version that additionally
assumes H is still possible, but the old proof does not establish it.

1. **Restore the original 49-class sufficient target.** The 24-class list
   depended on the false lemma. Keep it as a historical hypothetical list,
   not a proved reduction. Original classes 20 and 49 are independently
   excluded, so the current rigorous count is **2 excluded, 47 open**.
2. **Reopen the one-nonconvex-patch whole-net claim.** Its two candidate
   openings do make all local pairs safe, and one makes both opposite-petal
   pairs safe under H. The final far-fan step is no longer justified. The
   displayed individual example still has its independent full-net proof.
3. **Keep the independent results.** Every all-convex-patch net works; at
   least one strictly convex patch always exists; the two switching
   implications remain proved. The curvature-pair, centrally symmetric,
   short-edge-cover, and mixed radial-cover theorems are unaffected.

The higher remaining-class count is an audit correction, not a claim that
new shapes became harder. It avoids counting a missing proof as completed.

The numerical audit first found this example. Its verdict comes from the
independent rational replay, not the sample. Two earlier optimization runs
failed to find it, illustrating why unsuccessful searches are not proofs.

## What survives: the two interior fan triangles

**Restricted lemma.** Assume the three local pairs are nonoverlapping.
If a petal overlaps a different, interior fan triangle (one with both radial
edges uncut), it also overlaps the petal attached to that triangle. No
curvature ranking is required.

**Proof.** Write P for the entering petal, W for the interior fan triangle,
and V for W's own petal. Suppose P and V have disjoint interiors. The interior
of P cannot meet either open radial edge of W: a small disk about such a
point would enter both adjacent fan faces, contrary to the surviving
interior-hinge lemma. Nor can the interior of P meet the relative interior
of W's equator edge, since that would enter V on its other side.

P has interior points outside W. Indeed, its own equator edge belongs to a
different fan triangle; the midpoint of that edge lies strictly inside that
triangle's angular wedge, disjoint from W's wedge. Nearby interior points of
P remain outside W. If P also had an interior point inside W, a generic
segment between the two points, lying entirely inside P, would cross the
relative interior of one of W's three edges. Choose the segment to avoid
the three vertices of W. Every such crossing was just excluded, a
contradiction. Thus P and W cannot overlap without P and V overlapping.

For a slit at w-u0, the interior fan triangles are W1 and W2. Of the four
residual petal/far-fan pairs, the lemma treats V3/W1 and V0/W2; their
corresponding opposite-petal pairs are V3/V1 and V0/V2. The other two pairs,
V2/W0 and V1/W3, target the slit-side triangles. The exact counterexample
uses the first of these and therefore respects the restricted lemma.

Consequently, after local and opposite-petal safety are known, **only the
two slit-side far-fan pairs remain**. This is a conditional geometric
reduction. It neither proves those last two pairs nor changes the current
conservative count of 47 open original failure classes.

The audit also caught a numerical replay bug: saved tree pairs become lists
in JSON, whereas the batch mask expected tuples. The mask now normalizes
them. Exact certificate checkers were unaffected; a regression reproduces
this real overlapping example before and after a JSON round trip.
