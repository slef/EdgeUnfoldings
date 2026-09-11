# Lemma L: a curvature gate separates the two local overlap routes

10 September 2026 JST / 9 September UTC. **Subsequent completion:** [LEMMA_L_PROOF.md](LEMMA_L_PROOF.md) now proves
the general Lemma L. This earlier gate theorem remains valid. The results below are geometric proofs about the three local face
pairs. They do not establish a whole net or the full octahedron theorem.
Unlike L's proposed selection rule, these proofs require neither the source
nor the slit vertex to have maximum curvature.

## The two routes and the result

Work with a nondegenerate convex octahedron with six actual vertices and
eight triangular faces. All face angles and vertex curvatures are positive.
Cut the four edges at a pole v and one edge w-u0 from its opposite w.
Label the fan counterclockwise W0,W1,W2,W3. Let Q0 and Q3 be its first and
last two-face patches, with their attached petals V0 and V3. The local pairs
are V0/V3, V0/W3, and V3/W0.

Write

    sigma = kappa_(u0) + kappa_w.

Each patch is contained in its angular cone about w. Those two cones
could meet by either of two circular routes: across the slit gap, or
through the intervening fan wedges W1,W2.
Here meeting of cones refers to their directions, not their shared apex w.
The cones have width less than pi: each flattened patch is a simple union
of triangles on opposite sides of their common base, with a convex corner
at w. Its only possible reflex corner is at one equator endpoint.

**Curvature-gate theorem.**

- If sigma<=pi, the cones cannot meet through the intervening fan wedges.
- If sigma>=pi, the cones cannot meet across the slit gap.
- Consequently, if sigma=pi, all three local pairs are nonoverlapping.

In particular both angular-overlap routes can never be active at once.
A cone intersection is only a necessary condition for face overlap. Each
strict half still requires a further geometric argument in the cases left
below; this gate theorem alone is not a proof of L in either entire half.
The subsequent complete proof supplies the remaining geometric arguments.

## The across-slit bound

Use e_i for the patch angle at u_i, and f_i for that at u_(i+1).
At the slit vertex,

    e_0 + f_3 = 2*pi-kappa_(u0).

Let B0 be Q0's backward extension beyond its slit ray, and F3 be Q3's
forward extension beyond the other slit ray. An extension is positive
only when the corresponding corner at the slit is reflex. At most one of
B0,F3 can be positive, since e_0+f_3<2*pi.

For a positive extension, the shared-excess identity from
[OCTA_PATCH_BUDGET.md](OCTA_PATCH_BUDGET.md) gives

    B0 < e_0-pi,   or   F3 < f_3-pi.

The other corner angle is positive. Therefore, when B0+F3>0,

    B0+F3 < pi-kappa_(u0).

If sigma>=pi this is strictly below kappa_w, the fan gap. When B0+F3=0
it is also below that positive gap. Thus no across-slit cone intersection
is possible. This recovers the previously proved gap bound in
[LEMMA_L.md](LEMMA_L.md).

## The new bound through the fan

The extensions toward the fan interior are F0 for Q0 and B3 for Q3.
Let omega_i and nu_i be the original face angles at w and v. The cones
are separated through the fan precisely when

    F0+B3 <= omega_1+omega_2.

If F0+B3=0, this holds strictly. Suppose F0+B3>0. Let F0^v,B3^v denote
the corresponding extensions toward that same side of each physical patch
when viewed from the other pole. We only use the two patches separately;
we do not identify their different developed copies of v.

For the first patch,

    (omega_0+F0) + (nu_0+F0^v)
       = pi-e_0 + max(pi-f_0, 0).

If f_0>pi, its two extensions sum to f_0-pi, and the identity follows
from the patch's 2*pi angle sum. If f_0<=pi, both extensions on this side
are zero and the same identity follows directly. This includes a straight
corner f_0=pi. Similarly, for the last patch,

    (omega_3+B3) + (nu_3+B3^v)
       = pi-f_3 + max(pi-e_3, 0).

Set

    Cw = omega_0+omega_3+F0+B3,
    Cv = nu_0+nu_3+F0^v+B3^v > 0,
    D  = max(pi-f_0,0) + max(pi-e_3,0).

Adding gives the exact identity

    Cw + Cv = kappa_(u0) + D.

Since F0+B3>0, at least one of f_0,e_3 exceeds pi, so at least one term
in D is zero. The other is strictly less than pi because the original
corner is positive. Hence D<pi. The gap through the fan is therefore

    omega_1+omega_2-F0-B3
       = 2*pi-sigma-D+Cv
       > pi-sigma.

If sigma<=pi, this gap is strictly positive. This proves the first part
of the theorem, including its equality boundary. The two parts together
prove the third part. Within each patch the two triangles lie on opposite
sides of their common edge; disjoint patch cones exclude all three local
face-pair overlaps. The cut-side fan faces are explicitly included.

## Additional local families that now follow

These are universal local-separation statements with explicit hypotheses.

1. If sigma<=pi and neither corner at the slit is reflex, all three local
   pairs are safe. There is no extension across the slit, and the theorem
   excludes the other route.
2. If sigma>=pi and neither flank extends toward the fan interior, all
   three local pairs are safe. The complementary argument applies.
3. If both flank patches have their inward corners *away* from the slit,
   and sigma<=2*pi, all three local pairs are safe. In this case D=0, so
   the through-fan gap is 2*pi-sigma+Cv>0, while B0=F3=0.

The third statement includes sigma=2*pi. These families may overlap other
proofs. They are not whole additional universal obligations in L's original
three-pair count.

## A further reduction in the small-sum half

Suppose sigma<pi. If no patch is inward at the slit, item 1 settles L.
Otherwise exactly one of the two patches is inward at its slit corner.
Every remaining possible local overlap involves that patch's petal:

| Slit corner that is inward | Local pairs still needing work | Pair already safe |
| --- | --- | --- |
| First patch Q0 at u0 | V0/V3 and V0/W3 | V3/W0 |
| Last patch Q3 at u0 | V0/V3 and V3/W0 | V0/W3 |

For example, in the first row only Q0 extends across the gap. Q3's cone
cannot enter W0 across the slit, and the new theorem excludes entry by the
other route. Thus V3/W0 is safe. The reflected row is identical.

This supplies a precise distance-sensitive target: in the small-sum half,
handle one offending petal against the other patch. It must include both
the other petal and the other fan face, not just one of them.

## Relation to the three-patch investigation and to the older radial example

For three common-direction patches, the equator vertex with no inward
corner is the maximum of |vu_i|+|wu_i|. Opening there produces no extension
across the slit. If its curvature plus kappa_w is at most pi, item 1 proves
all three local pairs for that opening. This does not settle the remaining
opposite-petal and far-fan checks.

The old `three-chain-uncovered` solid satisfies these hypotheses at its
maximum-curvature equator vertex u3. `local-gate-three-chain` uses that
slit and also has an independent certificate for its entire particular net.
The middle-patch sufficient condition failing elsewhere was never a failure
of Lemma L at this selected slit.

The `local-gate-radial-family` box is centered on the older
`local-radial-failure` example. It keeps both maximum-curvature selections,
sigma<pi, and one inward slit corner. The new theorem removes the through-fan
route and one of the mixed pairs. Exact radial clipping separately proves
that the offending petal is at least 6/5 as far from w as the opposite fan
edge on every shared ray. The other local pair and the rest of the net have
independent separating-edge/vertex-fan certificates. This is a proof for an
explicit coordinate region, not a universal radial inequality.

## Scope and replay

The gate theorem by itself settled the boundary and explicit corner families.
At that stage the general count was 0/3 local pair obligations. The subsequent
[complete proof](LEMMA_L_PROOF.md) closes both strict halves and changes the
current count to **3/3**. This is separate from the unrecounted four-opening
failure-class enumeration and does not settle the full octahedron.

```sh
python3 -m n6.local_gate n6/results/local-gate-three-chain.certificate.json
python3 -m n6.local_gate n6/results/local-gate-radial-family.certificate.json --analyze
python3 -m n6.local_radial n6/results/local-gate-radial-family.certificate.json --bits 240
python3 -m n6.polycert verify n6/results/local-gate-radial-family.certificate.json --bits 240
python3 -m n6.local_gate_examples
```

These exact commands use the standard library. The theorem comes from the
identities above. Numerical searches used to investigate possible extensions
are not proofs and do not establish that a remaining branch is empty.
