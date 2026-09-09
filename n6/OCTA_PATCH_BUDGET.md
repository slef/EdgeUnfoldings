# A shared lean budget: all two-patch cases and the mixed three-patch case

10 September 2026 JST / 9 September UTC. These are written geometric
proofs. **The full octahedron remains open.** The proofs allow exchanging
the two poles and do not settle the fixed sharpest-source four-choice rule.

## Result and remaining pattern

Choose a globally sharpest vertex v and its opposite w. Classify their
four flattened two-face patches as in [OCTA_CONVEX_PATCHES.md](OCTA_CONVEX_PATCHES.md).

**Theorem.** There is a nonoverlapping original-edge net if there are at
most two nonconvex patches. There is also such a net if there are three
nonconvex patches whose directions are mixed. One of the eight trees
obtained by cutting the four edges at either pole and one edge at the
other pole works.

For adjacent two-patch and mixed three-patch configurations, two prescribed
trees suffice, using the same equator endpoint for the fifth edge. For
opposite two-patch configurations the proof uses at most four prescribed
trees. The simpler eight-tree search contains all these choices.

The remaining pattern is **three consecutive nonconvex patches all leaning
in the same cyclic direction**. Reflection identifies all-forward and
all-backward. This is a real geometric family, not an empty formal case:
`sector-three-patch-radial-failure.certificate.json` is an exact example.
Its particular net is separately certified, but the whole family is open.

## One patch shares its reflex excess between the two poles

For a nonconvex Q_i let l_i^w be its angular extension beyond its W_i
triangle, viewed from w, and l_i^v the corresponding extension viewed
from the other pole after exchanging v,w. These are positive, strictly
less than pi. A convex patch has both extensions zero.

Let r_i>pi be the patch's reflex corner and c_i its other equator corner.
The outer triangle of the flattened patch has pole angles
omega_i+l_i^w and nu_i+l_i^v. Its third angle is c_i. Comparing its angle
sum with the quadrilateral's angle sum gives the exact identity

    l_i^w + l_i^v = r_i - pi =: rho_i.

Thus the two pole views divide the patch's reflex excess rho_i between
them. The two extensions are not independent.

## A total budget when no vertex has curvature above pi

Write L_w=sum_i l_i^w and L_v=sum_i l_i^v. Let R be the set of equator
vertices that are reflex corners of bad patches, and let m=|R|. These
corners are distinct: two patches cannot both be reflex at their common
vertex because its total face angle is strictly below 2*pi.

At each x in R, let a_x>0 be the corner of the other patch incident at x.
The complete face angle there is r_x+a_x=2*pi-kappa_x. Hence

    rho_x = pi - kappa_x - a_x.

Using the total curvature 4*pi of the octahedron, summation gives

    L_w + L_v
      = kappa_v + kappa_w
        + sum_(x not in R, x on equator) kappa_x
        - (4-m)*pi - sum_(x in R) a_x.

If the nonreflex equator vertices all have curvature at most pi, and
m>0, this proves

    L_w + L_v < kappa_v + kappa_w.

Consequently **one of the two poles has total extension smaller than its
fan gap**: L_w<kappa_w or L_v<kappa_v. This hypothesis is automatic when
the globally sharpest vertex has curvature below pi.

There is therefore a useful general choice under H. If some pole has
curvature at least pi, use it as fan center; each individual extension is
then below the gap. Otherwise use a pole whose total extension is below
its gap; again each individual extension is below the gap. In either case
we obtain a pole p with

    l_i^p < kappa_p for every bad patch.

The total-budget alternative is stronger than these individual bounds and
will also be used below. No numerical survey is part of this argument.
For one bad patch, this pole choice already proves its prescribed opening
by the one-patch row of the half-fan table. With no bad patches every
opening works by the disjoint convex wedges.

## Two adjacent bad patches: all three direction cases

Rotate the labels so the bad patches are Q0,Q1. Their possible directions
and fifth-edge endpoints are:

| Directions | Endpoint q |
| --- | --- |
| Forward, forward | u2 |
| Backward, backward | u0 |
| Backward, forward | u3 |

Forward, backward is impossible because both reflex corners would be u1.
Use the pole p supplied by the preceding choice as fan center, cut the
other pole's four edges, and cut p-q.

The substitutions in [OCTA_HALF_FAN.md](OCTA_HALF_FAN.md) only require
each nonzero extension to be at most the fan gap. They therefore prove
the entire net safe here, without the previous 180-degree restriction.
Reversing the ring when exchanging poles gives the same physical q in
each row. This proves the full adjacent-two-patch family under H.

## Two opposite bad patches pointing toward each other

Take Q0 forward and Q2 backward; they lean toward the intervening convex
patch Q1. (The other opposing-direction case is obtained by relabeling.)
Let t_p=l_0^p+l_2^p at each pole p. The full angles at the two vertices
u1,u2 on the intervening patch give

    rho_0 + rho_2 = omega_1 + nu_1 - kappa_(u1) - kappa_(u2).

For clarity, substitute rho_0=f_0-pi, rho_2=e_2-pi and
f_0+e_1=2*pi-kappa_(u1), f_1+e_2=2*pi-kappa_(u2), then use
omega_1+nu_1+e_1+f_1=2*pi. In particular,

    t_w + t_v < omega_1 + nu_1.

At least one pole therefore has t_p less than its angle on Q1. With the
opening at u0, the two bad patch cones are separated across Q1. Substitution
in the six wedge tests leaves just t_p<=angle_p(Q1); the other nonzero
flank bound is weaker. All other pairs are safe. Exchanging the poles
reverses the order but keeps the same physical opening u0 valid.

**This subfamily needs no H at all.** The reflection with the intervening
good patch Q3 is the same proof.

## Two opposite bad patches pointing in the same cyclic direction

Take Q0,Q2 both forward; both backward is the reflected case. Each bad
patch is followed by a convex patch. A useful individual identity is

    rho_i - (omega_(i+1)+nu_(i+1))
       = f_(i+1) - pi - kappa_(u_(i+1)) < 0,       i=0,2.

It follows by adding the two patch corner angles at u_(i+1), just as
above. Strictness holds because the following patch is convex and the
original vertex has positive curvature. Hence, if at one pole the
extension of Q_i is bigger than the next fan angle, at the other pole it
is smaller than that next fan angle.

First use the pole p where each extension is smaller than its fan gap.
If l_0^p<=angle_p(Q1), open at u0; if l_2^p<=angle_p(Q3), open at u2.
For example, the u0 opening requires l_0^p<=angle_p(Q1) and
l_2^p<=angle_p(Q3)+kappa_p, and the latter follows from the gap bound.
The u2 case is symmetric.

If neither comparison holds, switch to the other pole. The preceding
identity makes **both** comparisons hold there. Opening at u0 or u2 is
then safe even without a gap bound. This proves the same-direction
opposite-two-patch family under H. The four candidate trees use either
pole as fan center and q in {u0,u2}.

## Three bad patches with mixed directions

The three bad patches form a consecutive block; label them Q0,Q1,Q2,
with Q3 convex. The prohibition on a forward patch followed by a backward
one leaves BBB, BBF, BFF, FFF. Reflection exchanges BBF and BFF, so take
the mixed case BFF.

Use the opening q=u3. At a given fan pole p, let theta_i be that pole's
original face angle on Q_i and l_i its extensions. The six wedge tests
reduce to

    l_1 <= kappa_p + theta_2,
    l_0 + l_2 <= kappa_p + theta_3,
    l_2 <= kappa_p.

Exchanging the poles and reversing the cyclic labels gives the same
three conditions in the original physical patch indices. The following
bounds therefore treat both choices.

If the sharpest curvature is below pi, choose a pole with
l_0+l_1+l_2<kappa_p using the total budget. All three conditions follow.
If a pole has curvature at least pi, use that pole. The individual bounds
follow because every extension is below pi. For the middle condition,
Q0 and Q2 point toward each other across the convex Q3. The preceding
opposing-direction identity gives

    l_0^p+l_2^p <= rho_0+rho_2 < theta_3^p+theta_3^(other)
                       < theta_3^p+pi <= theta_3^p+kappa_p.

Thus all conditions hold in this case too. The BBF pattern is its
reflection. Both pole choices use the same physical endpoint u3, the
convex patch's endpoint that is reflex in Q2 in the BFF labeling.

## Proof status and scope

Four of the five coarse patch regimes under H now have complete
**existence** proofs: zero, one, two adjacent, and two opposite bad
patches. The fifth regime, three bad patches, is proved for mixed
directions; the common-direction case remains open.

These are not equal fractions of shape space, and the proof is not an
80-percent completion estimate. The original **fixed sharpest-source**
target remains 49 classes, 2 excluded and 47 open. Exchanging the source
does not exclude those fixed-source failure classes. The full six-vertex
theorem remains unproved.

Straight corners in the good patches and curvature exactly pi are
included. All other original convexity and nondegeneracy assumptions are
as in the previous patch proofs. The full-net conclusion comes from the
six sufficient angular tests plus shared-vertex separation; it never uses
the refuted conditional far-fan lemma.

## Exact replays

```sh
python3 -m n6.patch_budget n6/results/patch-budget-adjacent-family.certificate.json
python3 -m n6.patch_budget n6/results/patch-budget-opposite-same.certificate.json
python3 -m n6.patch_budget n6/results/patch-budget-opposite-facing.certificate.json
python3 -m n6.patch_budget n6/results/patch-budget-three-mixed.certificate.json
python3 -m n6.patch_budget n6/results/patch-budget-three-same.certificate.json --analyze
python3 -m n6.polycert verify n6/results/patch-budget-adjacent-family.certificate.json --bits 240
```

The family allows each of all 18 coordinates of its six vertices to vary
independently by 1/1000 in either direction. Both pole curvatures remain
below pi, with v globally sharpest. A single prescribed tree passes every
angular test and every independent face-pair check throughout this box.
The written theorem applies beyond this illustrative region.

The `--analyze` command for three common directions deliberately records
the regime as open, even though this example has a successful net. A
successful numerical search, a successful individual certificate, and a
complete family theorem are distinct conclusions.
