# Assume an overlap, then change the opening

9 September 2026. This develops the user's proposed case analysis. It proves
two switching statements, using the existing shared-vertex, Case A, and
base-cone lemmas. **The four-choice unfolding rule and the octahedron case
remain open.**

## Start with an actual failed choice

Choose a maximum-curvature vertex v, its nonneighbor w, and an opening wu_k.
Write Z_k for the resulting net. The four other vertices u_0,...,u_3 have
their cyclic order, with W_i=w u_i u_{i+1} and V_i=v u_i u_{i+1}.

If desired, first choose u_k of maximum equator curvature, retaining both
old hypotheses H and R. Only H remains guaranteed after changing the opening.
No argument using R may silently be reused at the new opening.

Nineteen of the 28 face pairs are already separated by a common uncut vertex.
Every positive-area overlap must therefore be one of:

| Kind | Number of pairs | Existing lemma |
| --- | ---: | --- |
| Across the opening: adjacent petals, or a petal and the fan face on the other side | 3 | L |
| Two opposite petals | 2 | Part of F |
| A petal and the far fan triangle | 4 | Rest of F |

First branch on whether any local pair overlaps. If none does, the existing
conditional hinge/far-fan lemma implies that any far-fan overlap forces an
opposite-petal overlap. This uses **local nonoverlap of this particular net**,
not the unproved universal assertion of Lemma L. It is not circular.

Thus a failed net can be diagnosed by five tests: three local, two opposite.
After reflection about the opening there are three basic pictures: adjacent
petals across the opening; petal/fan across the opening; opposite petals.

## Proved switching statement 1: the old local pairs are repaired

**For any convex octahedron, moving the opening from wu_k to any wu_l with
l different from k makes all three old local pairs nonoverlapping.**

Proof. Rejoining wu_k identifies the two copies of u_k. The faces
V_{k-1}, W_{k-1}, W_k, V_k now form one connected fan about that copy.
Their total angle is 2*pi-curvature(u_k), strictly below 2*pi. Their wedges
have disjoint interiors, so every pair in this fan is nonoverlapping.
This includes all three formerly local pairs. The claim does not even need
v to be sharpest.

This repairs the identified obstruction, **not necessarily the whole net**.
New local pairs occur at u_l, and an opposite-petal arrangement can change.
Repeatedly repairing one pair without tracking the other pairs could cycle.

## Proved switching statement 2: opposite petals cannot fail on both routes

Let S_j be the fan-angle sum used in the existing opposite-petal partition
for the triple W_{j-1}, W_j, W_{j+1}. Explicitly, it is the sum of these four
angles at the two endpoints of the middle base edge:

    angle at u_j in W_{j-1} + angle at u_j in W_j
      + angle at u_{j+1} in W_j + angle at u_{j+1} in W_{j+1}.

The [existing Case A and base-cone proofs](CASE_PARTITION.md), together, say:

    Under H, opposite-petal overlap along this route implies S_j < pi.

Case A excludes alpha+beta<pi under H. In the complementary range the
base-cone lemma excludes S_j>=pi. Hence all equality cases are included.

The two opposite petals V_{j-1} and V_{j+1} can instead be connected through
W_{j+2}. The key identity is

    S_j + S_{j+2} = 2*pi + curvature(w) > 2*pi.

Proof of the identity. In this sum each of the eight equator angles of the
four W triangles appears exactly once. Those triangles have total angle
4*pi. Their angles at w sum to 2*pi-curvature(w). Subtracting gives the
displayed identity. No regularity or planar-equator assumption is used.

Therefore if the first route overlaps, S_j<pi forces
S_{j+2}>pi+curvature(w)>pi. The established partition makes the **same two
petals disjoint along the other route**. They cannot overlap on both routes.
This is a universal implication under H, not an observation from samples.

It excludes **original class 49** of the four-slit enumeration: that class
requires V0 and V2 to overlap along both W0-W1-W2 and W0-W3-W2.

## A useful consequence, with a remaining local problem

At least one of S_0,S_2 is greater than pi, and at least one of S_1,S_3 is
greater than pi. Select one from each pair. The selected indices are adjacent
on the four-cycle. Thus there is always an opening k for which both
S_{k+1} and S_{k+2} are at least pi. Both opposite-petal pairs in that net
are disjoint under H.

This does **not** prove that its local pairs are disjoint. Nor may we conclude
all four far-fan pairs are safe before checking the local pairs: the hinge
reduction depends on them. A numerical test on the same 3,000 pilot shapes
found 11 apparent failures when choices were restricted to these angle-safe
openings. Those failures have not been exactly audited. They caution against
committing to this stronger selector; they do not weaken the proved
opposite-petal switching implication.

## How the obligations change

The [initial count](OCTA_FOUR_SLITS.md) retained all nine residual pairs per
net: 36 checks, 24 distinct placements, 315 minimal covers, 49 symmetry classes.
Using the conditional hinge reduction *inside the no-local-overlap branch*
leaves five possible failure witnesses per net. They give:

| Measure | Revised target |
| --- | ---: |
| Listed checks across four nets | 20 |
| Distinct relative placements | 16 |
| Minimal covers of all four openings | 131 |
| Symmetry classes sufficient for the proof | 24 |
| Excluded by opposite-route switching | 1 (original class 49) |
| Remaining classes | **23** |

The change from 49 to 24 removes redundant proof obligations; it does **not**
mean 25 configurations were geometrically ruled out. The additional change
from 24 to 23 is a genuine geometric exclusion. Eight remaining classes mix
local and opposite-petal failures; fifteen use only local failures. The
original class numbers and the earlier enumeration are retained.

## Relation to the original L and F program

- L aims to prove the three local pairs safe at the prescribed sharpest-
  neighbor opening. It remains unproved.
- F aims to prove all six far pairs safe; its original formulation asks for
  this in every opening under H. Its opposite-petal proof has the small-angle
  branch open, and the far-fan reduction uses local nonoverlap.
- The switching approach asks for less: **one opening where local and
  opposite-petal pairs are both safe**. The hinge lemma then settles the
  other far pairs. It can tolerate a failure of the stronger L/F prescriptions.

The next target is the mixed case: a local repair changes the two
opposite-petal routes, while an opposite-petal repair changes which local
pairs sit at the opening. Use the new implications to rule out a complete
cycle of failures. The 23 remaining classes make that task explicit; none of
those remaining classes has yet been excluded.

## Checks and reproduction

[The saved analysis](results/octa-failure-analysis.json) checks all 36
local-pair repairs by their common uncut vertex paths, records both exact
angle-sum identities, and preserves the original class numbers. It relies
on the stated mathematical lemmas; it is not a formal verification of their
proofs. Independent product enumeration of the 5^4 choices of one failed pair
per net reproduces the 131 minimal covers. Existing tests retain the separate
9^4 enumeration and the original 49 classes.

```sh
durer_small_n/.venv/bin/python -m n6.octa_patterns --case-analysis --output n6/results/octa-failure-analysis.json
durer_small_n/.venv/bin/python -m n6.octa_patterns --samples 3000 --seed 6090931 --output n6/results/octa-patterns-fan-rule.json
durer_small_n/.venv/bin/python -m unittest n6.tests.test_octa_patterns
```
