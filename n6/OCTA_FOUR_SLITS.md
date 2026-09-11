# Octahedron priority: a four-choice unfolding rule

**Subsequent completion, 11 September:** [the equal-length argument](LEMMA_F_CHORD.md)
completes the selected H/R octahedron proof. Earlier open-case counts in this
note describe the investigation at that stage. The every-slit Lemma F and
full n=6 theorem remain open; the new research proof awaits independent review.


9 September 2026. **The rule is conjectural.** The [overlap case analysis](OCTA_CASE_ANALYSIS.md)
now proves two switching implications: moving the opening repairs the old
local pairs, and opposite petals cannot overlap along both routes under H.
The sufficient class list reduces from 49 to 24; original class 49 is then
excluded, leaving 23. The initial enumeration and pilot below are retained.

This note gives a finite
combinatorial reduction and a numerical comparison, not a proof of the
octahedron case. The existing two gaps in the sharper H/R rule remain open.

## The proposed algorithm

Let the polyhedron be a strictly convex realization of the octahedral graph;
its eight original facets are triangles. It need not be regular, symmetric,
or have a planar equator.

1. Choose a vertex **v with maximum angle deficit** (curvature). If tied,
   choose any maximum. Let w be the unique vertex not joined to v by an edge.
2. Cut the four edges incident to v.
3. For each of the four neighbors u of w, also cut wu, develop the surface,
   and check for overlap. Return a nonoverlapping choice if one exists.

Every candidate cuts five original edges forming a spanning tree. The four
triangles incident to w become an open fan; each has a triangular petal at v
attached to its outside edge. The only choice is where to put the opening
in that fan. Boundary touching is allowed.

**Conjecture (four-slit lemma).** For every such polyhedron and every vertex v
of maximum curvature, at least one of these four developments is
nonoverlapping.

The four nets are already present among the repository's 24 near-stars; no
new unfolding construction is being claimed. The new focus is to prove a
statement about the choices together. The earlier H/R conjecture specifically
selects the highest-curvature neighbor as u. It implies this four-choice
conjecture; the converse is not required. Dropping that extra commitment can
make the proof easier. A proof must still include curvature ties and touching
boundaries, and use a justified limit argument if extending to merged facets.

For a concrete input, a successful exact all-pairs certificate proves that
particular output is a net. What remains unproved is that the algorithm will
always have an output. Floating-point success is not an exact certificate.

## Why changing the slit is a useful proof operation

Keep the four patches Q_i = W_i union V_i in cyclic order. Moving the opening
past one patch moves it from one end of the opened fan to the other. After
aligning the other three patches, that patch is rotated about w by the deficit
at w, with sign depending on the direction of the move. Thus the four nets
are strongly correlated; they are not four unrelated searches.

The possible lemma is: **bad relative placements cannot obstruct all four
positions of the opening at once when v has maximum curvature.** This is
weaker than requiring every troublesome pair to be safe at the one prescribed
H/R slit. It suggests studying simultaneous failures, as for the minus-edge
two-choice rule, and seeking inequalities that exclude many at once.

Pure angular separation is insufficient. The exactly checked
[local radial example](LEMMA_L.md) has two disjoint faces visible on some of
the same rays from w: one is farther away. The same lengths and convexity
constraints must be retained across all four developments. Independent
angle assignments that fail global metric closure are not octahedra.

## An exhaustive finite target, not a percentage complete

Use canonical labels v=0, w=1, u_i=i+2. Face numbers 0..3 denote W_i and
4..7 denote V_i. Each slit has 28 face pairs. The shared-vertex fan lemma
settles 19; nine remain. Across four slits that gives 36 listed checks.

The relative placement of a pair is fixed by the unique path of uncut
hinges between its faces. If that same path occurs in two nets, the overlap
question is identical, up to a plane isometry. Identifying equal paths reduces
the 36 checks to **24 distinct relative placements**:

- 12 placements each occur in one slit choice.
- 12 placements each occur in two slit choices.

For all four nets to fail, the bad placements must cover all four slit
choices. Every such cover contains an inclusion-minimal cover with at most
four events: select one actual bad pair from each net, then discard redundant
events. Exhaustive enumeration gives:

| Bad placements in a minimal cover | Labeled covers | Classes under ring symmetry |
| --- | ---: | ---: |
| 2 | 18 | 4 |
| 3 | 216 | 30 |
| 4 | 81 | 15 |
| **Total** | **315** | **49** |

The eight rotations/reflections of the ring fix v and w, preserve the
maximum-curvature hypothesis, and identify equivalent geometric questions.
[The complete enumeration](results/octa-four-slit-obligations.json) records
every event's hinge path, the slit choices it obstructs, and the 49 class
representatives with orbit sizes. An independent test also starts from the
9^4 choices of one failed pair per net and recovers the same minimal covers.

This is a valid combinatorial reduction of the conjecture: excluding all 49
classes for convex realizations with v of maximum curvature would prove it.
**Initially no class in this list had been excluded geometrically.** The
[follow-up proof](OCTA_CASE_ANALYSIS.md) excludes class 49, and convex-patch
existence excludes class 20, leaving **47 open out of 49**. The former
24-class reduction is withdrawn after [HINGE_AUDIT.md](HINGE_AUDIT.md). These are alternative obligations, not 49 additional gaps appended
to the two gaps in the earlier single-choice strategy. There is no justified
percentage of the octahedron theorem completed.

The initial focused target was the **four classes requiring only two bad
placements**. They have the fewest simultaneous inequalities. If feasible
candidates appear, validate the original convex geometry and audit the
claimed overlaps exactly before drawing a conclusion. An exact failure of
this rule would still leave other cut trees available.

Their canonical representatives are below. A path lists the hinges that fix
the relative positions of its first and last face; the two listed overlaps
would have to happen together. The left event obstructs slits u_0 and u_3,
and the right event obstructs slits u_1 and u_2.

| Class in the saved list | First overlap, along this path | Second overlap, along this path |
| --- | --- | --- |
| 37 | W0—W1—W2—V2 | W0—W3—W2—V2 |
| 40 | W0—W1—W2—V2 | W2—W3—W0—V0 |
| 44 | W0—W1—W2—V2 | V0—W0—W3—W2—V2 |
| 49 | V0—W0—W1—W2—V2 | V0—W0—W3—W2—V2 |

For example, class 49 asks whether the same two opposite petals can overlap
both when connected around one side of the fan and when connected around the
other. That simultaneous event is now excluded by the complementary angle
sums. This settles just that class, not the complete four-choice rule.

## Initial comparison

[The reproducible pilot](results/octa-patterns.json) uses seed 6090931 and
3,000 accepted octahedra from Claude's existing generator: Gaussian points,
points on a sphere, cube samples, or one distant point, followed by anisotropic
scaling and strict facet screening. The four families below were evaluated
on the same inputs, using all 24 near-stars as a reference.

| Candidate rule | Shapes with a numerically clear choice | Minimum clear choices |
| --- | ---: | ---: |
| Existing sharpest-v, sharpest-u rule: 1 tree | 3,000 / 3,000 | 1 |
| Sharpest-v, try all four slits: 4 trees | 3,000 / 3,000 | 2 |
| Sharpest-v, two endpoints of a shortest antipodal path's crossing edge: 2 trees | 3,000 / 3,000 | 1 |
| Both orientations of that opposite pair: 8 trees | 3,000 / 3,000 | 3 |

Across all 24 near-stars the minimum was 15 numerically clear choices. These
samples contain substantial freedom of choice, supporting the search for an
existence lemma. They do **not** establish a universal lower bound, rule out
rare simultaneous failures, or certify even the sampled outputs exactly.
Every diameter is normalized to one and the numerical separation threshold
is 1e-10. The report distinguishes clear, borderline, and failed candidates.

The batch implementation was generalized from the minus-edge investigation,
rather than introducing a third development engine. Tests compare all 384
octahedral cut trees on two fixtures against the independent existing
development and separation implementation. The original minus-edge batch
comparison also still passes.

## A second route with an existing sufficient theorem

The archive's [geodesic-sector argument](GEODESIC_SECTOR.md) supplies a useful
bridge from the proved shortest-path star unfolding to an edge unfolding.
A shortest path from v to its opposite vertex w crosses a single equator
edge a-b through two faces. At an endpoint u of that edge, let L be the path
length, r=|wu|, and gamma the angle between the path and wu at w in the
two-face development. The existing sufficient conditions are

    r <= L,    gamma <= curvature(w).

Under these conditions one can replace the last geodesic cut by the original
edge wu; the moved triangle stays in a known empty sector. The unresolved
step is existence of an oriented opposite pair and endpoint passing both
conditions. This could prove a small-choice algorithm without excluding
overlaps individually.

**Do not fix w to be the sharpest vertex.** Although that choice passed the
sufficient conditions throughout this pilot, an earlier
[exact counterexample](results/sector-sharpest-radial-failure.verification.json)
proves that its radial condition can fail at every neighbor of that w. The
regression test retains that obstruction. Allowing other opposite pairs
remains worth investigating; the pilot found some eligible choice in every
sample. Again, this is numerical evidence only.

Pinciu's face-neighborhood theorem, which removed seven minus-edge classes,
does not immediately add new exclusions here: two edge-neighbors of a
triangular base share a vertex with that base, so these direct cases are
already among the 19 shared-vertex exclusions.

## Reproduction

From the repository root:

```sh
durer_small_n/.venv/bin/python -m n6.octa_patterns --samples 3000 --seed 6090931
durer_small_n/.venv/bin/python -m n6.octa_patterns --obligations --output n6/results/octa-four-slit-obligations.json
durer_small_n/.venv/bin/python -m unittest n6.tests.test_octa_patterns
```
