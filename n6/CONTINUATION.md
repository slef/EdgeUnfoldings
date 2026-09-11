# Current continuation: Lemma F reduced to two cut-side fan checks

11 September 2026 JST. [LEMMA_F_CUT_REDUCTION.md](LEMMA_F_CUT_REDUCTION.md)
proves a new reduction under H and R. In Z_k retain V_(k+2)/W_k and
V_(k+1)/W_(k-1). If these two pairs are safe, the whole net is safe.
Opposite petals are now consequences of the retained checks, then the
surviving interior-fan reduction disposes of the two interior targets.

For the last triple, put a=u_i, b=the last slit copy, and p inside a
hypothetical opposite-petal overlap. Gamma=a,p,b,w,a is simple: the retained
cut-side check excludes ap/bw crossing and L excludes bp/wa crossing.
All four vertices are below the middle base, even if a or b passes X.
The inside must face the fourth patch; otherwise the above-base middle
petal would be inside a below-base curve. Shared vertices and L put the
whole fourth patch inside. Remove it to get the historical hexagon.
Its angle sum requires nu_m>kappa_back, contradicting R plus the cone bound.
Reflection supplies the other opposite pair without changing the slit.

The same proof settles the small-angle case when the slit-side far vertex
is at or before X: the other outer edge separates the blue-orange pair.
Unlike the historical two-apex lemma, the nonslit far vertex may pass X.
The slit-side-past-X branch remains open; this position is necessary for
failure of that sufficient test, not sufficient for overlap. The two fan
checks also need study outside the small-angle branch.

Next: prove these two actual blue-orange checks, possibly by controlling
entry across their cut radial edge. Do not return to individual-apex
exclusion (refuted), nor assume an interior-hinge argument applies at a cut.
The universal pair count stays 22/28, the 49-class record stays 2/47, and the
full octahedron and n=6 remain open. Original Lemma F asks for all slits under
H; the new reduction uses the selected slit under H and R.

`n6/far_pairs.py` checks H/R, the hull/cuts, and precisely two exact edge
separators. Four saved examples, including 11- and 18-coordinate boxes,
agree with independent all-28 certificates. The geometric reduction is a
written proof dependency, not a numerical inference or formal verification.

# Previous continuation: Lemma L is proved

11 September 2026 JST. [LEMMA_L_PROOF.md](LEMMA_L_PROOF.md) is a complete
geometric proof of all three local pairs. It needs only kappa_v>=kappa_w
and a maximum-curvature equator slit, so it includes the original hypotheses.
The full octahedron and n=6 remain open; **do not claim a whole net from L**.

First, [LEMMA_L_SMALL_SUM.md](LEMMA_L_SMALL_SUM.md) closed the entire
sigma<=pi branch. If one petal reaches across the slit, extend its cut edge
vu. The slit ranking gives 2*kappa_u+kappa_w>pi; the other u copy and its
whole patch lie strictly on the other side of the line. This handles both
remaining pairs at once, including the older radial obstruction.

The missing through-fan route is now excluded for every slit under the pole
curvature comparison. The spherical link at a pole is a convex polygon with
perimeter equal to its total face angle; the direction of the other pole is
strictly interior. Boundary paths bound the distance from the slit direction
to that interior direction. For the original triangle wuv, if its angle beta
at v is nonobtuse, flattening an inward-away patch increases the pole distance
and decreases its angle at w. The link bounds then separate one or both
extending flanks. If beta is obtuse, the link at v forces kappa_v<pi, hence
kappa_w<pi. The fan spans more than pi while each extending patch subtends
less than pi/2, again giving separation. The proof includes all equalities.

Current status: **3/3 universal local obligations; 22/28 pairs of the selected
net safe**. The remaining two universal objectives are the opposite-petal
small-angle branch and the cut-side far-fan pairs. Once opposite-petal safety
is proved at this same slit, the interior-fan reduction is applicable.
The unrecounted 49-class four-opening enumeration stays a separate conservative
2-excluded/47-open record. Four of five whole patch regimes remain settled.

Next: work on Lemma F at the maximum-curvature slit, where L is now available.
Do not silently carry the slit ranking to an angle-safe opening chosen by the
switching theorem; the openings need not coincide. Do not revive the refuted
unrestricted far-fan reduction. Numerical searches are not proof premises.

Exact hypothesis checks: `python3 -m n6.local_lemma CERTIFICATE`. The saved
large-sum and radial-family reports illustrate the complete theorem. The
small-sum separator is independently checked by `python3 -m n6.local_small_sum
CERTIFICATE --cut-separator`. The webpage includes the full case table and
preserves the earlier radial picture and proof history.

# Previous continuation: direct progress on Lemma L

10 September 2026 JST / 9 September UTC.
[LEMMA_L_CURVATURE_GATE.md](LEMMA_L_CURVATURE_GATE.md) proves a new local
case split without either curvature ranking. Set sigma=kappa_u+kappa_w
at the slit. If sigma<=pi, the first and last patch cones cannot meet
through the intervening fan. If sigma>=pi they cannot meet across the slit.
At equality all three local pairs are safe. The proof adds the two pole
views of each flank patch, using their shared reflex excess; it includes
straight patch corners and the equality boundary.

Further local families follow: no inward slit corner in the small-sum
half; no extension toward the fan interior in the large-sum half; or both
flanks inward away from the slit with sigma<=2*pi. If sigma<pi and a slit
corner is inward, only its petal against the other petal and other fan face
remain. The other mixed pair is proved safe. This narrows the distance
problem to one petal against the opposite patch, but does not solve it.

The old three-chain-uncovered shape has all three local pairs proved at
the maximum-curvature equator slit; this is a different fifth cut from its
previous illustration. The saved point also passes an independent all-pairs
certificate. A second point illustrates the both-away family with pi<sigma<2*pi.

The exact radial example now has an 18-coordinate box: independently vary
every coordinate by ±1/10000. Both maximum-curvature selections and angular
intrusion persist. Radial clipping proves a distance ratio of at least 6/5
against the opposite fan edge on every shared ray, and separate certificates
prove all 28 face pairs safe. This is a certified coordinate family, not a
universal radial inequality. Rebuild with `python3 -m n6.local_gate_examples`.

Next: in sigma<pi, prove simultaneous distance separation of the offending
petal from both faces of the other patch, using H and the slit ranking.
Treat the through-fan route separately for sigma>pi. The gate does not use
those rankings, so they remain extra information for this next step.

The full Lemma L, octahedron, and n=6 remain open. Counts stay 0/3 universal
local obligations, 4/5 complete patch regimes, and 2 excluded / 47 open
fixed-source classes. The proof is geometric; numerical searches and linear
angle relaxations are not used as proofs or as geometric counterexamples.

# Previous continuation: a middle-patch switch proves three-chain subfamilies

10 September 2026 JST / 9 September UTC. [OCTA_THREE_CHAIN.md](OCTA_THREE_CHAIN.md)
proves an original-edge unfolding under H for three bad patches with a
common direction when the middle patch satisfies explicit angle bounds.
For forward Q0,Q1,Q2, try both four-cut poles and fifth endpoints u2,u3.

The simple condition is rho_1<=min(kappa_v,kappa_w). The stronger version
requires the middle extension at each pole to fit that pole's gap, and
rho_1<=kappa_(u1)+min(kappa_v,kappa_w). Start at a pole whose individual
extensions fit its gap. If the two selected openings both fail their
sufficient tests there, the shared-excess identities force the u2 opening
to pass at the other pole. This checks whole patches including slit-side
fan triangles, without the refuted far-fan lemma.

The `three-chain-switch` example strictly fails the simple threshold but
passes the stronger theorem. `three-chain-family` varies all 18 coordinates
independently by ±1/100 and certifies one fixed net throughout. Both point
examples and the box fail the old weighted-curvature test for all three
opposite pairs. The old illustrated `patch-budget-three-same` example is
now covered even by the simple threshold.

The rest splits into two disjoint branches: a middle extension exceeds a
pole gap, or both fit but the combined excess bound fails. The former is
nonempty: the exact `three-chain-uncovered` example (reusing the old sector
radial-failure coordinates) has that behavior and a separately certified
successful net. No actual octahedron in the second branch was established.

Next: exploit radial separation when the middle cone crosses its gap, or
prove an alternative opposite pair enters a covered regime. The temporary
linear relaxations permit the obstruction but do not impose full metric
realization. Numerical optimizations of the second branch approached its
boundary without furnishing a geometric example; this is not an exclusion
proof. Another exploratory search found three common directions with both
poles below pi without H; retaining H did not find such a shape. Neither
search establishes a universal curvature threshold.

The full octahedron remains open. Counts stay 4 of 5 complete patch regimes
(the fifth is partly proved), and 2 excluded / 47 open fixed-source classes.
Use `python3 -m n6.three_chain_examples` to rebuild the exact evidence and
`python3 -m n6.three_chain ... --analyze` for a condition audit. The main
proof is written mathematics, not a numerical or solver conclusion.

The earlier entries below preserve the successive proof states.

# Previous continuation: a shared lean budget closes the two-patch cases

10 September 2026 JST / 9 September UTC. [OCTA_PATCH_BUDGET.md](OCTA_PATCH_BUDGET.md)
proves existence under H for both two-patch arrangements and three bad
patches with mixed directions. Together with the earlier cases, four of
five coarse patch regimes are proved, with the fifth partly settled.
**The remaining pattern is three consecutive bad patches all leaning in
the same direction.** The original fixed-source count is unchanged:
2 excluded, 47 open; the new proofs can exchange the four-cut pole.

For each bad patch, the extensions seen from the two poles add to its
reflex excess. When all curvatures are below pi, the total extensions at
both poles are smaller than the combined fan gaps, so one pole supplies
an adequate total gap. A pole of curvature at least pi supplies the
complementary case. Identities across intervening convex patches finish
the opposite-patch and mixed-three-patch cases. All proofs use direct
whole-patch cone separation, not the refuted far-fan lemma.

The new `n6.patch_budget` checker computes all six sufficient angular tests
for the eight two-pole trees and distinguishes prescribed theorem choices.
Exact examples cover the new direction cases, and an 18-coordinate region
has both poles below pi with one fixed net certified throughout. The
common-direction three-patch example is explicitly classified as an open
regime despite its independently certified individual net.

Next target: the all-forward (or reflected all-backward) three-patch chain.
The total budget alone does not stop an extension entering a later patch
inside the fan. The identity rho_i - (omega_(i+1)+nu_(i+1)) =
f_(i+1)-pi-kappa_(u_(i+1)) now carries another reflex excess when the next
patch is bad. Coordinate the resulting chain across both pole views; a
new geometric step is needed. A [20,000-shape exploratory survey](results/patch-budget-survey.json)
classified every sample and checked angular choices for the 4,351 samples
with opposite bad patches or three bad patches. All of those had a successful
choice, including 28 common-direction three-patch shapes; this is numerical
evidence only and proves no further case. The written proofs above do not
depend on that survey. Reproduce it with:

```sh
durer_small_n/.venv/bin/python -m n6.patch_budget_probe --samples 20000 --seed 6091002 --output /tmp/patch-budget-survey.json
```

The earlier entries below preserve the successive proof states.

# Continuation: the one-patch family has a two-pole proof

9 September 2026 UTC / 10 September JST. [OCTA_ONE_PATCH.md](OCTA_ONE_PATCH.md)
proves existence for the entire one-nonconvex-patch family when either pole
is globally sharpest. Choose the equator vertex opposite the bad patch's
convex corner; use it for the fifth edge in two trees, with the four cuts
at either pole. If both whole-patch cone tests failed, both poles would
have curvature below pi, while the equator vertex opposite the reflex
corner would have curvature above pi. This contradicts sharpness.

The old fixed sharpest-source rule remains open. This proof can change
which pole carries the four cuts, so the original failure-class count
stays **2 excluded, 47 open**. The proof bypasses the refuted far-fan lemma.

[OCTA_HALF_FAN.md](OCTA_HALF_FAN.md) also gives a direct rule for two adjacent
bad patches when either pole has curvature at least pi. All three possible
lean patterns are proved. Exact examples and an 18-coordinate neighborhood
have separate hypothesis and all-28-pair net certificates. These families
may overlap the previous curvature and sector criteria; no global coverage
fraction is asserted.

The next three full regimes are two adjacent bad patches (especially both
poles below pi), two opposite bad patches, and three bad patches. The new
one-patch argument suggests looking for a similar contradiction coordinating
more than one pole choice. Preserve the distinction between this existence
strategy and the stronger fixed-source four-choice conjecture.

The overview has new proof pages, paired nets and 3D cut models, and a
retained progress entry. The following audit remains valid; its older
one-patch wording refers to the withdrawn fixed-source proof.

# Current timed-session audit, 9 September 2026

**Read [HINGE_AUDIT.md](HINGE_AUDIT.md) before the earlier entries below.**
An exact convex octahedron has one far-fan overlap and all other 27 pairs
safe. The source is not sharpest, so H-specific claims remain open; the
old unrestricted conditional reduction is refuted. Restore **49 original
classes, 2 excluded and 47 open**. Reopen the one-nonconvex-patch whole-net
claim. Its local and opposite-petal repair steps survive, as do all-convex
patches and the two independent switching implications.

The restricted interior-fan lemma is now also proved in the audit note: once local and opposite-petal pairs are safe, only the two slit-side far-fan pairs remain. This leaves the conservative original 49-class count unchanged.

The strongest new positive result is unchanged: **every centrally symmetric
octahedron unfolds**, by the opposite-pair curvature theorem. The new
[local radial-cover theorem](OCTA_RADIAL_COVER.md) combines exact chord and
face-angle bounds. It certifies a fifteen-parameter asymmetric family that
failed the earlier criteria. A second integer example exactly fails the
stronger criterion while its chosen net succeeds.

A further elementary reduction in [OCTA_REMAINING_FAMILIES.md](OCTA_REMAINING_FAMILIES.md) proves that, outside the curvature-pair family, all vertices of curvature at least 120 degrees lie on one triangular face. That face carries more than 360 degrees of total curvature. The three possible threshold patterns (one vertex, one edge, the whole face) are all open in full. This is a proved necessary condition, not another unfolding theorem.

Earlier entries retain their then-current conclusions and counts; the audit
above supersedes the former 24-class and one-patch claims.

# Latest octahedron step: assume overlap and switch

## Further timed-session proofs: curvature pair and short edges

[OCTA_TWO_SHARP_POLES.md](OCTA_TWO_SHARP_POLES.md) proves the opposite-pair condition K+2J>=2*pi, where K>=J, and consequently **every centrally symmetric octahedron**. The proof forces a short endpoint of the shortest two-face path by omega+2*nu<=2*pi. The sector angle is automatic since K>=2*pi/3. Source cuts are at the other pole. The more general sufficient hypotheses K>=2*pi/3 and K+2J>=2*pi are supported by the exact checker.

[OCTA_SHORT_EDGES.md](OCTA_SHORT_EDGES.md) separately proves families whose strictly convex patches each have an endpoint within the pole chord radius of a >=120-degree sector vertex. Five exact examples include all patch regimes. Neither result closes the whole octahedron or another fixed-source class. The central nine-parameter certificate is only an illustration of the unbounded central-symmetry theorem.


## Timed session: convex-patch proofs (9 September 2026)

[OCTA_CONVEX_PATCHES.md](OCTA_CONVEX_PATCHES.md) proves every four-slit net works when all four flattened patches are convex, and at least one of two specified slits works when exactly one is nonconvex and H holds. Four nonconvex patches are impossible: reflex corners force strict increases of |wu|+|vu|. This also excludes original class 20. With class 49, **2 of 24 sufficient classes are excluded, 22 remain** (8 mixed, 14 local-only). Two adjacent, two opposite, and three nonconvex patches remain open. Five integer examples have exact patch and all-pairs net checks; the 5,000-shape survey is numerical only. The full octahedron theorem, L, and F remain open.

Earlier entries below retain their then-current counts.

9 September 2026. The [case analysis](OCTA_CASE_ANALYSIS.md) implements the
user's suggested contradiction/repair approach and explains its relation to
L and F. Two universal implications are proved:

- Moving the opening repairs all three old local pairs, by the shared-vertex
  fan lemma. It can introduce different overlaps elsewhere.
- Under H, the same opposite petals cannot overlap along both fan routes.
  The necessary overlap conditions S_j<pi and S_{j+2}<pi contradict the exact
  identity S_j+S_{j+2}=2*pi+curvature(w). This invokes the existing Case A and
  base-cone exclusions and includes equality boundaries.

Using the conditional hinge lemma inside the no-local-overlap branch reduces
the sufficient failure list from 49 to 24 classes. The new angle identity
excludes original class 49, leaving **23 classes** (8 mixed, 15 local-only).
The 49-to-24 change is removal of redundant obligations, not 25 exclusions.
The 24-to-23 change is a geometric exclusion. The full rule remains open.

The identity guarantees some opening with both opposite-petal pairs safe.
Local pairs need not be safe there: a numerical follow-up found 11 apparent
failures of that stronger restricted selector on the same 3,000 shapes.
Those candidates are not exactly audited, so the notes identify them only as
numerical failures. Continue studying mixed/local failure cycles, retaining
all four choices. The report checks 36 local repairs and the symbolic angle
identities and preserves original class IDs.

# Earlier priority change: the octahedron four-slit rule

9 September 2026. At the user's request, prioritize the octahedron. The new
[four-choice proposal](OCTA_FOUR_SLITS.md) retains the sharpest apex and tries
all four openings at its opposite vertex. It is a weaker target than the
existing H/R single-choice rule, using the same near-star constructions.

- Exact combinatorial reduction: 36 residual checks become 24 distinct
  relative placements, with 315 minimal simultaneous-failure covers and 49
  symmetry classes. **No new geometric class is excluded yet.**
- First target: classes 37, 40, 44, 49, each with only two bad placements.
  Class 49 is the same opposite-petal pair overlapping along both fan routes.
- Numerical pilot: 3,000 shapes, all 24 near-stars tested; every sharpest-apex
  four-tree family has a numerically clear choice. This is not a proof.
- Secondary route: the archived geodesic-sector sufficient theorem, with
  an open existence step. Retain its exact sharpest-sector radial obstruction.
- Reused the minus-edge batch development and archive two-face path routines;
  compared all 384 octahedral trees on two fixtures with independent geometry.
- The overview now puts this priority first, links the full proposal and
  saved enumeration, and preserves earlier notes and proof counts.

The old single-choice proof still has Lemma L and the small-angle
opposite-petal gap. The full octahedron and n=6 theorem remain open.

# Earlier continuation: a universal seven-class exclusion

9 September 2026. [MINUS_NEIGHBORHOOD.md](MINUS_NEIGHBORHOOD.md) applies
Pinciu's face-neighborhood theorem to one previously residual pair in each
minus-edge tree. It excludes original classes 7, 13, 18, 19, 20, 21, 22
for every convex realization. The remaining 21 classes, two-tree conjecture,
and full n=6 case remain open. The checker now validates this theorem
application, with an explicit literature dependency. Earlier notes follow.

---

# Latest continuation: minus-edge patterns

9 September 2026. [MINUS_PAIR.md](MINUS_PAIR.md) records a new two-tree
conjecture, a two-fan interpretation, exact switching examples, and a complete
16-cell certificate using one fixed tree on the same ±0.05 box. The earlier
certificate used nine trees and 409 cells. The domain is unchanged. The
universal two-tree statement remains open; 33,000 samples and 150 directed
starts are numerical evidence only. Its simultaneous-failure cases reduce
combinatorially to 28 symmetry classes, none yet excluded as a whole.

The earlier sessions are retained below.

---

# Second continuation on 9 September 2026

The overview was updated first, and the additional research hour began at
approximately 02:05 UTC. The full n=6 theorem remains open. The main new exact
result rules out a stronger intermediate claim without refuting the proposed
unfolding itself. Earlier progress is retained below.

## New exact results

- **Individual-apex exclusion is false for actual convex octahedra.** Six
  small integer-coordinate vertices satisfy H and R, strict Case B, and
  `Sigma_W+a<pi`; one outer apex and its far vertex pass into the relevant
  half-plane. The other petal remains outside, and all 28 pairs of the selected
  net are certified simple. An eleven-parameter closed box of radius `1/1000`
  has the same verified behavior. [CASE_PARTITION.md](CASE_PARTITION.md)
  gives the coordinates, orientation, figure, and exact replay commands.
  This does not settle the distinct remote-apex orientation.
- **Global metric closure is an additional necessary condition.** An exact
  intrinsic metric passes shared triangle lengths, positive curvatures, all
  six strict convex-vertex cone conditions, and H/R. Nevertheless, a complete
  five-interval certificate proves that it cannot be the original edges of
  a strictly convex octahedron. [AXIS_CLOSURE.md](AXIS_CLOSURE.md) derives the
  necessary equations and documents the verifier. No sufficiency claim is made.
- **Distance resolves the known local angular obstruction at that example.**
  On every shared ray, its petal starts at least `1217/1000` as far from w as
  the opposite fan's outer edge. Three exact inequalities establish this bound.
  [LEMMA_L.md](LEMMA_L.md) explains the clipped-triangle argument. L universally
  remains open. The closest candidate from the new coordinate search is also
  exactly certified nonoverlapping after rational reconstruction at 320 bits.
- **Prism path rules need a genuine choice.** Both quadrilateral routes at a
  fixed degree-four apex can fail. In a smaller example, the shorter route
  at the strictly sharper degree-four apex fails while the longer route gives
  a certified simple net. See [PRISM_DIAGONAL.md](PRISM_DIAGONAL.md). Neither
  example refutes the conditional reduction or the existence of an unfolding.

## Numerical exploration and unresolved queries

A reproducible coordinate optimizer retains the actual octahedron geometry,
H/R comparisons, and explicit support and azimuth guards. Ten-minute runs
made 2,112 local-search attempts and 971 joint-petal reach attempts in the
remote/slit-3 orientation. A further seven-minute run made 702 joint-reach
attempts in slit 0; neither orientation produced a candidate with positive
joint reach within these guarded searches. The saved
reports state their coordinate bounds and guards. The best local near-contact
candidate was rechecked exactly; its selected net is simple. No search absence
is treated as a theorem, and no numerical lower margin is claimed uniform.

The best joint-reach candidates are limited by the imposed support guard:
their minimum normalized supporting-plane clearance is approximately 1e-5.
Their fan-angle sums approach pi from below (gaps about 1.27e-4 and 2.88e-5
radians). In both, the far vertices approach the wedge crossing, while the
apex reach scores stay substantially negative. Thus these two optimizations
point toward nearly flat shapes near the already-proved cone boundary, not
toward both apices entering together. This is diagnostic numerical evidence
only; it suggests treating this boundary separately in a future proof and
explains why the observed negative score cannot be taken as a uniform bound.

The symbolic intrinsic search now supports axis closure. Two versions returned
`unknown` because of the 1 GB memory limit, after about 159 and 44 seconds.
The second version uses lower-degree opposite-arc equations and a shorter
angle target. Neither outcome proves the remaining bound.

For the prism, 50,000 samples found no failure of the four quadrilateral-route
trees. A separate 60,000-sample run found no failure when keeping both routes
at the sharper degree-four apex. Always choosing the shorter route failed
395 times, and one such failure was independently certified with integer
coordinates. Only the latter exact check proves that specific rule false.

## Overview and verification

The top notes are now retained in a collapsed history and repeated, filtered,
with their relevant results. Result links navigate and scroll to the actual
explanation, including repeated clicks on the currently selected result.
The cone proof, 409-region minus-edge certificate, 443-region prism certificate,
and remaining obligations have plain-language scope explanations. The original
illustrative prism remains first on its page. The new apex-entry example has
both a scientific net diagram and a matching interactive 3D model.

All **77 tests pass**, including the new point/region counterexamples, five-cell
nonclosure certificate, positive closure controls, and rejected tampered
certificates. The navigation regression passes; code-level checks render all
24 models and verify the thesis/prism controls and original prism ordering.
Every local file link resolves. These are code-level UI checks, not a claim of
interactive browser verification. The rebuilt eleven-page proof PDF was
rendered and visually checked before being saved.

## Next obligations

The individual-apex shortcut must be replaced by a joint constraint: when one
petal reaches the possible-meeting wedge, what prevents the other from meeting
it? Keep the slit-side and remote orientations explicit. For L, use distances
rather than requiring disjoint directions. For the prism, investigate both
quadrilateral paths at the sharper degree-four apex; length minimization alone
is false. For complete computational coverage, an exhaustive domain reduction
and treatment of degeneracies remain missing. The bounded region certificates
continue to prove exactly their stated domains.

---

# Continuation on 9 September 2026

The requested one-hour search began at approximately 00:12 UTC. Independent
verification and final packaging continued afterward. The full n=6 theorem,
Lemma L, and the remaining small-fan-angle Case B bound remain open.

## Independently verified progress

- **Wider original-facet coverage.** Every parameter in the ten-parameter
  octahedron-minus-edge chart may now vary independently by `1/20` about
  `(1,1,0,1,3/4,1/4,1,1/4,3/4,1)`. The 409-region cover passes independent
  replay, with nine trees and all 8,589 face-pair checks. See
  [REGION_COVER.md](REGION_COVER.md). This is an exact theorem about that closed
  box, not universal coverage of the combinatorial type.
- **A stronger obstruction to an angular proof of L.** An integer-coordinate
  convex octahedron satisfies H and R, yet one ray from w passes through both
  interiors of a local petal/fan pair at different distances. Every line through
  w fails to separate that pair. All 28 pairs of the same net are independently
  certified nonoverlapping. See [LEMMA_L.md](LEMMA_L.md) and its new diagram.
- **Metric compatibility made explicit.** The earlier rational angle model
  cannot close either spoke cycle. The new sine-rule equations characterize
  shared-edge compatibility of the eight triangles. A separate exact intrinsic
  metric satisfies the rankings but violates necessary convex-vertex cone
  inequalities. These distinguish two inadequate relaxations; neither witness
  disproves the geometric conjecture. See [INTRINSIC_METRIC.md](INTRINSIC_METRIC.md).

## Search and verification improvements

The wider cover was completed by overlaying complementary partial searches,
then resolving only their remaining cells. Candidate leaf counts are now
accompanied by exact parameter-volume fractions. Neither label counts nor
volume bookkeeping substitute for independent geometric replay.

The exact checker retains linear correlations when a norm is provably the
absolute value of one coordinate. An experimental affine-coefficient split
rule performed worse on this box and remains optional. Trying all 224 trees
on the unsplit wider root did not produce a single-box certificate; this was
an inconclusive interval calculation, not a proof of overlap.

The two intrinsic nonlinear queries timed out: approximately 904 seconds for
the lifted slit-3 query and 695 seconds for the unlifted slit-0 query. They
prove no universal bound. The driver now reuses the existing separate-process
time and memory guard; a short-limit check confirmed an explicit unresolved
termination result.

All **64 tests pass**. Overview checks render every section and all 23 existing
3D models, including the thesis and prism controls. The original illustrative
prism still appears before its reduction and failure example. The updated
overview includes the new L diagram and exact coverage scope.

## Next mathematical priorities

For L, look for a separator whose position depends on distances, or compare
radial intervals directly; disjoint angular sectors around w are too strong.
For Case B, retain both shared-edge compatibility and the convex-vertex cone
conditions, and state which triple/slit orientation is being treated. For
global computational coverage, the outstanding issue is an exhaustive domain
reduction, including near-degenerate limits; enlarging one local box does not
settle that issue.
