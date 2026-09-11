# Six-vertex integration and certification

**Latest completion, 12 September:** [all seven six-vertex type arguments are written](N6_PROOF_MAP.md),
including the [complete minus-edge proof](MINUS_EDGE_PROOF.md) and now the
[seven-candidate prism proof](PRISM_EDGE_PROOF.md). **Independent mathematical
review remains necessary.** The three new prism angle identities pass exact
rational coefficient expansion; the geometric dependencies are written proofs,
not formally verified results. Numerical experiments are not proof premises.

The prism argument uses the [one-pair chain reduction](PRISM_ONE_PAIR.md),
[sharp-fan switch](PRISM_SHARP_FAN_SWITCH.md), and [alternate-source gate switch](PRISM_GATE_SWITCH.md).
A failed direct-cut test forces an alternate candidate's hypotheses.
The old fixed two-tree minus-edge conjecture remains separate at 7/28.

Replay exact illustrations with `python3 -m n6.minus_complementary_examples`,
`python3 -m n6.prism_complementary_examples`, and
`python3 -m n6.prism_edge_theorem INPUT.json`. The last selector tries seven
original trees and certifies one uniformly on the supplied domain; it may
reject a box whose shapes require different choices. The universal theorem
is the separate written proof. Run `python3 -m n6.prism_angle_identities`
for its exact algebraic audit. New results include full ten- and nine-parameter
families and independent original-face checks.

The earlier [curvature budgets](ORIGINAL_EDGE_RULE.md), [wider Case A cones](CASE_A_WIDE_CONES.md),
[actual-length separators](CASE_A_LENGTH_SEPARATORS.md), and
[support-triangle sharpening](CASE_A_SUPPORT_TRIANGLE.md) remain available.
The following earlier entries retain their historical scopes and counts.

**Every-slit progress:** [safe local pairs imply the whole net is safe](LOW_CURVATURE_FAR_REDUCTION.md)
when all six curvatures are at most pi. Neither H nor R is needed. The
three local premises must be checked at the actual slit; the original
every-slit Lemma F remains open. Replay the point and 18-coordinate family
with `python3 -m n6.low_far_examples`. Both curvature rankings fail there,
and independent all-28-pair certificates agree.

**Latest extension, 11 September:** [flat auxiliary hinges](OCTA_FLAT_HINGES.md)
close the maximum-curvature pi boundary for both nonsimplicial types.
Every shape of either type with all six curvatures<=pi now has an
original-edge unfolding. Additional higher-curvature fixed trees follow
when the original degree-four source has curvature>=pi and the original
fifth edge satisfies [the weighted slit threshold](OCTA_SLIT_THRESHOLD.md).
The remaining n=6 shapes have maximum curvature strictly above pi and
lie outside these sufficient original-tree criteria. Whole types stay 5/7.
Independent mathematical review is still needed.

The weighted threshold also widens the octahedral selected rule: under H,
any slit with 2*kappa_c+kappa_w>=pi gives a whole safe net, including
equality. A remaining every-slit Lemma F counterexample must lie below
that threshold; in its all-low branch it must also have a local overlap.



The full n=6 theorem remains open. **The octahedron type now has a complete
written selected-net proof** in [LEMMA_F_CHORD.md](LEMMA_F_CHORD.md), with a
dependency audit and two exhaustive source-curvature branches. Choose a
maximum-curvature source v, its opposite w, and a maximum-curvature equator
slit c; cut the four edges at v and w-c. Every tied choice is included.

This gives 28/28 safe pairs and all five patch regimes, bringing the whole
six-vertex type count to 5/7. The original every-slit Lemma F remains open,
as do the two nonsimplicial types, where artificial diagonals cannot be cut.
The proof awaits independent mathematical review; the code checks explicit
domains and is not a formal verification of the whole geometric argument.

Run `python3 -m n6.selected_octahedron_examples` to replay nine exact domains,
including a point at source curvature pi, a full 18-coordinate box crossing
pi, and the regular octahedron with ties. Each domain also has an independent
all-28-pair certificate. Numerical searches are not proof premises.
Read [CONTINUATION.md](CONTINUATION.md) for the current next questions.

<details>
<summary>Earlier investigation, retained with its historical proof states</summary>


The full six-vertex theorem is **not proved or computationally certified here**.
Read [REVIEW.md](REVIEW.md) before using the older handoff or proof notes.
The current priority is the **octahedron**. The [hinge audit](HINGE_AUDIT.md)
exactly refutes the older conditional fan-to-petal reduction. Restore the
original **49 failure classes: 2 excluded, 47 open**. The all-convex-patch
case and the convex-patch existence theorem remain proved; the proposed
fixed-source one-nonconvex-patch argument has a remaining far-fan step.

**Latest result, 11 September:** [the selected net is nonoverlapping whenever
the sharpest curvature is at least 180 degrees](LEMMA_F_POLE_ANGLE.md),
including equality. A hypothetical cut crossing traps a neighboring patch
inside a triangle; a supporting line makes that containment impossible.
The spherical-link bound supplies the nonobtuse pole angle throughout this
entire curvature family, completing all 28 pairs. Below 180 degrees,
nonobtuse original/flat angles and a quarter-turn circle argument cover
further families. The remaining obstruction needs an obtuse original and
flat angle, with blue angle plus gap below 90 degrees. That joint branch
is open; the general selected rule and every-slit Lemma F are not proved.
Replay four exact examples, including an 18-coordinate box and an obtuse
point repaired by the circle argument: `python3 -m n6.far_projection_examples`.

**Previous result, 11 September:** [two finite cut segments characterize safety
of the selected net](LEMMA_F_CUT_RAYS.md) under H and R. The through-fan bound
from Lemma L excludes one approach to each segment. Convex remote patches,
leans away from the slit gap, and insufficient angular reach are proved safe,
including in Case B past X. The common-direction three-patch pattern leaves
one segment check. The universal gap inequality and finite-edge separation
remain open; the unconditional count stays 22/28. Replay the exact point
and coordinate-box checks with `python3 -m n6.cut_ray_examples`.

**Previous result, 11 September:** [two cut-side fan checks now suffice for all
six far pairs](LEMMA_F_CUT_REDUCTION.md) under H and R. The proved reduction
uses the completed Lemma L. It also settles the small-angle case when the
slit-side far vertex is at or before X, even if the other far vertex passes X.
The two universal fan checks remain open; the unconditional count stays 22/28.
Replay exact two-pair certificates with `python3 -m n6.far_pair_examples` or
`python3 -m n6.far_pairs n6/results/far-pair-apex-entry-family.certificate.json`.
The latter covers an 11-coordinate box; another saved box has 18 coordinates.
Independent all-28-pair certificates agree on these explicit regions.

**Previous result, 11 September:** [Lemma L is proved](LEMMA_L_PROOF.md). All three local pairs are safe under the original selections (in fact, a pole-curvature comparison and maximum-curvature slit suffice). A cut-edge separator handles the slit route; a spherical-link and pole-triangle argument handles the route through the fan. The selected net now has 22/28 pairs universally safe. Lemma F and the full octahedron remain open. Use `python3 -m n6.local_lemma CERTIFICATE` for exact hypothesis checks.

**Previous result:** [LEMMA_L_CURVATURE_GATE.md](LEMMA_L_CURVATURE_GATE.md)
directly advances Lemma L. The slit and opposite-pole curvatures determine
which of two local overlap routes is impossible; at sum pi, all three local
pairs are safe. Additional corner subfamilies follow. In the small-sum
half only one slit-inward petal can cause the remaining two local pairs.
The general lemma remains open. Exact examples include an 18-coordinate
box with radial separation ratio 6/5 and independent whole-net certificates.
Replay with `python3 -m n6.local_gate_examples`.

**Previous result:** [OCTA_THREE_CHAIN.md](OCTA_THREE_CHAIN.md) proves
common-direction three-patch subfamilies with a four-tree rule. The middle
patch controls a safe pole switch. A simple inward-excess threshold and
a stronger two-view condition have geometric proofs and exact point/box
illustrations. Two branches outside those conditions remain open. The
full three-patch regime remains unproved, so the coarse count stays 4 of 5.

**Previous result:** [OCTA_PATCH_BUDGET.md](OCTA_PATCH_BUDGET.md) proves every
configuration with at most two nonconvex patches, and three with mixed
directions, under H. It uses the identity that a patch’s two pole extensions
sum to its reflex excess, plus a total angle budget. **Three bad patches
with a common direction remain open.** Four of five coarse existence regimes
are settled, with the fifth partly settled. The fixed-source count is
unchanged; no percentage of shape space is inferred.

**Previous proof:** [one bad patch under H](OCTA_ONE_PATCH.md) now has a complete
existence proof using two prescribed trees with different four-cut poles.
The fixed sharpest-source statement remains open. The independent
[half-fan argument](OCTA_HALF_FAN.md) handles all three adjacent-two-patch
directions when either pole has curvature at least 180 degrees. Exact
examples and an 18-coordinate region have independent all-pairs checks.
These results do not change the original fixed-source class count.

The independent [curvature-pair theorem](OCTA_TWO_SHARP_POLES.md) proves
unfoldability when the sharper pole has curvature K, its opposite J, and
K+2J>=2*pi. **Every centrally symmetric octahedron follows.** The
[short-edge test](OCTA_SHORT_EDGES.md) and stronger
[local radial-cover theorem](OCTA_RADIAL_COVER.md) prove further asymmetric
families. Their hypotheses are not universal. Exact certificates check
both covered regions and exceptions to the sufficient tests.

A [universal partial lemma](MINUS_NEIGHBORHOOD.md) now excludes seven of the
28 failure classes of the two-tree conjecture; 21 classes remain open.

The initial minus-edge pattern investigation proposes a [two-choice algorithm](MINUS_PAIR.md):
one of its trees is independently certified on the entire earlier ±0.05 box
using 16 cells, but the universal two-tree claim remains open.
The latest verified results and remaining obligations are in
[CONTINUATION.md](CONTINUATION.md).

The continuing thesis audit and four workstreams are recorded in
[OVERNIGHT.md](OVERNIGHT.md). New rigorous results are the
[complete opposite-petal partition](CASE_PARTITION.md), an
[exact failure of DiBiase's fixed DF chart entry](THESIS_AUDIT.md), and original-
facet certificates for the two remaining nonsimplicial types. [LEMMA_L.md](LEMMA_L.md)
records the local gap, an exactly refuted bisector shortcut, and an exact
failure of every separating line through w for one local pair. The latter
net is nevertheless exactly certified simple; a diagram explains the distinction.
The final overnight coverage results are in [REGION_COVER.md](REGION_COVER.md).
[GEODESIC_SECTOR.md](GEODESIC_SECTOR.md) develops the archive's shortest-path
route and records an exact obstruction to fixing its sector vertex globally.
[INTRINSIC_METRIC.md](INTRINSIC_METRIC.md) gives the shared-edge compatibility
equations and distinguishes the abstract angle and intrinsic metric relaxations.
The second continuation refutes the individual-apex shortcut with an
[actual convex example](CASE_PARTITION.md), and adds a necessary
[global axis-closing condition](AXIS_CLOSURE.md). Neither changes the open
status of the full theorem.

This directory integrates the two supplied Codex archives with Claude's
`durer_small_n` work. It adds a smaller exact counterexample query, bounded solver
execution, and a rational interval checker for explicit regions of octahedra.


</details>

## Results with their scope

| Result | What it establishes |
|---|---|
| [Octahedron box certificate](results/octahedron-box.certificate.json) | Every coordinate tuple in this explicit 18-dimensional box is a convex octahedron with the specified nonoverlapping edge unfolding. |
| [D-lemma witness](results/d-lemma-counterexample.json) | The old unrestricted double-outward half-plane assertion is false, by exact rational interval verification. This is not a counterexample to unfoldability. |
| [24-tree query](results/nearstar.result.json) | Z3 returned `unknown` / `timeout`. The full octahedron question remains unresolved. |
| [Differential validation](results/differential-validation.json) | The two implementations agree on all 1,479 cut trees of seven fixed six-vertex realizations. Numerical validation only. |
| [Corrected angle check](results/corrected-angle-smoke.json) | A fresh, small numerical check after fixing the far-vertex index. It does not rehabilitate the historical saved searches. |
| [Individual-apex counterexample](results/caseB-apex-entry.certificate.json) | A convex integer-coordinate example under H and R has one apex strictly inside the outer wedge; all 28 net pairs remain nonoverlapping. |
| [Apex-entry neighborhood](results/caseB-apex-entry-region.certificate.json) | The same entry and complete nonoverlap hold throughout an eleven-parameter closed box of radius 1/1000. |
| [Global metric nonclosure](results/intrinsic-axis-nonclosure.certificate.json) | Five exact intervals exclude every possible opposite-vertex distance for a metric that passes all previous local checks. |
| [Prism boundary routes](PRISM_DIAGONAL.md#two-routes-around-a-quadrilateral-exact-failures-and-a-smaller-target) | Exact failures of both routes at a fixed apex, and of the shorter route at the sharper degree-four apex. Successful alternatives are certified; the two-route conjecture remains open. |
| [Local radial clearance](results/local-radial-distance.verification.json) | The angular-separation failure example has distance factor at least 1.217 beyond the opposite fan edge on every shared ray. Example-specific, not a proof of Lemma L. |
| [Base-cone lemma](CASE_PARTITION.md) | Under the sharpest-apex hypothesis, only the opposite-petal regime `Sigma_W<pi` remains; large D angles and both partition equality boundaries are included. |
| [Thesis DF witness](results/thesis-chart-DF.certificate.json) | A specified chart entry fails exactly. Reattaching only G cannot repair this core overlap. |
| [Direct prism chart](PRISM_DIAGONAL.md) | Complete nine-parameter coordinate chart; exact failure of the two-pair tree and successful alternative regional certificates. |
| [Wider prism box](results/prism-expanded-affine.certificate.json) | An explicit nine-parameter box, with every original quadrilateral retained; rational affine bounds verify all 15 pairs. |
| [Complete prism subdivision](results/prism-affine-cover.verification.json) | Independent replay verifies all 443 leaves of a larger nine-parameter box, using three trees. This is complete coverage of that box only. |
| [Larger minus-edge box](results/minus-merged-cover.verification.json) | All ten chart parameters vary by `1/20` about the specified center. Independent replay verifies 409 closed subregions, nine trees, and all 21 original-facet pairs in each. |
| [Bisector failure](results/local-bisector-failure.certificate.json) | The proposed slit bisector fails under both curvature rules; a separate all-pairs check proves that same net simple. |
| [Local radial-separator failure](results/local-radial-failure.certificate.json) | No line through w separates a first petal from the opposite fan face, under H and R; all 28 pairs of the same net are certified nonoverlapping. |
| [Intrinsic metric audit](INTRINSIC_METRIC.md) | Exact shared-edge compatibility equations; the old angle model has impossible spoke cycles, while a new shared-length countermodel fails the necessary cone inequalities. Neither is a convex-octahedron counterexample. |
| [Thin-candidate audit](results/local-directed-audit.verification.json) | The directed numerical search's apparent local overlap is certified nonoverlapping at 320 fractional bits, with the selection rules checked exactly. |

The box is centered at

```
(-4,-9,-5), (-4,-4,-7), (-7,-9,8), (-7,-6,4), (0,-7,-5), (4,9,8)
```

and allows every coordinate to vary independently by `1/1000`. Its cut tree is
`{5-1, 5-2, 5-3, 5-4, 0-2}`. The certificate checks 24 strict supporting-plane
inequalities and all 28 face pairs: 19 by the common uncut vertex-fan lemma and
9 by rigorously bounded separating edges. Boundary contact is permitted.

## Reproduction

Run from the repository root. The two certificate checks need only Python's
standard library; they use no floating-point arithmetic, NumPy, or SMT solver.

```
python3 -m n6.certify verify n6/results/octahedron-box.certificate.json
python3 -m n6.audit_witness
python3 -m n6.polycert verify-overlap n6/results/thesis-chart-DF.certificate.json
python3 -m n6.polycert verify n6/results/prism-expanded-affine.certificate.json
python3 -m n6.polycert verify n6/results/minus-wide-affine.certificate.json
python3 -m n6.cover verify n6/results/prism-affine-cover.certificate.json.gz
python3 -m n6.cover verify n6/results/minus-merged-cover.certificate.json.gz
python3 -m n6.bisector n6/results/local-bisector-failure.certificate.json --bits 80
python3 -m n6.local_radial n6/results/local-radial-failure.certificate.json
python3 -m n6.intrinsic verify n6/results/intrinsic-without-cone.certificate.json
python3 -m n6.polycert verify n6/results/local-directed-audit.selected.certificate.json --bits 320
python3 -m unittest discover -s n6/tests -p test_certificates.py -v
```

For experiments and integration tests, install `n6/requirements.txt` in a virtual
environment. The existing `durer_small_n/.venv` was used in this investigation.

```
durer_small_n/.venv/bin/python -m unittest discover -s n6/tests -v
durer_small_n/.venv/bin/python -m n6.validate
durer_small_n/.venv/bin/python -m n6.sector_probe --samples 100 --output n6/results/sector-smoke.json
durer_small_n/.venv/bin/python -m n6.query --output n6/results/nearstar --solver-ms 10000 --wall-seconds 20
```

The last command replaces its named generated query and report. Use a different
output stem to retain a run. The parent process bounds construction, export,
solver preprocessing, and solving together. The solver also has a memory limit.
Timeout, process failure, and `unknown` always remain unresolved. Even `unsat`
is labeled as a solver result without an independently checked proof certificate.

To export a query without solving, add `--export-only`. `--no-prune` retains the
archive's unpruned path formulation for comparison. `--family all --graph6 Ep~o`
or `--family all --graph6 EzNG` works directly with the original nonsimplicial
facets; artificial diagonals are never permitted cuts. `--trees 0` means every
tree in the selected family. The near-star family contains only 24 of 384 trees,
so SAT for it would not refute Dürer's conjecture.

## Provenance and code map

- `encoding.py`: the archives' byte-identical `unfolding.py`, integrated once.
  Changes are input-label validation and optional combinatorial vertex-fan pruning.
- `query.py`: the old `six_exact_probe.py` generalized to an import-safe driver
  with durable status reports and a hard process deadline.
- `sector_probe.py`: the archive's independent numerical geometry, made
  import-safe and configurable; rejects flat facet mergers.
- `intervals.py`, `certify.py`, `audit_witness.py`: new small rational checker,
  certificate generator, and proof-audit witness checker.
- `polynomials.py`, `polycert.py`, `families.py`: exact parameterized coordinates,
  original polygonal facets, and all-pairs region/fixed-tree-failure checking.
- `affine.py`: rational linear correlations with outward nonlinear remainders.
  It improves decisiveness without replacing exact sign checks by tolerances.
- `cover.py`: binary closed-box subdivision and independent all-leaf replay.
  Partial covers can be overlaid before resuming their remaining cells. Exact
  parameter-volume bookkeeping is distinct from geometric verification. Files
  with unresolved leaves are partial searches, regardless of their name.
- `curvature.py`, `regimes.py`: exact angle-product predicates and verification
  of curvature rankings, large-angle branches, and equality cases.
- `bisector.py`, `local_radial.py`, `point_audit.py`: exact follow-up of proposed
  local obstructions, sharing the same validated slit and flank construction.
- `intrinsic.py`: a rational checker for shared triangle metrics and a separate
  nonlinear query retaining positive curvature, cone conditions, and H/R.
- `sector_audit.py`, `angle_relaxation.py`: exact checks of a geometric obstruction
  to one sector strategy and an abstract angle countermodel, respectively. The
  latter is not a claimed geometric realization.
- `lemma_query.py`, `direct_query.py`, `lift.py`: focused nonlinear searches,
  including an explicit-triangle formulation and degree-reducing auxiliary
  equations. All current runs remain unresolved; no solver proof is claimed.
- `trees.py`: all original-edge cut trees and the thesis's 48 three-arm trees.
  This latter family is distinct from the 24 near-star trees, but already lies
  within the full 384-tree octahedron enumeration.
- `validate.py`: cross-check against Claude's rigid-motion development and
  polygon clipping, covering all seven six-vertex graph types.
- `archive_validation.py`: the archive's original tetrahedron validation helper.
  Its direct floating evaluation of large homogeneous determinants is unsuitable
  for certifying signs at contacts; `validate.py` removes positive homogeneous
  factors before numerical comparisons.
- `archive_notes/`: historical notes, result reports, original probe listings,
  and SHA-256 hashes of both archives and every archive member. These documents
  are research evidence, not instructions to execute or extend the task to n=7.
  The old generated SMT files are not duplicated: the original archives and
  checksums preserve provenance, and the integrated code regenerates queries.
- `results/source-inventory.json`: repository-wide inventory of the 73 existing
  Python files, their definitions and import-time experiment loops.

The archive files retain their historical claims and commands. Current scope,
corrections, and reproduction instructions are in this README and REVIEW.
