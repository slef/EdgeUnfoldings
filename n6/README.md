# Six-vertex integration and certification

The full six-vertex theorem is **not proved or computationally certified here**.
Read [REVIEW.md](REVIEW.md) before using the older handoff or proof notes.
The current priority is the **octahedron**. The [hinge audit](HINGE_AUDIT.md)
exactly refutes the older conditional fan-to-petal reduction. Restore the
original **49 failure classes: 2 excluded, 47 open**. The all-convex-patch
case and the convex-patch existence theorem remain proved; the proposed
one-nonconvex-patch whole-net argument has a remaining far-fan step.

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
