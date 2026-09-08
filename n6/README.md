# Six-vertex integration and certification

The full six-vertex theorem is **not proved or computationally certified here**.
Read [REVIEW.md](REVIEW.md) before using the older handoff or proof notes.

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
