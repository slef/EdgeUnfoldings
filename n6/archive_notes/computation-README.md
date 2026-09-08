# Small-vertex edge-unfolding experiment

Read `edge-unfolding-notes.md` first. The seven-vertex case has **not** been solved by this experiment. This is a research prototype, not a proof checker.

Install the Python dependencies from requirements.txt in a virtual environment.

```
python unfolding.py census --output census.json
python validation.py
python unfolding.py benchmark 'C~' --timeout-ms 15000 --output tetrahedron.smt2
python unfolding.py benchmark 'Fhf~o' --trees 0 --timeout-ms 15000 --output pentagonal-bipyramid-all-trees.smt2
python unfolding.py benchmark 'FJn^W' --trees 0 --timeout-ms 15000 --output stacked-octahedron-all-trees.smt2
```

The benchmark's default `--trees 1` is a partial query; use `--trees 0` to include every tree. For a graph with a universal vertex, it deliberately uses just that vertex's spanning-star cut tree, because UNSAT for that one tree would already prove the graph's universal statement. SAT for a partial tree family is not a counterexample to Dürer.

The solver timeout limits solving; graph/formula construction and exporting are additional time. Long-path expressions may make both construction and solving expensive. A timeout or interrupted process leaves the mathematical question unresolved.

The graph census is exhaustive through seven vertices. The geometric code uses the original facets, supports polygonal faces, and allows boundary contact while forbidding interior overlap. Do not silently replace the graph by a triangulation with additional permitted cut edges.

The complete-query SMT2 export uses define-fun for common arithmetic expressions. These definitions introduce no new independent geometric choices. The geometric variable count is at most 3n−7+F; Boolean path names are definitional abbreviations.

`validation.py` compares the encoded overlap predicate with a separate numerical polygon-clipping implementation on two fixed tetrahedra. This is implementation validation, not universal geometric coverage.
