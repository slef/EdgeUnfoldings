# Seven minus-edge failure classes excluded by a face-neighborhood theorem

9 September 2026. **Seven of the original 28 classes are excluded; 21 remain
open. The two-tree conjecture and the full minus-edge case remain unproved.**

## The geometric fact being used

Pinciu's Theorem 1 states that a face and its edge-adjacent faces unfold
without overlap when each neighbor stays hinged directly to that face.
This is a result for arbitrary convex polyhedra, with no angle or thickness
restriction. See Val Pinciu, [*On the Fewest Nets Problem for Convex
Polyhedra*, CCCG 2007, Theorem 1, pp. 21–22](https://cccg.ca/proceedings/2007/01a4.pdf).

The proof considers the two supporting lines of the hinge edges. Parallel
lines separate the opened faces. When the lines meet, their intersection
and the three supporting planes give a virtual trihedral corner; its face
angles leave a positive gap between the opened faces. The common-vertex
case follows from positive curvature. This explains why convexity matters.

We use that published theorem as a mathematical dependency. The code checks
its hypotheses and application; it is not a formal derivation of the theorem.

## Application to the two particular trees

Retain the labels and trees in [MINUS_PAIR.md](MINUS_PAIR.md). Consider two
faces whose unique uncut dual path has the form **face — base — face**.
Their relative placement is determined by those two hinges alone. It is
the same placement as in the base's face-neighborhood unfolding, regardless
of the other faces attached elsewhere in the full net. They cannot overlap.

This applies to the following previously residual pairs:

| Tree | Faces that cannot overlap | Exact uncut path | Hinge edges |
|---|---|---|---|
| T_P | ACP and BDQ | 1 — 0 — 4 | AC, BD |
| T_Q | ADQ and BCP | 3 — 0 — 6 | AD, BC |

All four faces in this table are original facets; the base is the original
quadrilateral ACBD. No diagonal, additional cut, or limiting argument is
introduced. The conclusion holds throughout the full convex realization
space, including shapes outside every previously certified coordinate box.

The tree matters: **ACP/BDQ is not excluded this way in T_Q**, where its
path is 1 — 6 — 0 — 4. Likewise ADQ/BCP has a longer path in T_P. The checker
rejects a face-neighborhood witness for such a path.

## What this removes from the proof target

Each tree originally had seven residual pairs after the common-vertex
checks. One pair per tree is now excluded, leaving six. Simultaneous failure
therefore has 36 combinations instead of 49. The existing symmetry reduces
these to **21 classes instead of 28**.

For stable comparison, keep the original class numbers. Classes **7, 13,
18, 19, 20, 21, 22** are excluded. These are 13 ordered combinations: the
row and column containing a proved-impossible pair, with their intersection
counted once. Under symmetry they form one singleton and six two-element
classes. The other 21 classes retain their original IDs and remain open.

These are logical cases, not equal portions of shape space or equal amounts
of proof work. The result is a universal partial lemma, not a completed
unfoldability theorem. No additional six-vertex type has been proved.

## Exact checking and the remaining search

`polycert` now accepts `face_neighborhood` witnesses only after checking the
convex polyhedron and the exact two-hinge path through the named base.
Old certificates keep their original witnesses. A new fixed-point replay
in `results/minus-pair-neighborhood.verification.json` records 14 vertex-fan,
one face-neighborhood, and six separating-edge checks, and names the theorem
dependency explicitly.

The original combinatorial census is retained in
`results/minus-pair-obligations.json`. The updated classification is in
`results/minus-pair-proof-progress.json`. Reproduce it with:

```
python3 -m n6.minus_pair progress
python3 -m n6.polycert verify n6/results/minus-pair-neighborhood.certificate.json
```

The numerical survey and targeted searches are recorded separately. A lack
of failures does not exclude any additional class. Even a solver's UNSAT
report is kept separate from an independently checked proof.

The survey tested 12,000 generated shapes. The class-directed search made
393,475 objective calls across all 21 open classes, with no joint failure
above its numerical threshold. Eight candidates within 10^-12 of zero were
reconstructed using their exact decimal coordinates and checked at 240-bit
interval precision. Five have exactly one failing candidate tree, and three
have both candidates certified nonoverlapping. None is a counterexample to
the two-tree rule. These are fixed-shape checks, not exclusions of their
entire geometric classes.

```
durer_small_n/.venv/bin/python -m n6.minus_targeted survey --output n6/results/minus-pair-survey.json
durer_small_n/.venv/bin/python -m n6.minus_targeted search --input n6/results/minus-pair-survey.json --output n6/results/minus-pair-targeted.json
python3 -m n6.minus_targeted audit --input n6/results/minus-pair-targeted.json --output n6/results/minus-pair-targeted-audits.certificate.json
python3 -m n6.minus_targeted verify-audits --input n6/results/minus-pair-targeted-audits.certificate.json
```

These commands replace their named outputs. Preserve the saved run with
different filenames when exploring new seeds or budgets. Counts record
actual work, including invalid objective proposals; they are not counts of
distinct convex polyhedra.

`minus_query.py` provides a polynomial query for each original class. Set
A=(0,0,0), B=(1,0,0), C=(c,−d,0), D=(e,f,0), P=(r,s,−h), Q=(t,k,−l).
Every labelled realization has this form after a rigid motion and positive
scaling. Quadrilateral convexity is exactly d,f>0 and
0<cf+de<d+f; h,l>0 put P,Q below the base. The queries impose every strict
original-facet support, develop the triangles by exact distance and side
equations, and require interior overlap in both specified pairs. They do
not bound coordinates or angles and do not triangulate the quadrilateral.

```
durer_small_n/.venv/bin/python -m n6.minus_query --class-id 14 --solver-ms 20000 --wall-seconds 28 --output n6/results/minus-class-14
```

The next geometric target is the remaining cross-fan interaction, especially
the two arrangements of ACP versus ADQ (class 14). The additional individual
pair ACP/BPQ in T_P has not failed in the searches, but has no proof here and
is deliberately retained among the open cases.
