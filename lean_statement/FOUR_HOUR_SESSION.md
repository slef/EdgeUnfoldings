# Four-hour star-unfolding continuation

Authorized window: 16 September 2026, 00:13:33–04:13:33 UTC
(02:13:33–06:13:33 Europe/Brussels).

The authorized window is complete. Latest full validation: 834 Lean files /
3,937 audited theorem declarations. The existing heartbeat was PAUSED at
04:13 UTC after the deadline. Resume only under a new user continuation.
Heartbeat id: `lean-proof-three-hour-session`.

## Scope preserved

Work stayed in `lean_statement/`. No subagents were used. One compiler
pipeline ran at a time against the pinned, read-only dependency checkout
`/Users/sl/Dropbox/MyStuff/dev/lean-unfoldings`. The public Definitions
(55 lines) and Statement (15 lines) retain their original hashes. The
separate mathematical manuscript is unchanged.

## What is now proved about the star

[CofacialStarEmbedding](SixVertexUnfolding/Geometry/CofacialStarEmbedding.lean)
constructs the actual star development in the covered cofacial-source cases.
All five bounded construction milestones are checked:

1. One coherent planar placement and global kite separation.
2. Agreement of complete triangle maps and continuity of the retained map.
3. Actual inverse disks, open embedding, and exact local intrinsic isometry.
4. Boundedness and path connectivity of the actual retained image.
5. The exact compact kite closure and finite straight-segment cut boundary.

This is 100% of these five specified milestones, not 100% of the star
theorem. The hypotheses use the nonuniversal `SixVertexGraph` models and
a vertex source sharing a face with every vertex. In particular, they
do not cover the universal family or arbitrary sources, and do not assert
that an all-triangular octahedron has such a source.

[StarEdgeAssembly](SixVertexUnfolding/Geometry/StarEdgeAssembly.lean)
proves the generic conversion from a connected injective local isometric
star development, with uncut original face interiors, to the public
whole-face edge unfolding. [UniversalStarInteriors](SixVertexUnfolding/Geometry/UniversalStarInteriors.lean)
proves that face-interior cut condition at a universal source. The actual
universal development has not been constructed.

## Universal-vertex progress and next obligation

The actual link is a five-cycle. Its five original triangular faces are
distinct, cyclically ordered, and exhaust the incident faces. Their
transverse directions give a strictly supported five-ray figure, with
each corner strictly exposed. The five triangles cover the whole surface
near the vertex, and normalization preserves their spatial angles.

Still prove the strict total five-ray angle deficit, build the shorter
surface detour, and prove vertex avoidance. Then extend the canonical
cut-locus and source-cone construction to the universal family. A general
arbitrary-source star theorem also needs singular internal junctions.

[FIVE_RAY_NEXT.md](FIVE_RAY_NEXT.md) records a concrete proposed enclosing-
triangle proof of the angle deficit. The triangle-perimeter and corner-cut
lemmas are checked, as is extension to a specified supporting line. The
cyclic-start selection calculation and the base-order argument in that
file are informal and have not yet been formalized. Do not count them as
proved lemmas or assume their conclusions.

## Validation

Starting checkpoint: 716 Lean files / 3,529 audited theorem declarations.
Current checkpoint: **834 Lean files / 3,937 audited theorem declarations**,
using only `propext`, `Classical.choice`, and `Quot.sound`. All project
source files belong to the audited build closure. The sole original
main-theorem `sorry` remains; no new proof holes or axioms were added.

Read [STAR_NEXT.md](STAR_NEXT.md) for the concise proof map and
[GLOBAL_ASSEMBLY.md](GLOBAL_ASSEMBLY.md) for the now-checked assembly.
The full star theorem remains unfinished; no overall progress percentage
is justified.
