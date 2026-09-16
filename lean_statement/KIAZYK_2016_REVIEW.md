# Journal paper comparison: point-source star unfolding

Reviewed 16 September 2026 against the supplied
`/Users/sl/Downloads/kiazyk2016.pdf`: Kiazyk and Lubiw, *Star Unfolding
from a Geodesic Curve*, Discrete & Computational Geometry 56 (2016),
1018-1036, DOI [10.1007/s00454-016-9795-1](https://doi.org/10.1007/s00454-016-9795-1).
Relevant parts: Section 1.1, p. 1021; Section 2, pp. 1022-1026.
Compared with Chapter 2 of Kiazyk's 2014 thesis, pp. 12-21.

## What improves

- **Lemma 2, pp. 1023-1024:** a single kite lies in its wedge when the
  outer-leg angle is between `pi / 2 + alpha(e)` and `3 * pi / 2`.
  Figure 3 explains this using tangents to two circular sectors. Exclusion
  is obtained by applying the same lemma to the complementary region.
  This is a cleaner statement than the thesis's two-kite Lemma 2.1.
- **Theorem 1, pp. 1023-1025:** the initial exterior wedge `W0` makes the
  induction uniform: the next kite is outside the old wedge, and the new
  wedge contains both. The intermediate rotated wedge is named explicitly.
  These are the operations checked by `WedgeStep` and `JunctionWedgeStep`.
- **Original vertices inside the cut locus:** p. 1025 explicitly explains
  local nonoverlap at an original vertex after its one chosen source cut.
  Lemma 3, pp. 1025-1026, also treats original vertices that are not leaves.
  This case was already mentioned in thesis Lemma 2.3; it is not a new
  theorem discovered only in the journal version.
- **Dependencies are clearer:** p. 1021 cites Sharir-Schorr [12] for the
  cut-locus tree and Agarwal-Aronov-Schevon [1] for its edge geometry.
  Page 1023 cites [9, Lemma 2] for noncrossing shortest paths and
  [12, Lemma 4.2] for shortest paths not crossing the cut locus.
  These are references to mathematical prerequisites, not Lean assumptions
  that may be inserted without proof.

## Consequences for the current Lean construction

The journal confirms the same kite-and-wedge route. The checked planar
argument already uses the explicit angle budget and rotation/root-move
steps. There is no reason from this comparison to replace that argument.

The present `CutTreeCharts.original_leaves` field is a restriction of our
construction, not a hypothesis of the published theorem. `JunctionFan`
currently constructs a flat circular fan only at non-original vertices.
For arbitrary sources, a proposed extension is to develop an original
vertex's cone after the selected source cut into an ordered planar sector,
and prove the corresponding incident-kite ordering and frame compatibility.
The journal's local argument explains why this should suffice, but does
not construct those Lean objects or discharge their proof obligations.
The cofacial-source case can continue to use the existing leaf construction.

## What it does not resolve

Page 1023 uses the surface-angle bound `<= 2 * pi` as an established fact.
The wedge argument only needs that non-strict bound. Our separate
shortest-path avoidance argument needs strict deficit at an original
vertex to construct a shorter local detour. Section 2 supplies no new
proof of either the general angle bound or the degree-five detour.
The five-ray target in `FIVE_RAY_NEXT.md` therefore remains open, as does
extension of the cut-locus construction beyond `SixVertexGraph`.

For transcription, p. 1025 has apparent slips: the shared junction of
`ki` and `ki-1` is `pi-1`; and after the root move the outer-leg angle is
`pi / 2 + alpha_i`, as defined on p. 1023 and drawn in Figure 4.
The text abbreviates that latter angle to `alpha_i`. These observations
are consistency checks, not claims of a flaw in the geometric argument.

This review proves no additional Lean declarations and does not increase
the scope of the checked star theorem. Use the journal numbering as the
primary reference for subsequent work, with the thesis as a supplement.

Subsequent implementation: the five-ray angle bound and its transfer to
the actual universal-vertex faces were completed on 16 September 2026.
See `FIVE_RAY_NEXT.md`. The descriptions of open work above record the
state at the time of the paper comparison.
