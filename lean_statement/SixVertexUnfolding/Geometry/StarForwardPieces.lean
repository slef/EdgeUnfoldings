import SixVertexUnfolding.Geometry.TriangleForwardPieces
import SixVertexUnfolding.Geometry.StarDevelopmentContinuity

/-! The entire assembled development is a finite selection of actual
nonexpanding ambient formulas. This controls distances even on a
convex patch crossing many radial triangles. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutTreeCharts

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)

theorem finite_forward_pieces :
    ∃ maps : Set (Space → Plane), maps.Finite ∧ (∀ g ∈ maps, LipschitzWith 1 g) ∧
      ∀ b : frontier P.body, ∃ g ∈ maps, charts.develop b = g (b : Space) := by
  classical
  letI : Fintype T.vertices := T.finite_vertices.fintype
  letI : DecidableRel T.graph.Adj := Classical.decRel _
  let pieces (i : T.graph.Dart × Bool) :=
    (((charts.global i.1.adj).sideTriangle i.2).finite_forward_pieces).choose
  have specs (i : T.graph.Dart × Bool) :=
    (((charts.global i.1.adj).sideTriangle i.2).finite_forward_pieces).choose_spec
  refine ⟨⋃ i, pieces i, finite_iUnion (fun i => (specs i).1), ?_, ?_⟩
  · intro g member
    obtain ⟨i, member⟩ := mem_iUnion.mp member
    exact (specs i).2.1 g member
  · intro b
    obtain ⟨u, v, edge, side, inside, at_b⟩ := charts.develop_spec b
    let i : T.graph.Dart × Bool := (⟨(u, v), edge⟩, side)
    obtain ⟨g, member, formula⟩ := (specs i).2.2 ⟨b, inside⟩
    exact ⟨g, mem_iUnion.mpr ⟨i, member⟩, at_b.symm.trans formula⟩

end SixVertexUnfolding.ConvexPolyhedron.CutTreeCharts
