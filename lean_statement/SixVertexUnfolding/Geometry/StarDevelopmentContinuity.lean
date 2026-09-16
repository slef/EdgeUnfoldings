import SixVertexUnfolding.Geometry.StarDevelopmentMap

/-! The finite closed triangle cover glues continuously on the actual
surface with its star-cut rays removed. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

/-- The assembled development is continuous throughout the retained surface. -/
theorem develop_continuous {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    Continuous (fun b : P.UncutSurface a => charts.develop b.val) := by
  classical
  letI : Fintype T.vertices := T.finite_vertices.fintype
  letI : DecidableRel T.graph.Adj := Classical.decRel _
  let pieces (i : T.graph.Dart × Bool) : Set (P.UncutSurface a) :=
    {b | b.val ∈ range (closedRouteStripMap ((charts.global i.1.adj).routes i.2))}
  have closed (i : T.graph.Dart × Bool) : IsClosed (pieces i) :=
    (isCompact_range (closedRouteStripMap ((charts.global i.1.adj).routes i.2)).continuous).isClosed.preimage
      continuous_subtype_val
  have covered : ⋃ i, pieces i = univ := by
    apply eq_univ_of_forall
    intro b
    obtain ⟨u, v, edge, side, inside, _⟩ := charts.develop_spec b.val
    exact mem_iUnion.mpr ⟨(⟨(u, v), edge⟩, side), inside⟩
  have continuous_piece (i : T.graph.Dart × Bool) :
      ContinuousOn (fun b : P.UncutSurface a => charts.develop b.val) (pieces i) := by
    apply continuousOn_iff_continuous_restrict.mpr
    let inclusion (b : pieces i) : range (closedRouteStripMap ((charts.global i.1.adj).routes i.2)) :=
      ⟨b.val.val, b.property⟩
    have continuous_inclusion : Continuous inclusion :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have continuous_coordinates := continuous_subtype_val.comp
      (((charts.global i.1.adj).sideTriangle i.2).homeomorph.continuous.comp continuous_inclusion)
    apply continuous_coordinates.congr
    intro b
    exact (graph.develop_on_triangle small_faces charts cofacial i.1.adj i.2 b.val.val b.property b.val.property).symm
  exact (locallyFinite_of_finite pieces).continuous covered closed continuous_piece

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
