import SixVertexUnfolding.Geometry.CutLineCharts
import SixVertexUnfolding.Geometry.FiniteJunctions
import SixVertexUnfolding.Geometry.ClosedCutSet

/-! The only cut points not yet described by a straight-line neighborhood
belong to a finite set: original vertices and targets with at least three routes. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- The finite exceptional set for the regular cut-line neighborhoods. -/
def cutExceptions (P : ConvexPolyhedron) (a : frontier P.body) : Set (frontier P.body) :=
  P.junctions a ∪ {b | (b : Space) ∈ P.vertices ∧ b ≠ a}

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem cutExceptions_finite (a : frontier P.body) : (P.cutExceptions a).Finite := by
  have vertices_finite := P.vertices.finite_toSet.preimage
    (f := fun b : frontier P.body => (b : Space)) Subtype.val_injective.injOn
  exact (graph.junctions_finite small_faces a).union (vertices_finite.subset (fun _ h => h.1))

include graph small_faces in
/-- Every remaining cut point has exactly two routes and a flat chart of its full cut line. -/
theorem regular_cut_point (a b : frontier P.body) (cut : b ∈ P.cutSet a)
    (regular : b ∉ P.cutExceptions a) :
    Nat.card (P.geodesicFiber a b) = 2 ∧ Nonempty (P.CutLineChart a b) := by
  have different : a ≠ b := by
    rintro rfl
    exact P.source_not_cutSet a cut
  have not_vertex : (b : Space) ∉ P.vertices := fun vertex => regular (Or.inr ⟨vertex, different.symm⟩)
  have multiple : (b : Space) ∈ P.multipleRouteLocus a := cut.resolve_right (fun h => not_vertex h.1)
  have not_unique := ((P.multiple_routes_iff_fiber a b).mp multiple).2
  have lower : ¬ (P.geodesicFiber a b).ncard ≤ 1 := by
    intro bound
    exact not_unique ((ncard_le_one (graph.geodesicFiber_finite small_faces a b different)).mp bound)
  have upper : ¬ 2 < Nat.card (P.geodesicFiber a b) := fun many =>
    regular (Or.inl ((graph.junction_iff_route_count small_faces a b different).mpr many))
  have two : Nat.card (P.geodesicFiber a b) = 2 := by
    change ¬ Nat.card (P.geodesicFiber a b) ≤ 1 at lower
    omega
  exact ⟨two, graph.cut_line_chart small_faces a b different not_vertex two⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
