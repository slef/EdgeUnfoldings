import SixVertexUnfolding.Geometry.PrismDiagonalFanSeparation
import SixVertexUnfolding.Geometry.PrismDiagonalShortFanSeparation

/-! The fixed fallback has only one possible overlapping pair: B and D.
This is the geometric reduction used by the manuscript's two-view argument. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4}
variable (prism_kind : graph.kind = .prismDiagonal)
variable (net : graph.PrismFallbackDevelopment small_faces)
include prism_kind

/-- Star comparison and the four uncut vertex fans settle every pair except B/D. -/
theorem PrismFallbackDevelopment.nonoverlap_except_quadrilaterals
    (core_safe : ∀ f ∈ starCore, ∀ g ∈ starCore, f ≠ g →
      Disjoint (interior (net.place f '' (graph.prismDiagonalFace small_faces f).val))
        (interior (net.place g '' (graph.prismDiagonalFace small_faces g).val)))
    (f g : FaceLabel) (different : f ≠ g) (not_quadrilaterals : s(f, g) ≠ s(B, D)) :
    Disjoint (interior (net.place f '' (graph.prismDiagonalFace small_faces f).val))
      (interior (net.place g '' (graph.prismDiagonalFace small_faces g).val)) := by
  rcases (by decide : ∀ f g, f ≠ g → s(f, g) ≠ s(B, D) →
    (f ∈ starCore ∧ g ∈ starCore) ∨
    (∃ (q : Fin 2) (i j : Fin 4), i ≠ j ∧ f = fanFace q i ∧ g = fanFace q j) ∨
    (∃ (q : Fin 2) (i j : Fin 3), i ≠ j ∧ f = shortFanFace q i ∧ g = shortFanFace q j))
      f g different not_quadrilaterals with core | long | short
  · exact core_safe f core.1 g core.2 different
  · obtain ⟨q, i, j, distinct, rfl, rfl⟩ := long
    exact net.vertexFan_nonoverlap prism_kind q i j distinct
  · obtain ⟨q, i, j, distinct, rfl, rfl⟩ := short
    exact net.shortVertexFan_nonoverlap prism_kind q i j distinct

/-- For every convex prism with a diagonal, a concrete outward fallback separates 14/15 pairs.
The remaining B/D comparison is not assumed in this construction. -/
theorem exists_prism_fallback_safe_except_quadrilaterals :
    ∃ net : graph.PrismFallbackDevelopment small_faces,
      ∀ f g, f ≠ g → s(f, g) ≠ s(B, D) →
        Disjoint (interior (net.place f '' (graph.prismDiagonalFace small_faces f).val))
          (interior (net.place g '' (graph.prismDiagonalFace small_faces g).val)) := by
  obtain ⟨net, core_safe⟩ := graph.exists_prism_fallback_with_star_core small_faces prism_kind
  exact ⟨net, net.nonoverlap_except_quadrilaterals prism_kind core_safe⟩

/-- Once B and D are separated, the constructed fallback is a public edge unfolding. -/
theorem PrismFallbackDevelopment.hasEdgeUnfolding_of_quadrilaterals
    (other_pairs : ∀ f g, f ≠ g → s(f, g) ≠ s(B, D) →
      Disjoint (interior (net.place f '' (graph.prismDiagonalFace small_faces f).val))
        (interior (net.place g '' (graph.prismDiagonalFace small_faces g).val)))
    (quadrilaterals :
      Disjoint (interior (net.place B '' (graph.prismDiagonalFace small_faces B).val))
        (interior (net.place D '' (graph.prismDiagonalFace small_faces D).val))) : P.HasEdgeUnfolding := by
  apply net.hasEdgeUnfolding prism_kind
  intro f g different _
  by_cases pair : s(f, g) = s(B, D)
  · rcases (by decide : ∀ f g, s(f, g) = s(B, D) →
      (f = B ∧ g = D) ∨ (f = D ∧ g = B)) f g pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact quadrilaterals
    · exact quadrilaterals.symm
  · exact other_pairs f g different pair

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
