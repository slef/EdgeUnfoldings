import SixVertexUnfolding.Geometry.PrismDiagonalStarCore
import SixVertexUnfolding.Geometry.NonoverlapHingeSides

/-! Attach B and D to the four-face star core. The resulting fallback already
separates eight of its fifteen face pairs, including the opposite caps A/F. -/

namespace SixVertexUnfolding.Prism

open FaceLabel

/-- Exactly the seven unordered pairs not yet covered by the star core or an attachment. -/
def fallbackRemainingPairs : Finset (Sym2 FaceLabel) :=
  {s(A, B), s(A, D), s(B, D), s(B, E), s(B, F), s(C, D), s(D, F)}

end SixVertexUnfolding.Prism

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set Prism Prism.FaceLabel

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)
variable (prism_kind : graph.kind = .prismDiagonal)
include prism_kind

/-- A fallback can be chosen with the complete four-face chain inherited from the star.
All six core comparisons and the two quadrilateral attachment comparisons are proved. -/
theorem exists_prism_fallback_with_star_core :
    ∃ net : graph.PrismFallbackDevelopment small_faces,
      ∀ f ∈ starCore, ∀ g ∈ starCore, f ≠ g →
        Disjoint (interior (net.place f '' (graph.prismDiagonalFace small_faces f).val))
          (interior (net.place g '' (graph.prismDiagonalFace small_faces g).val)) := by
  obtain ⟨core, rigid, safe, joined⟩ := graph.exists_prism_star_core small_faces prism_kind
  obtain ⟨pB, rigidB, joinedB, safeB, _, _⟩ :=
    (graph.prismDiagonalFace small_faces C).exists_polygon_petal (graph.prismDiagonalFace small_faces B)
      (graph.prism_fallback_original_hinge small_faces prism_kind C B (by decide)) (core C) (rigid C)
  obtain ⟨pD, rigidD, joinedD, safeD, _, _⟩ :=
    (graph.prismDiagonalFace small_faces E).exists_polygon_petal (graph.prismDiagonalFace small_faces D)
      (graph.prism_fallback_original_hinge small_faces prism_kind E D (by decide)) (core E) (rigid E)
  let place : FaceLabel → Space →ᵃ[ℝ] Plane
    | B => pB | D => pD | f => core f
  have on_core (f : FaceLabel) (hf : f ∈ starCore) : place f = core f := by
    cases f
    · rfl
    · simp [starCore] at hf
    · rfl
    · simp [starCore] at hf
    · rfl
    · rfl
  have rigid_all : ∀ f, ∀ x ∈ (graph.prismDiagonalFace small_faces f).val,
      ∀ y ∈ (graph.prismDiagonalFace small_faces f).val, dist (place f x) (place f y) = dist x y := by
    intro f
    cases f
    exacts [rigid A, rigidB, rigid C, rigidD, rigid E, rigid F]
  have joined_all : ∀ f, f ≠ C → EqOn (place (fallbackParent f)) (place f)
      ((graph.prismDiagonalFace small_faces (fallbackParent f)).val ∩
        (graph.prismDiagonalFace small_faces f).val) := by
    intro f not_root
    cases f
    · exact joined C (by decide) A (by decide) (by decide)
    · exact joinedB
    · exact (not_root rfl).elim
    · exact joinedD
    · exact joined C (by decide) E (by decide) (by decide)
    · exact joined E (by decide) F (by decide) (by decide)
  have safe_all : ∀ f, f ≠ C →
      Disjoint (interior (place (fallbackParent f) '' (graph.prismDiagonalFace small_faces (fallbackParent f)).val))
        (interior (place f '' (graph.prismDiagonalFace small_faces f).val)) := by
    intro f not_root
    cases f
    · exact safe C (by decide) A (by decide) (by decide)
    · exact safeB
    · exact (not_root rfl).elim
    · exact safeD
    · exact safe C (by decide) E (by decide) (by decide)
    · exact safe E (by decide) F (by decide) (by decide)
  let net : graph.PrismFallbackDevelopment small_faces := {
    place := place
    rigid := rigid_all
    joined := joined_all
    hinge_safe := safe_all
    outward := fun f not_root =>
      (graph.prismDiagonalFace small_faces (fallbackParent f)).opposite_sides_of_nonoverlap
        (graph.prismDiagonalFace small_faces f) _ _ (rigid_all _) (rigid_all _)
        (joined_all f not_root) (safe_all f not_root) }
  refine ⟨net, ?_⟩
  intro f hf g hg different
  change Disjoint (interior (place f '' _)) (interior (place g '' _))
  rw [on_core f hf, on_core g hg]
  exact safe f hf g hg different

variable {graph small_faces}

/-- The remaining geometric work is precisely these seven unordered pairs. -/
theorem PrismFallbackDevelopment.hasEdgeUnfolding_of_star_core
    (net : graph.PrismFallbackDevelopment small_faces)
    (core_safe : ∀ f ∈ starCore, ∀ g ∈ starCore, f ≠ g →
      Disjoint (interior (net.place f '' (graph.prismDiagonalFace small_faces f).val))
        (interior (net.place g '' (graph.prismDiagonalFace small_faces g).val)))
    (remaining : ∀ f g, s(f, g) ∈ fallbackRemainingPairs →
      Disjoint (interior (net.place f '' (graph.prismDiagonalFace small_faces f).val))
        (interior (net.place g '' (graph.prismDiagonalFace small_faces g).val))) : P.HasEdgeUnfolding := by
  apply net.hasEdgeUnfolding prism_kind
  intro f g different not_hinge
  rcases (by decide : ∀ f g, f ≠ g → ¬ fallbackHinges.Adj f g →
    (f ∈ starCore ∧ g ∈ starCore) ∨ s(f, g) ∈ fallbackRemainingPairs) f g different not_hinge with core | other
  · exact core_safe f core.1 g core.2 different
  · exact remaining f g other

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
