import SixVertexUnfolding.Geometry.PrismDiagonalIncidence
import SixVertexUnfolding.Geometry.PolygonPetal

/-! Construct the fixed fallback by attaching whole polygons outward:
A, B, E to C, then D, F to E. All five hinge-neighbor comparisons are proved.
The remaining face pairs are explicit obligations, not construction premises. -/

namespace SixVertexUnfolding.Prism

open FaceLabel

def fallbackParent : FaceLabel → FaceLabel
  | D | F => E
  | _ => C

theorem fallbackHinges_iff_parent (f g : FaceLabel) : fallbackHinges.Adj f g ↔
    (g ≠ C ∧ f = fallbackParent g) ∨ (f ≠ C ∧ g = fallbackParent f) := by
  revert f g
  decide

end SixVertexUnfolding.Prism

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- A concrete outward development of all six original faces along the fallback tree. -/
structure PrismFallbackDevelopment where
  place : FaceLabel → Space →ᵃ[ℝ] Plane
  rigid : ∀ f, ∀ x ∈ (graph.prismDiagonalFace small_faces f).val,
    ∀ y ∈ (graph.prismDiagonalFace small_faces f).val, dist (place f x) (place f y) = dist x y
  joined : ∀ f, f ≠ C → Set.EqOn (place (fallbackParent f)) (place f)
    ((graph.prismDiagonalFace small_faces (fallbackParent f)).val ∩
      (graph.prismDiagonalFace small_faces f).val)
  hinge_safe : ∀ f, f ≠ C →
    Disjoint (interior (place (fallbackParent f) '' (graph.prismDiagonalFace small_faces (fallbackParent f)).val))
      (interior (place f '' (graph.prismDiagonalFace small_faces f).val))
  outward : ∀ f, f ≠ C →
    ∀ a ∈ ((graph.prismDiagonalFace small_faces (fallbackParent f)).val ∩
      (graph.prismDiagonalFace small_faces f).val) ∩ (P.vertices : Set Space),
    ∀ b ∈ ((graph.prismDiagonalFace small_faces (fallbackParent f)).val ∩
      (graph.prismDiagonalFace small_faces f).val) ∩ (P.vertices : Set Space), a ≠ b →
    ∀ x ∈ (graph.prismDiagonalFace small_faces (fallbackParent f)).val,
    ∀ y ∈ (graph.prismDiagonalFace small_faces f).val,
      OppositeHingeSides (place (fallbackParent f) a) (place (fallbackParent f) b)
        (place (fallbackParent f) x) (place f y)

variable (prism_kind : graph.kind = .prismDiagonal)
include prism_kind

/-- The five outward attachments exist for every convex realization of this graph. -/
theorem exists_prism_fallback_development : Nonempty (graph.PrismFallbackDevelopment small_faces) := by
  obtain ⟨pC, rigidC⟩ := (graph.prismDiagonalFace small_faces C).exists_rigid_placement
  obtain ⟨pA, rigidA, joinedA, safeA, _, outwardA⟩ :=
    (graph.prismDiagonalFace small_faces C).exists_polygon_petal (graph.prismDiagonalFace small_faces A)
      (graph.prism_fallback_original_hinge small_faces prism_kind C A (by decide)) pC rigidC
  obtain ⟨pB, rigidB, joinedB, safeB, _, outwardB⟩ :=
    (graph.prismDiagonalFace small_faces C).exists_polygon_petal (graph.prismDiagonalFace small_faces B)
      (graph.prism_fallback_original_hinge small_faces prism_kind C B (by decide)) pC rigidC
  obtain ⟨pE, rigidE, joinedE, safeE, _, outwardE⟩ :=
    (graph.prismDiagonalFace small_faces C).exists_polygon_petal (graph.prismDiagonalFace small_faces E)
      (graph.prism_fallback_original_hinge small_faces prism_kind C E (by decide)) pC rigidC
  obtain ⟨pD, rigidD, joinedD, safeD, _, outwardD⟩ :=
    (graph.prismDiagonalFace small_faces E).exists_polygon_petal (graph.prismDiagonalFace small_faces D)
      (graph.prism_fallback_original_hinge small_faces prism_kind E D (by decide)) pE rigidE
  obtain ⟨pF, rigidF, joinedF, safeF, _, outwardF⟩ :=
    (graph.prismDiagonalFace small_faces E).exists_polygon_petal (graph.prismDiagonalFace small_faces F)
      (graph.prism_fallback_original_hinge small_faces prism_kind E F (by decide)) pE rigidE
  let place : FaceLabel → Space →ᵃ[ℝ] Plane
    | A => pA | B => pB | C => pC | D => pD | E => pE | F => pF
  refine ⟨⟨place, ?_, ?_, ?_, ?_⟩⟩
  · intro f
    cases f
    exacts [rigidA, rigidB, rigidC, rigidD, rigidE, rigidF]
  · intro f not_root
    cases f
    exacts [joinedA, joinedB, (not_root rfl).elim, joinedD, joinedE, joinedF]
  · intro f not_root
    cases f
    exacts [safeA, safeB, (not_root rfl).elim, safeD, safeE, safeF]
  · intro f not_root
    cases f
    exacts [outwardA, outwardB, (not_root rfl).elim, outwardD, outwardE, outwardF]

omit prism_kind
variable {graph small_faces}
variable (net : graph.PrismFallbackDevelopment small_faces)

/-- Hinge agreement also holds when a retained edge is read in the reverse direction. -/
theorem PrismFallbackDevelopment.joined_on_hinge (f g : FaceLabel) (edge : fallbackHinges.Adj f g) :
    Set.EqOn (net.place f) (net.place g)
      ((graph.prismDiagonalFace small_faces f).val ∩ (graph.prismDiagonalFace small_faces g).val) := by
  rcases (fallbackHinges_iff_parent f g).mp edge with ⟨not_root, rfl⟩ | ⟨not_root, rfl⟩
  · exact net.joined g not_root
  · intro x hx
    exact (net.joined f not_root ⟨hx.2, hx.1⟩).symm

/-- Five of the fifteen whole-face comparisons are already certified by outward attachment. -/
theorem PrismFallbackDevelopment.hinge_nonoverlap (f g : FaceLabel) (edge : fallbackHinges.Adj f g) :
    Disjoint (interior (net.place f '' (graph.prismDiagonalFace small_faces f).val))
      (interior (net.place g '' (graph.prismDiagonalFace small_faces g).val)) := by
  rcases (fallbackHinges_iff_parent f g).mp edge with ⟨not_root, rfl⟩ | ⟨not_root, rfl⟩
  · exact net.hinge_safe g not_root
  · exact (net.hinge_safe f not_root).symm

include prism_kind in
/-- Once the ten non-hinge face pairs are separated, this concrete development proves
an edge unfolding in the unchanged public definition. -/
theorem PrismFallbackDevelopment.hasEdgeUnfolding
    (other_pairs : ∀ f g, f ≠ g → ¬ fallbackHinges.Adj f g →
      Disjoint (interior (net.place f '' (graph.prismDiagonalFace small_faces f).val))
        (interior (net.place g '' (graph.prismDiagonalFace small_faces g).val))) : P.HasEdgeUnfolding := by
  let index := graph.prismDiagonalFaceEquiv small_faces prism_kind
  obtain ⟨hinges, tree, original, named⟩ := graph.exists_prism_fallback_hinges small_faces prism_kind
  refine ⟨⟨fun F => net.place (index.symm F), hinges, tree, fun _ _ edge => original edge, ?_, ?_, ?_⟩⟩
  · intro F
    obtain ⟨f, rfl⟩ := index.surjective F
    simpa only [index.symm_apply_apply] using net.rigid f
  · intro F G edge
    obtain ⟨f, rfl⟩ := index.surjective F
    obtain ⟨g, rfl⟩ := index.surjective G
    have adjacent := (named f g).mp edge
    simpa only [index.symm_apply_apply] using net.joined_on_hinge f g adjacent
  · intro F G different
    obtain ⟨f, rfl⟩ := index.surjective F
    obtain ⟨g, rfl⟩ := index.surjective G
    have fg : f ≠ g := fun same => different (congrArg index same)
    by_cases adjacent : fallbackHinges.Adj f g
    · simpa only [index.symm_apply_apply] using net.hinge_nonoverlap f g adjacent
    · simpa only [index.symm_apply_apply] using other_pairs f g fg adjacent

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
