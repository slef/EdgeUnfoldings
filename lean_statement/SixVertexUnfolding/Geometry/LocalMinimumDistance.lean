import SixVertexUnfolding.Geometry.ActiveSourceNeighborhoods

/-! Intrinsic distance near an interior-face target is the minimum of
finitely many Euclidean distances to actual developed source copies. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- On a face neighborhood, intrinsic distance is exactly the minimum over the old target's active sources. -/
theorem local_minimum_distance (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ ∀ x ∈ V ∩ F.val,
      (∀ source ∈ P.activeSources a b F, P.surfaceDist a x ≤ dist source (P.faceCoordinates F x)) ∧
      ∃ source ∈ P.activeSources a b F, P.surfaceDist a x = dist source (P.faceCoordinates F x) := by
  obtain ⟨U, openU, bU, competitors⟩ := graph.active_source_competitors small_faces a b different F unique_face
  obtain ⟨W, openW, bW, selection⟩ := graph.active_source_distance_nearby small_faces a b different F unique_face
  refine ⟨U ∩ W, openU.inter openW, ⟨bU, bW⟩, ?_⟩
  intro x hx
  refine ⟨?_, selection x ⟨hx.1.2, F.subset_frontier hx.2⟩⟩
  intro source active
  obtain ⟨path, finite, length⟩ := competitors x ⟨hx.1.1, hx.2⟩ source active
  calc
    P.surfaceDist a x ≤ path.length.toReal := ENNReal.toReal_mono finite path.surfaceEDist_le_length
    _ = dist source (P.faceCoordinates F x) := length

include graph small_faces in
/-- The same formula as a least-element statement, with finiteness and nonemptiness explicit. -/
theorem finite_local_minimum_distance (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    (P.activeSources a b F).Finite ∧ (P.activeSources a b F).Nonempty ∧
      ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ ∀ x ∈ V ∩ F.val,
        IsLeast ((fun source => dist source (P.faceCoordinates F x)) '' P.activeSources a b F)
          (P.surfaceDist a x) := by
  obtain ⟨V, openV, bV, formula⟩ := graph.local_minimum_distance small_faces a b different F unique_face
  refine ⟨graph.activeSources_finite small_faces a b different F unique_face,
    graph.activeSources_nonempty small_faces a b different F unique_face, V, openV, bV, ?_⟩
  intro x hx
  obtain ⟨lower, source, active, equal⟩ := formula x hx
  refine ⟨⟨source, active, equal.symm⟩, ?_⟩
  rintro _ ⟨other, member, rfl⟩
  exact lower other member

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
