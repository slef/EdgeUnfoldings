import SixVertexUnfolding.Geometry.SegmentFacetIncidence
import SixVertexUnfolding.Geometry.FaceLineCutPersistence
import SixVertexUnfolding.Geometry.EdgeLineCutPersistence

/-! Finitely many source-distance crossings control the whole interior
of any nondegenerate straight segment contained in an original facet. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Except at finitely many parameters, every cut point has a whole neighboring cut interval. -/
theorem segment_cut_crossings (a : frontier P.body) (F : P.Face)
    (curve : ℝ →ᵃ[ℝ] Space) (injective : Function.Injective curve)
    {l r : ℝ} (ordered : l < r) (left : curve l ∈ F.val) (right : curve r ∈ F.val) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ t ∈ Ioo l r, t ∉ E → curve t ∈ P.multipleRouteLocus a →
      ∃ J : Set ℝ, IsOpen J ∧ t ∈ J ∧ ∀ s ∈ J ∩ Icc l r, curve s ∈ P.multipleRouteLocus a := by
  let m := (l + r) / 2
  have middle : m ∈ Ioo l r := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have in_face := affine_interval_in_face F curve ordered.le left right
  have in_body_left := F.subset_body left
  have in_body_right := F.subset_body right
  have no_vertex {t : ℝ} (ht : t ∈ Ioo l r) : curve t ∉ P.vertices :=
    P.affine_segment_nonvertex curve injective in_body_left in_body_right ht
  rcases P.nonvertex_incident_facets (F.subset_frontier (in_face m ⟨middle.1.le, middle.2.le⟩))
    (no_vertex middle) with ⟨H, _, unique⟩ | ⟨H, G, shared, target, _⟩
  · have same : F = H := unique F (in_face m ⟨middle.1.le, middle.2.le⟩)
    subst H
    let line := (P.faceCoordinates F).comp curve
    refine ⟨lineSourceCrossings (P.sourceImages a F) line,
      lineSourceCrossings_finite _ (P.sourceImages_finite a F) line, ?_⟩
    intro t ht regular cut
    have unique_t (H : P.Face) (member : curve t ∈ H.val) : H = F := by
      exact unique H (facet_contains_affine_interval H curve in_body_left in_body_right ht member
        m ⟨middle.1.le, middle.2.le⟩)
    obtain ⟨J, openJ, tJ, persists⟩ := graph.face_cut_persists_along_line small_faces a F curve
      (in_face t ⟨ht.1.le, ht.2.le⟩) unique_t cut regular
    exact ⟨J, openJ, tJ, fun s hs => persists s hs.1 (in_face s hs.2)⟩
  · have in_H := facet_contains_affine_interval H curve in_body_left in_body_right middle target.1
    have in_G := facet_contains_affine_interval G curve in_body_left in_body_right middle target.2
    obtain ⟨center, inside⟩ := P.solid
    obtain ⟨facets⟩ := P.exists_normalized_facets inside
    obtain ⟨chart⟩ := exists_edge_folding facets H G shared
    let line := chart.left.comp curve
    refine ⟨lineSourceCrossings (chart.sourceImages a) line,
      lineSourceCrossings_finite _ (chart.sourceImages_finite a) line, ?_⟩
    intro t ht regular cut
    obtain ⟨J, openJ, tJ, persists⟩ := chart.cut_persists_along_line graph small_faces a shared curve
      ⟨in_H t ⟨ht.1.le, ht.2.le⟩, in_G t ⟨ht.1.le, ht.2.le⟩⟩ (no_vertex ht) cut regular
    exact ⟨J, openJ, tJ, fun s hs => persists s hs.1 (in_H s hs.2)⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
