import SixVertexUnfolding.Geometry.LineVoronoiPersistence
import SixVertexUnfolding.Geometry.LocalVoronoiCutLocus

/-! Along a straight line in an original face, membership in the cut locus
persists near a cut point unless two candidate source distances have an
isolated crossing there. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem face_cut_persists_along_line (a : frontier P.body) (F : P.Face)
    (curve : ℝ →ᵃ[ℝ] Space) {t : ℝ} (target : curve t ∈ F.val)
    (unique : ∀ G : P.Face, curve t ∈ G.val → G = F)
    (cut : curve t ∈ P.multipleRouteLocus a)
    (regular : t ∉ lineSourceCrossings (P.sourceImages a F) ((P.faceCoordinates F).comp curve)) :
    ∃ J : Set ℝ, IsOpen J ∧ t ∈ J ∧ ∀ s ∈ J, curve s ∈ F.val → curve s ∈ P.multipleRouteLocus a := by
  let b : frontier P.body := ⟨curve t, F.subset_frontier target⟩
  have different : a ≠ b := ((P.multiple_routes_iff_fiber a b).mp cut).1
  obtain ⟨V, openV, bV, diagram⟩ := graph.local_voronoi_cut_locus small_faces a b different F unique
  have contained := graph.activeSources_subset small_faces a b different F unique
  have common (p : Plane) (hp : p ∈ P.activeSources a b F) (q : Plane) (hq : q ∈ P.activeSources a b F) :
      dist p (((P.faceCoordinates F).comp curve) t) = dist q (((P.faceCoordinates F).comp curve) t) :=
    (P.activeSource_distance a b F p hp).symm.trans (P.activeSource_distance a b F q hq)
  have all_tied := voronoi_ties_persist_on_line (P.sourceImages a F) (P.activeSources a b F)
    contained ((P.faceCoordinates F).comp curve) regular common ((diagram _ ⟨bV, target⟩).mp cut)
  exact ⟨curve ⁻¹' V, openV.preimage curve.continuous_of_finiteDimensional, bV,
    fun s hs in_face => (diagram _ ⟨hs, in_face⟩).mpr (all_tied s)⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
