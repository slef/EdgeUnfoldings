import SixVertexUnfolding.Geometry.SourceBisectors
import SixVertexUnfolding.Geometry.LocalFacetHalfspaces

/-! Two Euclidean source-distance functions cannot touch at an interior
point while one stays below the other nearby, unless their sources coincide. -/

namespace SixVertexUnfolding

open Set

/-- A local distance comparison that is an equality at an interior point identifies the two planar sites. -/
theorem local_source_comparison_eq (p q x : Plane) (U : Set Plane) (openU : IsOpen U) (xU : x ∈ U)
    (comparison : ∀ y ∈ U, dist p y ≤ dist q y) (equal : dist p x = dist q x) : p = q := by
  by_contra different
  let height := innerSL ℝ (q - p)
  have onto : Function.Surjective height := plane_inner_height_surjective (sub_ne_zero.mpr (fun h => different h.symm))
  have inclusion : U ⊆ height ⁻¹' Iic ((‖q‖ ^ 2 - ‖p‖ ^ 2) / 2) := by
    intro y hy
    exact (nearer_site_iff_halfplane y p q).mp (by simpa only [dist_comm] using comparison y hy)
  have strict := interior_mono inclusion
  rw [openU.interior_eq, height.interior_preimage onto, interior_Iic] at strict
  exact (strict xU).ne ((equal_site_distances_iff_bisector p q x).mp equal)

namespace ConvexPolyhedron

/-- The same rigidity applies within a face at a point incident to no other face. -/
theorem local_face_source_comparison_eq (P : ConvexPolyhedron) (F : P.Face) (x : Space) (xF : x ∈ F.val)
    (unique : ∀ G : P.Face, x ∈ G.val → G = F) (p q : Plane)
    (U : Set Space) (openU : IsOpen U) (xU : x ∈ U)
    (comparison : ∀ y ∈ U ∩ F.val, dist p (P.faceCoordinates F y) ≤ dist q (P.faceCoordinates F y))
    (equal : dist p (P.faceCoordinates F x) = dist q (P.faceCoordinates F x)) : p = q := by
  obtain ⟨center, inside⟩ := P.solid
  obtain ⟨facets⟩ := P.exists_normalized_facets inside
  obtain ⟨O, openO, xO, plane⟩ := facets.single_face_local_plane F xF unique
  obtain ⟨lift, in_plane, coordinate, inverse, _⟩ :=
    F.exists_rigid_plane_inverse (P.faceCoordinates F) (P.faceCoordinates_rigid F)
  apply local_source_comparison_eq p q (P.faceCoordinates F x) (lift ⁻¹' (U ∩ O))
    ((openU.inter openO).preimage lift.continuous_of_finiteDimensional)
    (by simpa only [mem_preimage, inverse x (subset_affineSpan ℝ _ xF)] using (show x ∈ U ∩ O from ⟨xU, xO⟩))
    ?_ equal
  intro y hy
  have lifted : lift y ∈ F.val := by
    have member : lift y ∈ O ∩ (affineSpan ℝ F.val : Set Space) := ⟨hy.2, in_plane y⟩
    rw [← plane] at member
    exact member.2
  simpa only [coordinate] using comparison (lift y) ⟨hy.1, lifted⟩

end ConvexPolyhedron
end SixVertexUnfolding
