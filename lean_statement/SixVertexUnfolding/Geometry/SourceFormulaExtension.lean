import SixVertexUnfolding.Geometry.UniqueRouteSourceDistance
import SixVertexUnfolding.Geometry.LocalFacetHalfspaces

/-! Extend a local source-distance formula through a final face. The
competitors are actual shortest prefixes followed by straight face paths. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set
open scoped ENNReal

/-- A local source formula at an interior face point supplies exact-length competitors near any later point on its ray. -/
theorem source_formula_extension (P : ConvexPolyhedron) {a b z : Space}
    (source_on : a ∈ frontier P.body) (F : P.Face) (zF : z ∈ F.val) (bF : b ∈ F.val)
    (unique : ∀ G : P.Face, z ∈ G.val → G = F) (source : Plane)
    (t : ℝ) (positive : 0 < t) (before : t < 1)
    (on_ray : P.faceCoordinates F z = AffineMap.lineMap source (P.faceCoordinates F b) t)
    (U : Set Space) (openU : IsOpen U) (zU : z ∈ U)
    (formula : ∀ x ∈ U ∩ frontier P.body, P.surfaceDist a x = dist source (P.faceCoordinates F x)) :
    ∃ V : Set Space, IsOpen V ∧ b ∈ V ∩ F.val ∧ ∀ x ∈ V ∩ F.val,
      ∃ path : P.SurfacePath a x, path.length ≠ ⊤ ∧ path.length.toReal = dist source (P.faceCoordinates F x) := by
  obtain ⟨center, inside⟩ := P.solid
  obtain ⟨facets⟩ := P.exists_normalized_facets inside
  obtain ⟨O, openO, zO, plane⟩ := facets.single_face_local_plane F zF unique
  obtain ⟨lift, in_plane, coordinate, inverse, _⟩ :=
    F.exists_rigid_plane_inverse (P.faceCoordinates F) (P.faceCoordinates_rigid F)
  let middle : Space → Space := fun x => lift (AffineMap.lineMap source (P.faceCoordinates F x) t)
  have continuous_middle : Continuous middle := lift.continuous_of_finiteDimensional.comp (by
    simp only [AffineMap.lineMap_apply_module]
    exact continuous_const.add (continuous_const.smul (P.faceCoordinates F).continuous_of_finiteDimensional))
  have middle_b : middle b = z := by
    dsimp [middle]
    rw [← on_ray, inverse z (subset_affineSpan ℝ _ zF)]
  refine ⟨middle ⁻¹' (U ∩ O), (openU.inter openO).preimage continuous_middle,
    ⟨by simpa only [mem_preimage, middle_b] using (show z ∈ U ∩ O from ⟨zU, zO⟩), bF⟩, ?_⟩
  intro x hx
  have middleF : middle x ∈ F.val := by
    have member : middle x ∈ O ∩ (affineSpan ℝ F.val : Set Space) := ⟨hx.1.2, in_plane _⟩
    rw [← plane] at member
    exact member.2
  obtain ⟨front, shortest, finite, _⟩ := P.exists_shortest_lipschitz_surface_path source_on (F.subset_frontier middleF)
  let last := SurfacePath.inFace F middleF hx.2
  have last_finite : last.length ≠ ⊤ := by rw [SurfacePath.inFace_length]; exact edist_ne_top _ _
  have front_length : front.length.toReal = dist source (P.faceCoordinates F (middle x)) := by
    rw [front.length_eq_surfaceEDist shortest]
    exact formula _ ⟨hx.1.1, F.subset_frontier middleF⟩
  have last_length : last.length.toReal = dist (P.faceCoordinates F (middle x)) (P.faceCoordinates F x) := by
    rw [SurfacePath.inFace_length, edist_dist, ENNReal.toReal_ofReal dist_nonneg,
      P.faceCoordinates_rigid F _ middleF _ hx.2]
  refine ⟨front.join last, front.join_finite last finite last_finite, ?_⟩
  calc
    (front.join last).length.toReal = (front.length + last.length).toReal := congrArg ENNReal.toReal (front.join_length last)
    _ = front.length.toReal + last.length.toReal := ENNReal.toReal_add finite last_finite
    _ = dist source (P.faceCoordinates F x) := by
      rw [front_length, last_length, show P.faceCoordinates F (middle x) =
        AffineMap.lineMap source (P.faceCoordinates F x) t from coordinate _,
        dist_left_lineMap, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg positive.le, abs_of_nonneg (sub_nonneg.mpr before.le)]
      ring

end SixVertexUnfolding.ConvexPolyhedron
