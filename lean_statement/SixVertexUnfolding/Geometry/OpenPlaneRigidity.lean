import SixVertexUnfolding.Geometry.PlaneDistanceRigidity
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-! On a nonempty open planar region, an isometry is one rigid motion.
An affine basis inside the region supplies the three required distance anchors. -/

namespace SixVertexUnfolding

open Set

/-- Every nonempty planar open set contains three noncollinear points. -/
theorem open_plane_contains_triangle (region : Set Plane) (open_region : IsOpen region)
    (nonempty : region.Nonempty) :
    ∃ a b c : region, ¬ Collinear ℝ ({(a : Plane), (b : Plane), (c : Plane)} : Set Plane) := by
  classical
  obtain ⟨s, inside, independent, spans⟩ := open_region.exists_subset_affineIndependent_span_eq_top nonempty
  let basis : AffineBasis s ℝ Plane := {
    toFun := Subtype.val
    ind' := independent
    tot' := by simpa only [Subtype.range_coe_subtype, setOf_mem_eq] using spans }
  letI : Finite s := basis.finite
  letI : Fintype s := Fintype.ofFinite s
  have count : Fintype.card s = 3 := by simpa [Plane] using basis.card_eq_finrank_add_one
  let e : s ≃ Fin 3 := Fintype.equivFinOfCardEq count
  let triangle := basis.reindex e
  have triangle_inside (i : Fin 3) : triangle i ∈ region := inside (e.symm i).property
  refine ⟨⟨triangle 0, triangle_inside 0⟩, ⟨triangle 1, triangle_inside 1⟩,
    ⟨triangle 2, triangle_inside 2⟩, ?_⟩
  apply affineIndependent_iff_not_collinear_set.mp
  have functions : ![triangle 0, triangle 1, triangle 2] = triangle := by
    funext i; fin_cases i <;> rfl
  rw [functions]
  exact triangle.ind

/-- Any distance-preserving planar map on a nonempty open region is a rigid motion there. -/
theorem open_planar_isometry_agrees_with_motion (region : Set Plane) (open_region : IsOpen region)
    (nonempty : region.Nonempty) (f : region → Plane) (isometric : Isometry f) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, ∀ x : region, motion x = f x := by
  obtain ⟨a, b, c, noncollinear⟩ := open_plane_contains_triangle region open_region nonempty
  exact planar_isometry_agrees_with_motion region f isometric a b c noncollinear

end SixVertexUnfolding
