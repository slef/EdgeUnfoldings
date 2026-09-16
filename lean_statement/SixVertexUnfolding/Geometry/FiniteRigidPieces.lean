import SixVertexUnfolding.Definitions
import SixVertexUnfolding.Geometry.FiniteSelectionContinuity

/-! Retain the finite rigid inverse formulas of a triangle development.
Continuity excludes every incompatible formula near a chosen point, so
distances from that point are exactly preserved in a neighborhood. -/

namespace SixVertexUnfolding

open Set Filter Topology

/-- A folding selects, point by point, from finitely many rigid plane maps. -/
def HasFiniteRigidPieces (region : Set Plane) (fold : region → Space) : Prop :=
  ∃ maps : Set (Plane →ᵃ[ℝ] Space), maps.Finite ∧
    (∀ f ∈ maps, Isometry f) ∧ ∀ x, ∃ f ∈ maps, fold x = f x

namespace HasFiniteRigidPieces

variable {region : Set Plane} {fold : region → Space}

/-- A finite indexed family supplies the rigid-piece property. -/
theorem of_family {ι : Type*} [Finite ι] (maps : ι → Plane →ᵃ[ℝ] Space)
    (rigid : ∀ i, Isometry (maps i)) (selected : ∀ x, ∃ i, fold x = maps i x) :
    HasFiniteRigidPieces region fold := by
  refine ⟨range maps, finite_range maps, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact rigid i
  · intro x
    obtain ⟨i, agrees⟩ := selected x
    exact ⟨maps i, mem_range_self i, agrees⟩

/-- Near any point, every active rigid formula also agrees at the point itself. -/
theorem nearby_pieces (pieces : HasFiniteRigidPieces region fold)
    (continuous_fold : Continuous fold) (x : region) :
    ∀ᶠ y in 𝓝 x, ∃ f : Plane →ᵃ[ℝ] Space,
      Isometry f ∧ fold y = f y ∧ fold x = f x := by
  obtain ⟨maps, finite_maps, rigid, selected⟩ := pieces
  letI : Finite maps := finite_maps.to_subtype
  have near := finite_selection_nearby_pieces univ fold
    (fun f : maps => fun y : region => f.val y) continuous_fold.continuousOn
    (fun f => ((rigid f.val f.property).continuous.comp continuous_subtype_val).continuousOn)
    x (mem_univ x)
  simp only [nhdsWithin_univ] at near
  filter_upwards [near] with y hy
  obtain ⟨f, member, at_y⟩ := selected y
  exact ⟨f, rigid f member, at_y, hy ⟨f, member⟩ at_y⟩

/-- This is exact local radial distance preservation, including at triangle corners. -/
theorem local_radial_distance (pieces : HasFiniteRigidPieces region fold)
    (continuous_fold : Continuous fold) (x : region) :
    ∃ ε > 0, ∀ y : region, dist (y : Plane) x < ε →
      dist (fold y) (fold x) = dist (y : Plane) x := by
  have near : ∀ᶠ y in 𝓝 x, dist (fold y) (fold x) = dist y x := by
    filter_upwards [pieces.nearby_pieces continuous_fold x] with y hy
    obtain ⟨f, rigid, at_y, at_x⟩ := hy
    rw [at_y, at_x]
    exact rigid.dist_eq y x
  obtain ⟨ε, positive, inside⟩ := Metric.eventually_nhds_iff.mp near
  exact ⟨ε, positive, fun y hy => inside hy⟩

end HasFiniteRigidPieces
end SixVertexUnfolding
