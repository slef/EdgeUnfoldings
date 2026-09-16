import SixVertexUnfolding.Geometry.RadialHinges
import SixVertexUnfolding.Geometry.HingeIsometries
import SixVertexUnfolding.Geometry.PlanarSectors

/-! Four triangles joined successively around one vertex occupy consecutive angular sectors. -/

namespace SixVertexUnfolding

open EuclideanGeometry Real

/-- Four nondegenerate triangles, with each new triangle unfolded outward from the preceding one. -/
structure FourTriangleChain where
  center : Plane
  ray : Fin 5 → Plane
  noncollinear : ∀ i : Fin 4, ¬ Collinear ℝ ({center, ray i.castSucc, ray i.succ} : Set Plane)
  outward : ∀ i : Fin 3,
    OppositeHingeSides center (ray i.succ.castSucc) (ray i.castSucc.castSucc) (ray i.succ.succ)

namespace FourTriangleChain

variable (chain : FourTriangleChain)

noncomputable def corner (i : Fin 4) : ℝ := angle (chain.ray i.castSucc) chain.center (chain.ray i.succ)

noncomputable def directionAngle : Fin 5 → ℝ :=
  ![0, chain.corner 0, chain.corner 0 + chain.corner 1,
    chain.corner 0 + chain.corner 1 + chain.corner 2,
    chain.corner 0 + chain.corner 1 + chain.corner 2 + chain.corner 3]

noncomputable def radius (i : Fin 5) : ℝ := dist chain.center (chain.ray i)

noncomputable def target (i : Fin 5) : Plane := chain.radius i • direction (chain.directionAngle i)

def triangle (i : Fin 4) : Set Plane :=
  convexHull ℝ ({chain.center, chain.ray i.castSucc, chain.ray i.succ} : Set Plane)

theorem corner_pos (i : Fin 4) : 0 < chain.corner i := by
  apply angle_pos_of_not_collinear
  simpa only [Set.insert_comm] using chain.noncollinear i

theorem corner_lt_pi (i : Fin 4) : chain.corner i < π := by
  apply angle_lt_pi_of_not_collinear
  simpa only [Set.insert_comm] using chain.noncollinear i

theorem radius_pos (i : Fin 5) : 0 < chain.radius i := by
  apply dist_pos.mpr
  have first (j : Fin 4) : chain.center ≠ chain.ray j.castSucc := by
    intro same
    apply chain.noncollinear j
    simpa [same] using collinear_pair ℝ (chain.ray j.castSucc) (chain.ray j.succ)
  have last : chain.center ≠ chain.ray 4 := by
    intro same
    apply chain.noncollinear 3
    simpa [same, Set.insert_comm] using collinear_pair ℝ (chain.ray 3) (chain.ray 4)
  fin_cases i
  · exact first 0
  · exact first 1
  · exact first 2
  · exact first 3
  · exact last

theorem directionAngle_step (i : Fin 4) :
    chain.directionAngle i.succ - chain.directionAngle i.castSucc = chain.corner i := by
  fin_cases i <;> simp [directionAngle]

theorem directionAngle_strictMono : StrictMono chain.directionAngle := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have := chain.directionAngle_step i
  have := chain.corner_pos i
  linarith

theorem target_radius (i : Fin 5) : dist 0 (chain.target i) = chain.radius i :=
  polar_radius _ _ (chain.radius_pos i).le

theorem target_base (i : Fin 4) :
    dist (chain.target i.castSucc) (chain.target i.succ) = dist (chain.ray i.castSucc) (chain.ray i.succ) := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [target, target, polar_distance_sq, chain.directionAngle_step]
  have cosine_law := law_cos (chain.ray i.castSucc) chain.center (chain.ray i.succ)
  simp only [← sq, dist_comm (chain.ray i.castSucc) chain.center,
    dist_comm (chain.ray i.succ) chain.center] at cosine_law
  exact cosine_law.symm

theorem target_noncollinear (i : Fin 4) :
    ¬ Collinear ℝ ({0, chain.target i.castSucc, chain.target i.succ} : Set Plane) := by
  apply radial_triangle_noncollinear _ _ _ _ (chain.radius_pos _) (chain.radius_pos _)
  · rw [chain.directionAngle_step]; exact chain.corner_pos i
  · rw [chain.directionAngle_step]; exact chain.corner_lt_pi i

theorem target_outward (i : Fin 3) :
    OppositeHingeSides 0 (chain.target i.succ.castSucc)
      (chain.target i.castSucc.castSucc) (chain.target i.succ.succ) := by
  apply radial_hinge_opposite _ _ _ _ _ _ (chain.radius_pos _) (chain.radius_pos _) (chain.radius_pos _)
  · rw [show i.succ.castSucc = i.castSucc.succ from rfl, chain.directionAngle_step]
    exact chain.corner_pos _
  · rw [show i.succ.castSucc = i.castSucc.succ from rfl, chain.directionAngle_step]
    exact chain.corner_lt_pi _
  · rw [chain.directionAngle_step]; exact chain.corner_pos _
  · rw [chain.directionAngle_step]; exact chain.corner_lt_pi _

/-- Once two successive rays are aligned, the outward-side condition fixes the next ray. -/
theorem motion_next (motion : Plane ≃ᵃⁱ[ℝ] Plane) (at_center : motion chain.center = 0)
    (i : Fin 3) (previous : motion (chain.ray i.castSucc.castSucc) = chain.target i.castSucc.castSucc)
    (shared : motion (chain.ray i.succ.castSucc) = chain.target i.succ.castSucc) :
    motion (chain.ray i.succ.succ) = chain.target i.succ.succ := by
  apply outward_point_unique 0 (chain.target i.succ.castSucc) (chain.target i.castSucc.castSucc)
  · have reorder : ({0, chain.target i.succ.castSucc, chain.target i.castSucc.castSucc} : Set Plane) =
        {0, chain.target i.castSucc.castSucc, chain.target i.succ.castSucc} := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [reorder]
    exact chain.target_noncollinear i.castSucc
  · rw [← at_center, motion.dist_map, at_center, chain.target_radius]
    rfl
  · rw [← shared, motion.dist_map, shared, chain.target_base]
  · have side := (oppositeHingeSides_motion motion _ _ _ _).mpr (chain.outward i)
    simpa only [at_center, previous, shared] using side
  · exact chain.target_outward i

/-- The entire four-triangle chain has one common rigid coordinate frame with increasing polar directions. -/
theorem exists_radial_motion : ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane,
    motion chain.center = 0 ∧ ∀ i, motion (chain.ray i) = chain.target i := by
  obtain ⟨motion, at_center, first, second⟩ := exists_plane_motion_triangle chain.center (chain.ray 0)
    (chain.ray 1) 0 (chain.target 0) (chain.target 1)
    (dist_pos.mp (by rw [chain.target_radius]; exact chain.radius_pos 0))
    (chain.target_radius 0).symm (chain.target_radius 1).symm (chain.target_base 0).symm
  have third := chain.motion_next motion at_center 0 first second
  have fourth := chain.motion_next motion at_center 1 second third
  have fifth := chain.motion_next motion at_center 2 third fourth
  refine ⟨motion, at_center, ?_⟩
  intro i
  fin_cases i
  · exact first
  · exact second
  · exact third
  · exact fourth
  · exact fifth

end FourTriangleChain
end SixVertexUnfolding
