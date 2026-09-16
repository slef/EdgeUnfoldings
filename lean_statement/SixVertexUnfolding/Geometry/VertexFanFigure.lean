import SixVertexUnfolding.Geometry.VertexFaceFan
import SixVertexUnfolding.Geometry.FourRayFan
import SixVertexUnfolding.Geometry.FiveRayFan

/-! The ordered original edge rays form a supported transverse figure.
This construction depends only on the local face fan, not a global graph. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open Set

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n) (figure : P.VertexFigure pole)

noncomputable def ray (i : Fin n) : Space := figure.direction (fan.neighbor i)

theorem ray_injective : Function.Injective (fan.ray figure) := by
  intro i j same
  apply fan.neighbors_distinct
  apply Subtype.ext
  exact figure.direction_injective
    ⟨(fan.neighbor i).property, fan.neighbor_ne_pole i⟩
    ⟨(fan.neighbor j).property, fan.neighbor_ne_pole j⟩ same

theorem ray_height (i : Fin n) : -(inner ℝ figure.normal (fan.ray figure i)) = 1 := by
  rw [ray, figure.direction_height (fan.neighbor i).property (fan.neighbor_ne_pole i)]
  norm_num

theorem rays_span : Submodule.span ℝ (range (fan.ray figure)) = ⊤ := by
  apply top_unique
  rw [← figure.corners_span]
  apply Submodule.span_mono
  intro x corner
  obtain ⟨w, adjacent, at_x⟩ := figure.corner_is_neighbor corner
  obtain ⟨i, same⟩ := fan.order.surjective ⟨w, adjacent⟩
  refine ⟨i, ?_⟩
  change figure.direction (fan.order i).val = x
  rw [same]
  exact at_x

theorem ray_angle (i : Fin n) :
    InnerProductGeometry.angle (fan.ray figure i) (fan.ray figure (i + 1)) =
      EuclideanGeometry.angle (fan.neighbor i : Space) pole (fan.neighbor (i + 1)) := by
  rw [ray, ray, VertexFigure.direction, VertexFigure.direction,
    InnerProductGeometry.angle_smul_left_of_pos _ _
      (inv_pos.mpr (figure.gap_pos (fan.neighbor i).property (fan.neighbor_ne_pole i))),
    InnerProductGeometry.angle_smul_right_of_pos _ _
      (inv_pos.mpr (figure.gap_pos (fan.neighbor (i + 1)).property (fan.neighbor_ne_pole (i + 1))))]
  rfl

variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- A listed face contains precisely its two listed edge neighbors of the pole. -/
theorem neighbor_mem_face_iff (i j : Fin n) :
    (fan.neighbor j : Space) ∈ (fan.face i).val ↔ j = i ∨ j = i + 1 := by
  obtain ⟨c, _, _, _, exhaust⟩ := (fan.face i).exists_other_corner_neighbor (small_faces _)
    pole (fan.neighbor i) (fan.adjacent i) (fan.pole_mem i) (fan.left_mem i)
  have right_eq : fan.neighbor (i + 1) = c :=
    (exhaust _ (fan.right_mem i) (fan.adjacent (i + 1))).resolve_left (fan.successive_distinct i).symm
  constructor
  · intro member
    rcases exhaust _ member (fan.adjacent j) with first | last
    · exact Or.inl (fan.neighbors_distinct first)
    · exact Or.inr (fan.neighbors_distinct (last.trans right_eq.symm))
  · rintro (rfl | rfl)
    exacts [fan.left_mem _, fan.right_mem _]

include small_faces in
/-- The original facet normal supports each side strictly away from its endpoints. -/
theorem ray_side_exists (i : Fin n) : ∃ side : Space →ₗ[ℝ] ℝ,
    side ≠ 0 ∧ side (fan.ray figure i) = 0 ∧ side (fan.ray figure (i + 1)) = 0 ∧
      (∀ j, side (fan.ray figure j) ≤ 0) ∧
      ∀ j, j ≠ i → j ≠ i + 1 → side (fan.ray figure j) < 0 := by
  obtain ⟨_, normal, level, nonzero, support, face_eq⟩ := (fan.face i).property
  have pole_level : inner ℝ normal (pole : Space) = level := (face_eq ▸ fan.pole_mem i).2
  have difference (j : Fin n) : inner ℝ normal (fan.ray figure j) =
      (figure.gap (fan.neighbor j))⁻¹ * (inner ℝ normal (fan.neighbor j : Space) - level) := by
    rw [ray, VertexFigure.direction, inner_smul_right, inner_sub_right, pole_level]
  have on_side (j : Fin n) (member : (fan.neighbor j : Space) ∈ (fan.face i).val) :
      inner ℝ normal (fan.ray figure j) = 0 := by
    have at_level : inner ℝ normal (fan.neighbor j : Space) = level := (face_eq ▸ member).2
    rw [difference, at_level, sub_self, mul_zero]
  refine ⟨(innerSL ℝ normal).toLinearMap, ?_, on_side i (fan.left_mem i),
    on_side (i + 1) (fan.right_mem i), ?_, ?_⟩
  · intro zero
    have self_zero := congrArg (fun f : Space →ₗ[ℝ] ℝ => f normal) zero
    change inner ℝ normal normal = 0 at self_zero
    exact nonzero (inner_self_eq_zero.mp self_zero)
  · intro j
    change inner ℝ normal (fan.ray figure j) ≤ 0
    rw [difference]
    exact mul_nonpos_of_nonneg_of_nonpos
      (inv_nonneg.mpr (figure.gap_pos (fan.neighbor j).property (fan.neighbor_ne_pole j)).le)
      (sub_nonpos.mpr (support _ (P.vertices_subset_body (fan.neighbor j).property)))
  · intro j not_left not_right
    have outside : (fan.neighbor j : Space) ∉ (fan.face i).val := by
      rw [fan.neighbor_mem_face_iff small_faces]
      exact not_or_intro not_left not_right
    have below : inner ℝ normal (fan.neighbor j : Space) < level := by
      apply (support _ (P.vertices_subset_body (fan.neighbor j).property)).lt_of_ne
      intro equal
      apply outside
      rw [face_eq]
      exact ⟨P.vertices_subset_body (fan.neighbor j).property, equal⟩
    change inner ℝ normal (fan.ray figure j) < 0
    rw [difference]
    exact mul_neg_of_pos_of_neg
      (inv_pos.mpr (figure.gap_pos (fan.neighbor j).property (fan.neighbor_ne_pole j)))
      (sub_neg.mpr below)

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
