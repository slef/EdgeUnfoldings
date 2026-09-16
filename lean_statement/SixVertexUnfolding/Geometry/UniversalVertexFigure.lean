import SixVertexUnfolding.Geometry.UniversalVertexOrder
import SixVertexUnfolding.Geometry.VertexFigure
import SixVertexUnfolding.Geometry.FiveRayFan
import SixVertexUnfolding.Geometry.UniversalVertexFanCoverage

/-! Construct the supported five-ray figure from the actual universal
vertex, its cyclic original faces, and their supporting plane normals. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- The universal vertex has an actual supported five-ray transverse figure. -/
theorem universal_vertex_five_ray_figure (P : ConvexPolyhedron) (size : P.vertices.card = 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v)
    (figure : P.VertexFigure source) :
    ∃ fan : FiveRayFan, ∃ order : Fin 5 ≃ {v : P.Vertex // v ≠ source}, ∃ faces : Fin 5 → P.Face,
      (∀ i, fan.ray i = figure.direction (order i).val) ∧
      (∀ i : Fin 5, (faces i).val ∩ (P.vertices : Set Space) =
        {(source : Space), ((order i).val : Space), ((order (i + 1)).val : Space)}) ∧
      (∀ F : P.Face, (source : Space) ∈ F.val ↔ F ∈ range faces) ∧
      Set.range fan.ray = figure.points := by
  classical
  obtain ⟨order, faces, vertices⟩ := P.universal_vertex_face_order size small_faces source universal
  let ray : Fin 5 → Space := fun i => figure.direction (order i).val
  have different (i : Fin 5) : ((order i).val : Space) ≠ source :=
    fun same => (order i).property (Subtype.ext same)
  have exact_points : Set.range ray = figure.points := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(order i).val, ⟨(order i).val.property, different i⟩, rfl⟩
    · rintro ⟨w, ⟨vertex, nonsource⟩, rfl⟩
      let neighbor : {v : P.Vertex // v ≠ source} :=
        ⟨⟨w, vertex⟩, fun same => nonsource (congrArg Subtype.val same)⟩
      refine ⟨order.symm neighbor, ?_⟩
      simp only [ray, order.apply_symm_apply, neighbor]
  have injective : Function.Injective ray := by
    intro i j same
    have equal := figure.direction_injective
      ⟨(order i).val.property, different i⟩ ⟨(order j).val.property, different j⟩ same
    exact order.injective (Subtype.ext (Subtype.ext equal))
  have side_exists (i : Fin 5) : ∃ normal : Space, normal ≠ 0 ∧
      inner ℝ normal (ray i) = 0 ∧ inner ℝ normal (ray (i + 1)) = 0 ∧
      (∀ j, inner ℝ normal (ray j) ≤ 0) ∧
      ∀ j, j ≠ i → j ≠ i + 1 → inner ℝ normal (ray j) < 0 := by
    let F := faces i
    obtain ⟨_, normal, level, nonzero, support, face_eq⟩ := F.property
    have sourceF : (source : Space) ∈ F.val := by
      have member : (source : Space) ∈ F.val ∩ (P.vertices : Set Space) := by rw [vertices]; simp
      exact member.1
    have source_level : inner ℝ normal (source : Space) = level := (face_eq ▸ sourceF).2
    have difference (j : Fin 5) : inner ℝ normal (ray j) =
        (figure.gap (order j).val)⁻¹ * (inner ℝ normal ((order j).val : Space) - level) := by
      change inner ℝ normal (figure.direction (order j).val) = _
      rw [VertexFigure.direction, inner_smul_right, inner_sub_right, source_level]
    have on_side (j : Fin 5) (member : ((order j).val : Space) ∈ F.val) :
        inner ℝ normal (ray j) = 0 := by
      have at_level : inner ℝ normal ((order j).val : Space) = level := (face_eq ▸ member).2
      rw [difference, at_level, sub_self, mul_zero]
    refine ⟨normal, nonzero, on_side i ?_, on_side (i + 1) ?_, ?_, ?_⟩
    · have member : ((order i).val : Space) ∈ F.val ∩ (P.vertices : Set Space) := by rw [vertices]; simp
      exact member.1
    · have member : ((order (i + 1)).val : Space) ∈ F.val ∩ (P.vertices : Set Space) := by rw [vertices]; simp
      exact member.1
    · intro j
      rw [difference]
      exact mul_nonpos_of_nonneg_of_nonpos
        (inv_nonneg.mpr (figure.gap_pos (order j).val.property (different j)).le)
        (sub_nonpos.mpr (support _ (P.vertices_subset_body (order j).val.property)))
    · intro j not_left not_right
      have outside : ((order j).val : Space) ∉ F.val := by
        intro inside
        have member : ((order j).val : Space) ∈ F.val ∩ (P.vertices : Set Space) :=
          ⟨inside, (order j).val.property⟩
        rw [vertices] at member
        rcases member with at_source | at_left | at_right
        · exact different j at_source
        · exact not_left (order.injective (Subtype.ext (Subtype.ext at_left)))
        · exact not_right (order.injective (Subtype.ext (Subtype.ext at_right)))
      have below : inner ℝ normal ((order j).val : Space) < level := by
        apply (support _ (P.vertices_subset_body (order j).val.property)).lt_of_ne
        intro at_level
        apply outside
        rw [face_eq]
        exact ⟨P.vertices_subset_body (order j).val.property, at_level⟩
      rw [difference]
      exact mul_neg_of_pos_of_neg (inv_pos.mpr (figure.gap_pos (order j).val.property (different j)))
        (sub_neg.mpr below)
  choose normal nonzero left right bound strict using side_exists
  let fan : FiveRayFan := {
    ray := ray
    distinct := injective
    height := -(innerSL ℝ figure.normal).toLinearMap
    level := by
      intro i
      change -(inner ℝ figure.normal (figure.direction (order i).val)) = 1
      rw [figure.direction_height (order i).val.property (different i)]
      norm_num
    spans := by rw [exact_points]; exact figure.points_span
    side := fun i => (innerSL ℝ (normal i)).toLinearMap
    side_nonzero := by
      intro i zero
      have self_zero := congrArg (fun f : Space →ₗ[ℝ] ℝ => f (normal i)) zero
      change inner ℝ (normal i) (normal i) = 0 at self_zero
      rw [real_inner_self_eq_norm_sq] at self_zero
      exact nonzero i (norm_eq_zero.mp (sq_eq_zero_iff.mp self_zero))
    side_left := left
    side_right := right
    side_bound := bound
    side_strict := strict
  }
  exact ⟨fan, order, faces, fun _ => rfl, vertices,
    P.universal_vertex_fan_covers small_faces source universal order faces vertices, exact_points⟩

end SixVertexUnfolding.ConvexPolyhedron
