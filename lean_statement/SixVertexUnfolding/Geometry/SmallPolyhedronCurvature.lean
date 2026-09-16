import SixVertexUnfolding.Geometry.FacetAngleSums
import SixVertexUnfolding.Geometry.VertexFanIncidence
import SixVertexUnfolding.Geometry.UniversalVertexFaceCounting

/-! Surface angle and curvature computed directly from the original faces.
For the six-vertex universal-source case, a total-curvature upper bound is
sufficient; it follows from the face count without a global Euler formula. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Real

variable {P : ConvexPolyhedron} [Fintype P.Face]

/-- The total angle of all original faces incident to a vertex. -/
noncomputable def surfaceAngle (P : ConvexPolyhedron) [Fintype P.Face] (v : P.Vertex) : ℝ :=
  ∑ F : P.Face, F.cornerAngle v

/-- The actual angle deficit at an original vertex. -/
noncomputable def vertexCurvature (P : ConvexPolyhedron) [Fintype P.Face] (v : P.Vertex) : ℝ :=
  2 * π - P.surfaceAngle v

/-- A complete local fan sums exactly the angles of the original incident faces. -/
theorem VertexFaceFan.totalAngle_eq_surfaceAngle {v : P.Vertex} {n : ℕ} [NeZero n]
    (fan : P.VertexFaceFan v n) (size : P.vertices.card ≤ 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) :
    fan.totalAngle = P.surfaceAngle v := by
  apply Fintype.sum_of_injective fan.face (fan.faces_injective size small_faces)
    fan.sectorAngle (fun F => F.cornerAngle v)
  · intro F absent
    exact F.cornerAngle_of_not_mem v (fun member => absent ((fan.covers small_faces F).mp member))
  · intro i
    exact ((fan.face i).cornerAngle_eq (small_faces _) v (fan.neighbor i) (fan.neighbor (i + 1))
      (fan.successive_distinct i) (fan.pole_mem i) (fan.left_mem i) (fan.right_mem i)
      (fan.adjacent i) (fan.adjacent (i + 1))).symm

/-- Every actual vertex has strictly less than a full turn of surface angle. -/
theorem surfaceAngle_lt_two_pi (size : P.vertices.card ≤ 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) (v : P.Vertex) :
    P.surfaceAngle v < 2 * π := by
  have degree := P.edgeGraph_min_degree v
  letI : NeZero (P.edgeGraph.degree v) := ⟨by omega⟩
  obtain ⟨fan⟩ := P.exists_vertex_face_fan size small_faces v rfl
  rw [← fan.totalAngle_eq_surfaceAngle size small_faces]
  exact fan.totalAngle_lt_two_pi size small_faces

theorem vertexCurvature_pos (size : P.vertices.card ≤ 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) (v : P.Vertex) :
    0 < P.vertexCurvature v :=
  sub_pos.mpr (surfaceAngle_lt_two_pi size small_faces v)

/-- Counting each corner by its face or by its vertex gives the same angle sum. -/
theorem sum_surfaceAngle
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) :
    (∑ v : P.Vertex, P.surfaceAngle v) =
      ((∑ F : P.Face, ((F.val ∩ (P.vertices : Set Space)).ncard - 2) : ℕ) : ℝ) * π := by
  simp only [surfaceAngle]
  rw [Finset.sum_comm]
  simp_rw [Face.sum_cornerAngles _ (small_faces _)]
  rw [Nat.cast_sum, Finset.sum_mul]

/-- The universal-source case needs only this upper bound on total curvature. -/
theorem universal_sum_vertexCurvature_le (size : P.vertices.card = 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v) :
    (∑ v : P.Vertex, P.vertexCurvature v) ≤ 4 * π := by
  have count := universal_vertex_face_angle_weight size small_faces source universal
  have real_count : (8 : ℝ) ≤
      ((∑ F : P.Face, ((F.val ∩ (P.vertices : Set Space)).ncard - 2) : ℕ) : ℝ) := by
    exact_mod_cast count
  have angle_bound := mul_le_mul_of_nonneg_right real_count Real.pi_pos.le
  have vertex_count : Fintype.card P.Vertex = 6 := by simpa [Vertex] using size
  simp only [vertexCurvature, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, vertex_count]
  rw [sum_surfaceAngle small_faces]
  norm_num at angle_bound ⊢
  linarith

end SixVertexUnfolding.ConvexPolyhedron
