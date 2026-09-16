import SixVertexUnfolding.Geometry.QuadrilateralCornerAngles

/-! Sum the ordinary face angles over the actual original vertices. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

open Set Real EuclideanGeometry

variable {P : ConvexPolyhedron} (F : P.Face)

/-- An enumeration of a face's corners preserves its angle sum. -/
theorem sum_cornerAngles_of_vertices {ι : Type*} [Fintype ι]
    (corner : ι → P.Vertex) (distinct : Function.Injective corner)
    (vertices : F.val ∩ (P.vertices : Set Space) = range (fun i => (corner i : Space))) :
    (∑ v : P.Vertex, F.cornerAngle v) = ∑ i, F.cornerAngle (corner i) := by
  symm
  apply Fintype.sum_of_injective corner distinct _ _ _ (fun _ => rfl)
  intro v outside
  apply F.cornerAngle_of_not_mem
  intro on_face
  obtain ⟨i, same⟩ := vertices ▸
    (show (v : Space) ∈ F.val ∩ (P.vertices : Set Space) from ⟨on_face, v.property⟩)
  exact outside ⟨i, Subtype.ext same⟩

/-- A triangular original face contributes exactly π. -/
theorem triangle_angle_sum (triangle : (F.val ∩ (P.vertices : Set Space)).ncard = 3) :
    (∑ v : P.Vertex, F.cornerAngle v) = π := by
  classical
  obtain ⟨a, b, c, ab, ac, bc, vertices⟩ := Set.ncard_eq_three.mp triangle
  have original (x : Space) (member : x ∈ ({a, b, c} : Set Space)) : x ∈ P.vertices :=
    (vertices ▸ member).2
  let A : P.Vertex := ⟨a, original a (Or.inl rfl)⟩
  let B : P.Vertex := ⟨b, original b (Or.inr (Or.inl rfl))⟩
  let C : P.Vertex := ⟨c, original c (Or.inr (Or.inr rfl))⟩
  have AB : A ≠ B := fun same => ab (congrArg Subtype.val same)
  have AC : A ≠ C := fun same => ac (congrArg Subtype.val same)
  have BC : B ≠ C := fun same => bc (congrArg Subtype.val same)
  let corner : Fin 3 → P.Vertex := ![A, B, C]
  have distinct : Function.Injective corner := by
    intro i j same
    fin_cases i <;> fin_cases j <;> simp_all [corner]
  have enumerates : F.val ∩ (P.vertices : Set Space) = range (fun i => (corner i : Space)) := by
    rw [vertices]
    ext x
    simp [corner, Set.mem_range, Fin.exists_fin_succ, A, B, C, eq_comm]
  have member (i : Fin 3) : (corner i : Space) ∈ F.val := by
    have belongs : (corner i : Space) ∈ F.val ∩ (P.vertices : Set Space) :=
      enumerates.symm ▸ mem_range_self i
    exact belongs.1
  have actual (i : Fin 3) : F.cornerAngle (corner i) =
      angle (corner (i + 1) : Space) (corner i) (corner (i + 2)) := by
    apply F.cornerAngle_eq (Or.inl triangle) _ _ _
    · exact distinct.ne (by fin_cases i <;> decide)
    · exact member i
    · exact member (i + 1)
    · exact member (i + 2)
    · exact F.adjacent_of_triangle triangle _ _
        (distinct.ne (by fin_cases i <;> decide)) (member i) (member (i + 1))
    · exact F.adjacent_of_triangle triangle _ _
        (distinct.ne (by fin_cases i <;> decide)) (member i) (member (i + 2))
  rw [F.sum_cornerAngles_of_vertices corner distinct enumerates]
  simp_rw [actual]
  have sum := angle_add_angle_add_angle_eq_pi c ab.symm
  simp only [Fin.sum_univ_succ]
  change angle b a c + (angle c b a + (angle a c b + 0)) = π
  linarith [angle_comm a b c, angle_comm b c a, angle_comm c a b]

/-- A quadrilateral original face contributes exactly 2π. -/
theorem quadrilateral_angle_sum (four : (F.val ∩ (P.vertices : Set Space)).ncard = 4) :
    (∑ v : P.Vertex, F.cornerAngle v) = 2 * π := by
  obtain ⟨Q⟩ := F.exists_quadrilateral four
  rw [F.sum_cornerAngles_of_vertices Q.corner Q.distinct Q.vertices]
  have actual (i : Fin 4) : F.cornerAngle (Q.corner i) =
      angle (Q.corner (i + 1) : Space) (Q.corner i) (Q.corner (i + 3)) := by
    apply F.cornerAngle_eq (Or.inr four) _ _ _
    · exact Q.distinct.ne (by fin_cases i <;> decide)
    · exact Q.corner_mem i
    · exact Q.corner_mem (i + 1)
    · exact Q.corner_mem (i + 3)
    · exact Q.consecutive_adjacent i
    · exact (Q.corner_neighbors i _ (Q.corner_mem _)).mpr (Or.inr rfl)
  simp_rw [actual]
  exact Q.sum_angles

/-- Face-angle weight means the sum of the ordinary geometric corner angles. -/
theorem sum_cornerAngles
    (small : (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) :
    (∑ v : P.Vertex, F.cornerAngle v) =
      (((F.val ∩ (P.vertices : Set Space)).ncard - 2 : ℕ) : ℝ) * π := by
  rcases small with triangle | quadrilateral
  · rw [F.triangle_angle_sum triangle, triangle]
    norm_num
  · rw [F.quadrilateral_angle_sum quadrilateral, quadrilateral]
    norm_num

end SixVertexUnfolding.ConvexPolyhedron.Face
