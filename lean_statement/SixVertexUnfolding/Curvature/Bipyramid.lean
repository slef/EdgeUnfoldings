import SixVertexUnfolding.Geometry.BipyramidFaceIndex
import SixVertexUnfolding.Curvature.ThreeRays
import Mathlib.Geometry.Euclidean.Triangle

/-!
Actual corner angles of the six original bipyramid facets. Their total angle defect
is 4π, and both pole defects are strictly positive. Positivity at the equator
vertices is a separate, still unfinished geometric step.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices

open EuclideanGeometry
open scoped EuclideanGeometry

variable {P : ConvexPolyhedron} (B : BipyramidVertices P)

/-- The three face angles incident to one pole. -/
noncomputable def poleAngleSum (upper : Bool) : ℝ :=
  ∠ (B.equatorVertex 0 : Space) (B.poleVertex upper) (B.equatorVertex 1) +
  ∠ (B.equatorVertex 1 : Space) (B.poleVertex upper) (B.equatorVertex 2) +
  ∠ (B.equatorVertex 2 : Space) (B.poleVertex upper) (B.equatorVertex 0)

/-- The two angles contributed by one cap at an equator vertex. Indices are modulo three. -/
noncomputable def equatorAngleSum (upper : Bool) (i : Fin 3) : ℝ :=
  ∠ (B.poleVertex upper : Space) (B.equatorVertex i) (B.equatorVertex (i + 1)) +
  ∠ (B.poleVertex upper : Space) (B.equatorVertex i) (B.equatorVertex (i + 2))

/-- The angle defect at a pole. -/
noncomputable def poleCurvature (upper : Bool) : ℝ := 2 * Real.pi - B.poleAngleSum upper

/-- The angle defect at an equator vertex, counting both original caps. -/
noncomputable def equatorCurvature (i : Fin 3) : ℝ :=
  2 * Real.pi - B.equatorAngleSum true i - B.equatorAngleSum false i

/-- Each corner of an original cap triangle is strictly between zero and π. -/
theorem cap_corner_bounds (upper : Bool) (i j : Fin 3) (different : i ≠ j) :
    0 < ∠ (B.poleVertex upper : Space) (B.equatorVertex i) (B.equatorVertex j) ∧
    ∠ (B.poleVertex upper : Space) (B.equatorVertex i) (B.equatorVertex j) < Real.pi := by
  have noncollinear := P.no_three_collinear_vertices (B.poleVertex upper).property
    (B.equatorVertex i).property (B.equatorVertex j).property
    (fun same => B.pole_ne_equator upper i (Subtype.ext same))
    (fun same => B.pole_ne_equator upper j (Subtype.ext same))
    (fun same => different (B.equator_injective (Subtype.ext same)))
  exact ⟨angle_pos_of_not_collinear noncollinear, angle_lt_pi_of_not_collinear noncollinear⟩

/-- The nine corners in the three triangles of one cap sum to 3π. -/
theorem cap_angle_sum (upper : Bool) :
    B.poleAngleSum upper + ∑ i : Fin 3, B.equatorAngleSum upper i = 3 * Real.pi := by
  have triangle_sum (i j : Fin 3) :
      ∠ (B.equatorVertex i : Space) (B.poleVertex upper) (B.equatorVertex j) +
      ∠ (B.poleVertex upper : Space) (B.equatorVertex j) (B.equatorVertex i) +
      ∠ (B.poleVertex upper : Space) (B.equatorVertex i) (B.equatorVertex j) = Real.pi := by
    have sum := angle_add_angle_add_angle_eq_pi (B.equatorVertex j : Space)
      (show (B.poleVertex upper : Space) ≠ (B.equatorVertex i : Space) from
        fun same => B.pole_ne_equator upper i (Subtype.ext same))
    rwa [angle_comm (B.equatorVertex j : Space) (B.equatorVertex i) (B.poleVertex upper)] at sum
  have first := triangle_sum 0 1
  have second := triangle_sum 1 2
  have third := triangle_sum 2 0
  simp only [poleAngleSum, Fin.sum_univ_three, equatorAngleSum, Fin.reduceAdd]
  linarith

/-- For the identified six triangular facets, the five vertex angle defects sum to 4π. -/
theorem total_curvature :
    B.poleCurvature true + B.poleCurvature false +
      ∑ i : Fin 3, B.equatorCurvature i = 4 * Real.pi := by
  have top := B.cap_angle_sum true
  have bottom := B.cap_angle_sum false
  simp only [Fin.sum_univ_three] at top bottom
  simp only [poleCurvature, equatorCurvature, Fin.sum_univ_three]
  linarith

/-- The genuine supporting facet opposite an equator vertex gives positive pole curvature. -/
theorem pole_curvature_pos
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) : 0 < B.poleCurvature upper := by
  let F := B.face triangles upper 0
  obtain ⟨_, normal, level, _, support, face_eq⟩ := F.property
  have pole_height : inner ℝ normal (B.poleVertex upper : Space) = level :=
    (face_eq ▸ B.pole_mem_face triangles upper 0).2
  have first_height : inner ℝ normal (B.equatorVertex 1 : Space) = level :=
    (face_eq ▸ (B.equator_mem_face triangles upper 0 1).mpr (by decide)).2
  have second_height : inner ℝ normal (B.equatorVertex 2 : Space) = level :=
    (face_eq ▸ (B.equator_mem_face triangles upper 0 2).mpr (by decide)).2
  have third_height : inner ℝ normal (B.equatorVertex 0 : Space) < level := by
    apply lt_of_le_of_ne (support _ (P.vertices_subset_body (B.equatorVertex 0).property))
    intro same
    have member : (B.equatorVertex 0 : Space) ∈ F.val :=
      face_eq ▸ ⟨P.vertices_subset_body (B.equatorVertex 0).property, same⟩
    exact (B.equator_mem_face triangles upper 0 0).mp member rfl
  have noncollinear := P.no_three_collinear_vertices (B.equatorVertex 1).property
    (B.poleVertex upper).property (B.equatorVertex 2).property
    (fun same => B.pole_ne_equator upper 1 (Subtype.ext same.symm))
    (fun same => (show (1 : Fin 3) ≠ 2 by decide) (B.equator_injective (Subtype.ext same)))
    (fun same => B.pole_ne_equator upper 2 (Subtype.ext same))
  have not_straight := angle_lt_pi_of_not_collinear noncollinear
  have strict := three_ray_angle_sum_lt_two_pi
    ((B.equatorVertex 1 : Space) - B.poleVertex upper)
    ((B.equatorVertex 2 : Space) - B.poleVertex upper)
    ((B.equatorVertex 0 : Space) - B.poleVertex upper) normal
    (by rw [inner_sub_right, first_height, pole_height, sub_self])
    (by rw [inner_sub_right, second_height, pole_height, sub_self])
    (by rw [inner_sub_right, pole_height]; exact sub_ne_zero.mpr third_height.ne)
    not_straight
  change ∠ (B.equatorVertex 1 : Space) (B.poleVertex upper) (B.equatorVertex 2) +
    ∠ (B.equatorVertex 2 : Space) (B.poleVertex upper) (B.equatorVertex 0) +
    ∠ (B.equatorVertex 0 : Space) (B.poleVertex upper) (B.equatorVertex 1) < 2 * Real.pi at strict
  unfold poleCurvature poleAngleSum
  linarith

/-- The three angles at either pole have positive sum. -/
theorem pole_angle_sum_pos (upper : Bool) : 0 < B.poleAngleSum upper := by
  have noncollinear := P.no_three_collinear_vertices (B.equatorVertex 0).property
    (B.poleVertex upper).property (B.equatorVertex 1).property
    (fun same => B.pole_ne_equator upper 0 (Subtype.ext same.symm))
    (fun same => (show (0 : Fin 3) ≠ 1 by decide) (B.equator_injective (Subtype.ext same)))
    (fun same => B.pole_ne_equator upper 1 (Subtype.ext same))
  have first := angle_pos_of_not_collinear noncollinear
  have second := angle_nonneg (B.equatorVertex 1 : Space) (B.poleVertex upper) (B.equatorVertex 2)
  have third := angle_nonneg (B.equatorVertex 2 : Space) (B.poleVertex upper) (B.equatorVertex 0)
  unfold poleAngleSum
  linarith

/-- Each cap contributes a positive angle sum at every equator vertex. -/
theorem equator_angle_sum_pos (upper : Bool) (i : Fin 3) : 0 < B.equatorAngleSum upper i := by
  have different : i ≠ i + 1 := by fin_cases i <;> decide
  have first := (B.cap_corner_bounds upper i (i + 1) different).1
  have second := angle_nonneg (B.poleVertex upper : Space) (B.equatorVertex i) (B.equatorVertex (i + 2))
  unfold equatorAngleSum
  linarith

/-- Every actual vertex defect is strictly less than 2π. -/
theorem curvature_lt_two_pi :
    (∀ upper, B.poleCurvature upper < 2 * Real.pi) ∧
      ∀ i, B.equatorCurvature i < 2 * Real.pi := by
  constructor
  · intro upper
    have positive := B.pole_angle_sum_pos upper
    unfold poleCurvature
    linarith
  · intro i
    have top := B.equator_angle_sum_pos true i
    have bottom := B.equator_angle_sum_pos false i
    unfold equatorCurvature
    linarith

/-- A maximum-curvature equator source exists, and its actual defect lies strictly between 0 and 2π. -/
theorem exists_positive_equator_maximum :
    ∃ source : Fin 3, (∀ i, B.equatorCurvature i ≤ B.equatorCurvature source) ∧
      0 < B.equatorCurvature source ∧ B.equatorCurvature source < 2 * Real.pi := by
  obtain ⟨source, _, maximal⟩ := Finset.univ.exists_max_image B.equatorCurvature Finset.univ_nonempty
  have total := B.total_curvature
  have top := B.curvature_lt_two_pi.1 true
  have bottom := B.curvature_lt_two_pi.1 false
  have bound : (∑ i : Fin 3, B.equatorCurvature i) ≤ 3 * B.equatorCurvature source := by
    calc
      (∑ i : Fin 3, B.equatorCurvature i) ≤ ∑ _i : Fin 3, B.equatorCurvature source :=
        Finset.sum_le_sum (fun i hi => maximal i hi)
      _ = 3 * B.equatorCurvature source := by simp
  exact ⟨source, fun i => maximal i (Finset.mem_univ i), by linarith,
    B.curvature_lt_two_pi.2 source⟩

end SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices
