import SixVertexUnfolding.OctahedronComplete

/-! All twenty-eight subdivision triangle pairs are separated for every selected development. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles OctahedralNet

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem mixed_of_remainingNine (remaining : net.RemainingNine) (i j : Fin 4) (different : i ≠ j) :
    net.Separated (false, i) (true, j) := by
  fin_cases i <;> fin_cases j
  · exact False.elim (different rfl)
  · exact net.neighboring_fan_petal 0
  · exact (remaining.remote 2).symm
  · exact remaining.slit_right.symm
  · exact (net.neighboring_petal_fan 0).symm
  · exact False.elim (different rfl)
  · exact net.neighboring_fan_petal 1
  · exact (remaining.remote 3).symm
  · exact (remaining.remote 0).symm
  · exact (net.neighboring_petal_fan 1).symm
  · exact False.elim (different rfl)
  · exact net.neighboring_fan_petal 2
  · exact remaining.slit_left.symm
  · exact (remaining.remote 1).symm
  · exact (net.neighboring_petal_fan 2).symm
  · exact False.elim (different rfl)

theorem petals_of_remainingNine (remaining : net.RemainingNine) (i j : Fin 4) (different : i ≠ j) :
    net.Separated (true, i) (true, j) := by
  fin_cases i <;> fin_cases j
  · exact False.elim (different rfl)
  · exact net.neighboring_petals 0
  · exact remaining.opposite_even
  · exact remaining.slit_petals
  · exact (net.neighboring_petals 0).symm
  · exact False.elim (different rfl)
  · exact net.neighboring_petals 1
  · exact remaining.opposite_odd
  · exact remaining.opposite_even.symm
  · exact (net.neighboring_petals 1).symm
  · exact False.elim (different rfl)
  · exact net.neighboring_petals 2
  · exact remaining.slit_petals.symm
  · exact remaining.opposite_odd.symm
  · exact (net.neighboring_petals 2).symm
  · exact False.elim (different rfl)

/-- This result concerns the eight actual triangles, including subdivisions of quadrilateral facets. -/
theorem selected_triangles_nonoverlap
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit)) :
    ∀ x y : FaceIndex, x ≠ y → net.Separated x y := by
  have remaining := net.remainingNine_of_core (net.selected_local_pairs source_order maximal)
    (net.selected_opposite_petals source_order maximal) (net.selected_finite_cuts_clear source_order maximal)
  rintro ⟨left, i⟩ ⟨right, j⟩ different
  cases left <;> cases right
  · exact net.fan.nonoverlap i j (fun same => different (Prod.ext rfl same))
  · by_cases same : i = j
    · subst j
      exact net.attached_pair_nonoverlap i
    · exact net.mixed_of_remainingNine remaining i j same
  · by_cases same : j = i
    · subst j
      exact (net.attached_pair_nonoverlap i).symm
    · exact (net.mixed_of_remainingNine remaining j i same).symm
  · exact net.petals_of_remainingNine remaining i j (fun same => different (Prod.ext rfl same))

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
