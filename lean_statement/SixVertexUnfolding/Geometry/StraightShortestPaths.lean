import SixVertexUnfolding.Geometry.SurfacePaths

/-! A shortest path between cofacial points cannot take a different route around the surface. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open scoped ENNReal NNReal

variable {P : ConvexPolyhedron} {a b : Space}

/-- Splitting a path at any point bounds the sum of the two endpoint chords by its arc length. -/
theorem two_chords_le_length (path : P.SurfacePath a b) (t : unitInterval) :
    edist a (path.curve t) + edist (path.curve t) b ≤ path.length := by
  have first := eVariationOn.edist_le path.curve.extend
    (by exact ⟨le_rfl, t.property.1⟩ : (0 : ℝ) ∈ Set.Icc 0 (t : ℝ))
    (by exact ⟨t.property.1, le_rfl⟩ : (t : ℝ) ∈ Set.Icc 0 (t : ℝ))
  have second := eVariationOn.edist_le path.curve.extend
    (by exact ⟨le_rfl, t.property.2⟩ : (t : ℝ) ∈ Set.Icc (t : ℝ) 1)
    (by exact ⟨t.property.2, le_rfl⟩ : (1 : ℝ) ∈ Set.Icc (t : ℝ) 1)
  have split := eVariationOn.Icc_add_Icc path.curve.extend (s := Set.univ)
    t.property.1 t.property.2 (Set.mem_univ (t : ℝ))
  simp only [Set.univ_inter] at split
  have bound := (add_le_add first second).trans_eq split
  simpa only [Path.extend_zero, Path.extend_one, Path.extend_apply path.curve t.property] using bound

/-- Any shortest path between two points of one face has the straight chord length. -/
theorem shortest_cofacial_length (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (F : P.Face) (ha : a ∈ F.val) (hb : b ∈ F.val) : path.length = edist a b := by
  have upper := shortest (inFace F ha hb)
  rw [inFace_length] at upper
  exact le_antisymm upper path.chord_le_length

/-- Every point of such a shortest path lies on the straight segment; there is no alternate surface detour. -/
theorem shortest_cofacial_range_subset (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (F : P.Face) (ha : a ∈ F.val) (hb : b ∈ F.val) :
    Set.range path.curve ⊆ segment ℝ a b := by
  rintro x ⟨t, rfl⟩
  have bound := path.two_chords_le_length t
  rw [path.shortest_cofacial_length shortest F ha hb] at bound
  have real_bound : dist a (path.curve t) + dist (path.curve t) b ≤ dist a b := by
    rw [edist_dist, edist_dist, edist_dist,
      ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at bound
    exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp bound
  exact (dist_add_dist_eq_iff.mp (le_antisymm real_bound (dist_triangle _ _ _))).mem_segment

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
