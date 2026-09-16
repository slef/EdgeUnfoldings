import SixVertexUnfolding.Geometry.OctahedralFanNeighborhood

/-! A small chord between fan directions less than pi apart stays entirely
within the opened fan, and can therefore be folded onto the surface. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- Every sufficiently small short-angle chord is contained in the finite fan. -/
theorem openingTriangles_small_chords (pole : Fin 6) (slit : Fin 4) :
    ∃ ε > 0, ∀ r ∈ Icc (0 : ℝ) ε, ∀ s ∈ Icc (0 : ℝ) ε,
      ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ graph.totalAngleAt pole → β - α < π →
      segment ℝ (r • direction α) (s • direction β) ⊆
        ⋃ i : Fin 4, graph.openingTriangle pole slit i := by
  obtain ⟨ε, positive, rays⟩ := graph.openingTriangles_small_rays pole slit
  refine ⟨ε, positive, ?_⟩
  intro r hr s hs α β lower ordered upper short x member
  by_cases same : α = β
  · subst β
    obtain ⟨a, b, ha, hb, total, expression⟩ := member
    have combined : x = (a * r + b * s) • direction α := by
      rw [← expression]
      module
    rw [combined]
    exact rays _ ⟨add_nonneg (mul_nonneg ha hr.1) (mul_nonneg hb hs.1), by nlinarith [hr.2, hs.2]⟩
      α ⟨lower, upper⟩
  · have width : 0 < β - α := sub_pos.mpr (lt_of_le_of_ne ordered same)
    have cone : x ∈ twoRayCone (direction α) (direction β) :=
      (twoRayCone_convex _ _).segment_subset
        (show r • direction α ∈ twoRayCone (direction α) (direction β) from
          ⟨r, 0, hr.1, le_rfl, by simp⟩)
        (show s • direction β ∈ twoRayCone (direction α) (direction β) from
          ⟨0, s, le_rfl, hs.1, by simp⟩) member
    have in_ball : x ∈ Metric.closedBall (0 : Plane) ε :=
      (convex_closedBall (0 : Plane) ε).segment_subset
        (by rw [Metric.mem_closedBall, dist_comm, polar_radius r α hr.1]; exact hr.2)
        (by rw [Metric.mem_closedBall, dist_comm, polar_radius s β hs.1]; exact hs.2) member
    by_cases zero : x = 0
    · rw [zero]
      simpa only [zero_smul] using rays 0 ⟨le_rfl, positive.le⟩ α ⟨lower, ordered.trans upper⟩
    · obtain ⟨θ, first, last, expression⟩ := polar_representation_in_short_cone α β width short x zero cone
      rw [expression]
      apply rays _ ⟨dist_nonneg, ?_⟩ θ ⟨lower.trans first, last.trans upper⟩
      exact (dist_comm 0 x) ▸ in_ball

namespace FanDevelopment

variable {graph} {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4}
  {pole : Fin 6} {slit : Fin 4} (fan : graph.FanDevelopment small_faces pole slit)

/-- Nearby fan points less than pi apart admit a surface path shorter than the route through the pole. -/
theorem exists_short_chord_paths :
    ∃ fold : P.FiniteSurfaceFolding (Fin 4), ∃ ε > 0,
      (∀ i x, x ∈ graph.triangle (OctahedralTriangles.fanTriangle pole (slit + i)) →
        fold.map (fan.place i x) = x) ∧
      ∀ r ∈ Ioc (0 : ℝ) ε, ∀ s ∈ Ioc (0 : ℝ) ε,
        ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ graph.totalAngleAt pole → β - α < π →
        ∃ path : P.SurfacePath (fold.map (r • direction α)) (fold.map (s • direction β)),
          path.length < ENNReal.ofReal (r + s) := by
  obtain ⟨fold, pieces, inverse⟩ := fan.exists_surface_folding
  obtain ⟨ε, positive, chords⟩ := graph.openingTriangles_small_chords pole slit
  refine ⟨fold, ε, positive, inverse, ?_⟩
  intro r hr s hs α β lower ordered upper short
  have inside : segment ℝ (r • direction α) (s • direction β) ⊆ fold.domain := by
    have domains : fold.domain = ⋃ i : Fin 4, graph.openingTriangle pole slit i := by
      simp only [FiniteSurfaceFolding.domain, pieces]
    rw [domains]
    exact chords r ⟨hr.1.le, hr.2⟩ s ⟨hs.1.le, hs.2⟩ α β lower ordered upper short
  refine ⟨fold.segmentPath _ _ inside, (fold.segmentPath_length_le _ _ inside).trans_lt ?_⟩
  rw [edist_dist]
  exact (ENNReal.ofReal_lt_ofReal_iff (add_pos hr.1 hs.1)).mpr
    (polar_chord_shorter_than_radii r s α β hr.1 hs.1 (sub_nonneg.mpr ordered) short)

end FanDevelopment
end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
