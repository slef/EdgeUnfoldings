import SixVertexUnfolding.Geometry.RegularCutPoints
import SixVertexUnfolding.Geometry.HingeSideOrder

/-! The regular cut-line charts give actual surface arcs, parametrized
by intrinsic length, passing through the cut point in both directions. -/

namespace SixVertexUnfolding

open Set

/-- Every nonzero planar normal has a perpendicular unit direction. -/
theorem plane_unit_perpendicular (n : Plane) (nonzero : n ≠ 0) :
    ∃ d : Plane, ‖d‖ = 1 ∧ inner ℝ n d = 0 := by
  let D := Submodule.span ℝ ({n} : Set Plane)
  have dimensions := D.finrank_add_finrank_orthogonal
  have dimension : Module.finrank ℝ D = 1 := finrank_span_singleton nonzero
  have ambient : Module.finrank ℝ Plane = 2 := by simp [Plane]
  rw [dimension, ambient] at dimensions
  have nontrivial : Dᗮ ≠ ⊥ := by
    intro zero
    rw [zero, finrank_bot] at dimensions
    omega
  obtain ⟨q, member, q_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot nontrivial
  have perpendicular : inner ℝ n q = 0 :=
    D.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self n) member
  refine ⟨NormedSpace.normalize q, NormedSpace.norm_normalize q_ne, ?_⟩
  simp [NormedSpace.normalize, inner_smul_right, perpendicular]

namespace ConvexPolyhedron

/-- A genuine interval in the multiple-route locus, measured in surface distance. -/
structure CutArc (P : ConvexPolyhedron) (a b : Space) where
  radius : ℝ
  positive : 0 < radius
  curve : ℝ → Space
  continuous : Continuous curve
  at_zero : curve 0 = b
  on_surface : ∀ t ∈ Ioo (-radius) radius, curve t ∈ frontier P.body
  on_cut : ∀ t ∈ Ioo (-radius) radius, curve t ∈ P.multipleRouteLocus a
  distance : ∀ s ∈ Ioo (-radius) radius, ∀ t ∈ Ioo (-radius) radius,
    P.surfaceDist (curve s) (curve t) = dist s t
  covers : ∃ U : Set Space, IsOpen U ∧ b ∈ U ∧ ∀ y ∈ U ∩ frontier P.body,
    y ∈ P.multipleRouteLocus a → ∃ t ∈ Ioo (-radius) radius, curve t = y

namespace CutLineChart

variable {P : ConvexPolyhedron} {a b : Space} (chart : P.CutLineChart a b)

include chart in
/-- The full local cut line yields a surface arc through the target, with no missing subintervals. -/
theorem exists_cut_arc (multiple : b ∈ P.multipleRouteLocus a) : Nonempty (P.CutArc a b) := by
  obtain ⟨d, unit, perpendicular⟩ := plane_unit_perpendicular chart.normal chart.normal_ne_zero
  let line (t : ℝ) := chart.origin + t • d
  have continuous_line : Continuous line := continuous_const.add (continuous_id.smul continuous_const)
  have line_zero : line 0 = chart.origin := by simp [line]
  have origin_level : inner ℝ chart.normal chart.origin = chart.level :=
    (chart.cut_line chart.origin chart.origin_mem).mp (by rw [chart.at_origin]; exact multiple)
  obtain ⟨ε, positive, disk⟩ := Metric.isOpen_iff.mp
    (chart.open_domain.preimage continuous_line) 0 (by simpa only [mem_preimage, line_zero] using chart.origin_mem)
  have line_in (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : line t ∈ chart.domain := by
    apply disk
    change dist t 0 < ε
    simpa only [Real.dist_eq, sub_zero, abs_lt] using ht
  have distance (s t : ℝ) : dist (line s) (line t) = dist s t := by
    rw [dist_eq_norm, show line s - line t = (s - t) • d by dsimp [line]; module,
      norm_smul, unit, mul_one, Real.norm_eq_abs, Real.dist_eq]
  obtain ⟨U, openU, bU, covered⟩ := chart.covers
  have b_surface : b ∈ frontier P.body := by
    rw [← chart.at_origin]
    exact chart.on_surface chart.origin_mem
  let near : Set (frontier P.body) := {y | P.surfaceDist b y < ε}
  have near_open : IsOpen near := isOpen_lt ((P.surfaceDist_continuousOn b_surface).restrict) continuous_const
  obtain ⟨V, openV, sameV⟩ := isOpen_induced_iff.mp near_open
  have bV : b ∈ V := by
    have member : (⟨b, b_surface⟩ : frontier P.body) ∈ near := by
      change P.surfaceDist b b < ε
      rw [P.surfaceDist_self b_surface]
      exact positive
    rwa [← sameV] at member
  refine ⟨{
    radius := ε
    positive := positive
    curve := fun t => chart.map (line t)
    continuous := chart.continuous.comp continuous_line
    at_zero := by rw [line_zero, chart.at_origin]
    on_surface := fun t ht => chart.on_surface (line_in t ht)
    on_cut := ?_
    distance := fun s hs t ht => (chart.distance _ (line_in s hs) _ (line_in t ht)).trans (distance s t)
    covers := ⟨U ∩ V, openU.inter openV, ⟨bU, bV⟩, ?_⟩ }⟩
  · intro t ht
    apply (chart.cut_line _ (line_in t ht)).mpr
    simp only [line, inner_add_right, inner_smul_right, perpendicular, mul_zero, add_zero, origin_level]
  · intro y hy cut
    obtain ⟨x, hx, equal⟩ := covered ⟨hy.1.1, hy.2⟩
    have level := (chart.cut_line x hx).mp (by rw [equal]; exact cut)
    have orthogonal : inner ℝ chart.normal (x - chart.origin) = 0 := by
      rw [inner_sub_right, level, origin_level, sub_self]
    have d_ne : d ≠ 0 := by intro zero; simp [zero] at unit
    obtain ⟨t, position⟩ := perpendicular_multiple chart.normal d (x - chart.origin)
      chart.normal_ne_zero d_ne perpendicular orthogonal
    have line_t : line t = x := by dsimp [line]; rw [← position]; module
    have near_y : (⟨y, hy.2⟩ : frontier P.body) ∈ near := by
      rw [← sameV]
      exact hy.1.2
    have small : dist 0 t < ε := by
      rw [← distance 0 t, line_zero, line_t, ← chart.distance _ chart.origin_mem _ hx,
        chart.at_origin, equal]
      exact near_y
    have interval : t ∈ Ioo (-ε) ε := by
      simpa only [Real.dist_eq, zero_sub, abs_neg, abs_lt] using small
    exact ⟨t, interval, by rw [line_t, equal]⟩

end CutLineChart

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Away from the finite exceptions, every cut point lies inside an actual cut arc. -/
theorem regular_cut_arc (a b : frontier P.body) (cut : b ∈ P.cutSet a)
    (regular : b ∉ P.cutExceptions a) : Nonempty (P.CutArc a b) := by
  obtain ⟨_, ⟨chart⟩⟩ := graph.regular_cut_point small_faces a b cut regular
  apply chart.exists_cut_arc
  exact cut.resolve_right (fun vertex => regular (Or.inr vertex))

end SixVertexGraph
end ConvexPolyhedron
end SixVertexUnfolding
