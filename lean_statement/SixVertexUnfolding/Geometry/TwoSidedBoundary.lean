import SixVertexUnfolding.Geometry.SourceBisectorDensity

/-! A line has only two local sides. Three disjoint open planar regions
cannot all approach a point if their nearby boundaries lie on that line.
This is the local topological input for unique-route cut-tree leaves. -/

namespace SixVertexUnfolding

open Set

/-- A connected region avoiding the boundary of an open set is either
entirely in that set or entirely outside it. -/
theorem connected_region_inside_of_meeting {region U : Set Plane}
    (connected : IsPreconnected region) (openU : IsOpen U)
    (meets : (region ∩ U).Nonempty) (avoids : Disjoint region (frontier U)) :
    region ⊆ U := by
  apply connected.subset_of_closure_inter_subset openU meets
  rintro x ⟨limit, inside⟩
  by_contra outside
  exact disjoint_left.mp avoids inside ⟨limit, by simpa only [openU.interior_eq] using outside⟩

/-- Only two disjoint open regions can meet along one straight local boundary. -/
theorem not_three_regions_at_line (regions : Fin 3 → Set Plane)
    (open_regions : ∀ i, IsOpen (regions i))
    (separate : Pairwise (fun i j => Disjoint (regions i) (regions j)))
    (center normal : Plane) (normal_nonzero : normal ≠ 0) (height radius : ℝ)
    (positive : 0 < radius) (limits : ∀ i, center ∈ closure (regions i))
    (boundaries : ∀ i, frontier (regions i) ∩ Metric.ball center radius ⊆
      {x | inner ℝ normal x = height}) : False := by
  classical
  let sides : Bool → Set Plane := fun b => Metric.ball center radius ∩
    if b then {x | inner ℝ normal x < height} else {x | height < inner ℝ normal x}
  have connected (b : Bool) : IsPreconnected (sides b) := by
    cases b
    · exact ((convex_ball center radius).inter
        ((convex_Ioi height).linear_preimage (innerSL ℝ normal).toLinearMap)).isPreconnected
    · exact ((convex_ball center radius).inter
        ((convex_Iio height).linear_preimage (innerSL ℝ normal).toLinearMap)).isPreconnected
  have off_line : Dense {x : Plane | inner ℝ normal x ≠ height} := by
    exact interior_eq_empty_iff_dense_compl.mp (line_interior_empty normal normal_nonzero height)
  have occupies (i : Fin 3) : ∃ b, (sides b).Nonempty ∧ sides b ⊆ regions i := by
    obtain ⟨x, near, inside⟩ := mem_closure_iff.mp (limits i) (Metric.ball center radius)
      Metric.isOpen_ball (Metric.mem_ball_self positive)
    obtain ⟨y, not_line, in_open⟩ := off_line.exists_mem_open
      (Metric.isOpen_ball.inter (open_regions i)) ⟨x, near, inside⟩
    have side : ∃ b, y ∈ sides b := by
      rcases lt_or_gt_of_ne not_line with lower | upper
      · exact ⟨true, in_open.1, lower⟩
      · exact ⟨false, in_open.1, upper⟩
    obtain ⟨b, on_side⟩ := side
    refine ⟨b, ⟨y, on_side⟩, connected_region_inside_of_meeting
      (connected b) (open_regions i) ⟨y, on_side, in_open.2⟩ ?_⟩
    apply disjoint_left.mpr
    intro z hz boundary
    have on_line := boundaries i ⟨boundary, hz.1⟩
    change inner ℝ normal z = height at on_line
    cases b <;> simp only [sides, Bool.false_eq_true, ↓reduceIte, mem_inter_iff,
      mem_setOf_eq] at hz <;> linarith [hz.2]
  choose side inhabited contained using occupies
  have injective : Function.Injective side := by
    intro i j same
    by_contra different
    obtain ⟨x, member⟩ := inhabited i
    exact disjoint_left.mp (separate different) (contained i member)
      (contained j (same ▸ member))
  have impossible := Fintype.card_le_of_injective side injective
  norm_num at impossible

end SixVertexUnfolding
