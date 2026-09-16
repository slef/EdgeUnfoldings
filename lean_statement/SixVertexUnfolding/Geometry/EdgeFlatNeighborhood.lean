import SixVertexUnfolding.Geometry.EdgeFolding

/-! The two rigid half-planes of an edge folding give a genuine surface
neighborhood: every nearby surface point occurs, and no two planar points coincide. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

/-- The first inverse chart preserves distances throughout its facet plane. -/
theorem left_rigid : ∀ x ∈ affineSpan ℝ F.val, ∀ y ∈ affineSpan ℝ F.val,
    dist (chart.left x) (chart.left y) = dist x y := by
  intro x hx y hy
  rw [← chart.fold.first_rigid, chart.first_inverse x hx, chart.first_inverse y hy]

/-- The second inverse chart preserves distances throughout its facet plane. -/
theorem right_rigid : ∀ x ∈ affineSpan ℝ G.val, ∀ y ∈ affineSpan ℝ G.val,
    dist (chart.right x) (chart.right y) = dist x y := by
  intro x hx y hy
  rw [← chart.fold.second_rigid, chart.second_inverse x hx, chart.second_inverse y hy]

theorem left_nonnegative {x : Space} (hx : x ∈ F.val) : 0 ≤ chart.fold.height (chart.left x) :=
  (chart.left_halfplane x (subset_affineSpan ℝ _ hx)).mpr (facets.support G x (F.subset_body hx))

theorem right_nonpositive {x : Space} (hx : x ∈ G.val) : chart.fold.height (chart.right x) ≤ 0 :=
  (chart.right_halfplane x (subset_affineSpan ℝ _ hx)).mpr (facets.support F x (G.subset_body hx))

/-- Folding a point of the first original facet recovers that actual point. -/
theorem fold_left {x : Space} (hx : x ∈ F.val) : chart.fold.map (chart.left x) = x := by
  rw [chart.fold.map_of_nonnegative (chart.left_nonnegative hx),
    chart.first_inverse x (subset_affineSpan ℝ _ hx)]

/-- Folding a point of the second original facet recovers that actual point. -/
theorem fold_right {x : Space} (hx : x ∈ G.val) : chart.fold.map (chart.right x) = x := by
  rw [chart.fold.map_of_nonpositive (chart.right_nonpositive hx),
    chart.second_inverse x (subset_affineSpan ℝ _ hx)]

theorem height_on_hinge {x : Space} (hx : x ∈ F.val ∩ G.val) : chart.fold.height (chart.left x) = 0 := by
  apply le_antisymm _ (chart.left_nonnegative hx.1)
  rw [chart.joined hx]
  exact chart.right_nonpositive hx.2

/-- The part of a folded plane lying on these two actual facets is injective. -/
theorem injective_on_facets (V : Set Plane)
    (first_in : ∀ x ∈ V, 0 ≤ chart.fold.height x → chart.fold.first x ∈ F.val)
    (second_in : ∀ x ∈ V, chart.fold.height x ≤ 0 → chart.fold.second x ∈ G.val) :
    Set.InjOn chart.fold.map V := by
  intro x hx y hy equal
  by_cases px : 0 ≤ chart.fold.height x <;> by_cases py : 0 ≤ chart.fold.height y
  · rw [chart.fold.map_of_nonnegative px, chart.fold.map_of_nonnegative py] at equal
    simpa only [chart.left_inverse] using congrArg chart.left equal
  · rw [chart.fold.map_of_nonnegative px, chart.fold.map_of_nonpositive (le_of_not_ge py)] at equal
    have shared : chart.fold.first x ∈ F.val ∩ G.val :=
      ⟨first_in x hx px, equal ▸ second_in y hy (le_of_not_ge py)⟩
    calc
      x = chart.left (chart.fold.first x) := (chart.left_inverse x).symm
      _ = chart.right (chart.fold.first x) := chart.joined shared
      _ = y := by rw [equal, chart.right_inverse]
  · rw [chart.fold.map_of_nonpositive (le_of_not_ge px), chart.fold.map_of_nonnegative py] at equal
    have shared : chart.fold.first y ∈ F.val ∩ G.val :=
      ⟨first_in y hy py, equal ▸ second_in x hx (le_of_not_ge px)⟩
    calc
      x = chart.right (chart.fold.second x) := (chart.right_inverse x).symm
      _ = chart.right (chart.fold.first y) := congrArg chart.right equal
      _ = chart.left (chart.fold.first y) := (chart.joined shared).symm
      _ = y := chart.left_inverse y
  · rw [chart.fold.map_of_nonpositive (le_of_not_ge px), chart.fold.map_of_nonpositive (le_of_not_ge py)] at equal
    simpa only [chart.right_inverse] using congrArg chart.right equal

/-- A planar open set whose two folded halves form a full surface neighborhood. -/
structure Neighborhood (chart : EdgeFolding facets F G) (z : Space) where
  domain : Set Plane
  open_domain : IsOpen domain
  origin_mem : chart.left z ∈ domain
  first_in : ∀ x ∈ domain, 0 ≤ chart.fold.height x → chart.fold.first x ∈ F.val
  second_in : ∀ x ∈ domain, chart.fold.height x ≤ 0 → chart.fold.second x ∈ G.val
  covers : ∃ U : Set Space, IsOpen U ∧ z ∈ U ∧ U ∩ frontier P.body ⊆ chart.fold.map '' domain

/-- Every nonvertex point of an original edge admits this actual neighborhood construction. -/
theorem exists_neighborhood (shared : P.ShareEdge F G) {z : Space}
    (hz : z ∈ F.val ∩ G.val) (not_vertex : z ∉ P.vertices) : Nonempty (chart.Neighborhood z) := by
  obtain ⟨U₁, open₁, z₁, first_test⟩ := facets.edge_local_halfplane F G shared hz not_vertex
  obtain ⟨U₂, open₂, z₂, second_test⟩ := facets.edge_local_halfplane G F (F.shareEdge_symm G shared) ⟨hz.2, hz.1⟩ not_vertex
  let V : Set Plane := chart.fold.first ⁻¹' U₁ ∩ chart.fold.second ⁻¹' U₂
  have openV : IsOpen V := (open₁.preimage chart.fold.first.continuous_of_finiteDimensional).inter
    (open₂.preimage chart.fold.second.continuous_of_finiteDimensional)
  have origin : chart.left z ∈ V := by
    refine ⟨?_, ?_⟩
    · change chart.fold.first (chart.left z) ∈ U₁
      rwa [chart.first_inverse z (subset_affineSpan ℝ _ hz.1)]
    · change chart.fold.second (chart.left z) ∈ U₂
      rwa [chart.joined hz, chart.second_inverse z (subset_affineSpan ℝ _ hz.2)]
  have first_in : ∀ x ∈ V, 0 ≤ chart.fold.height x → chart.fold.first x ∈ F.val := by
    intro x hx positive
    apply (first_test _ hx.1).mpr
    refine ⟨chart.first_plane x, ?_⟩
    apply (chart.left_halfplane _ (chart.first_plane x)).mp
    rwa [chart.left_inverse]
  have second_in : ∀ x ∈ V, chart.fold.height x ≤ 0 → chart.fold.second x ∈ G.val := by
    intro x hx negative
    apply (second_test _ hx.2).mpr
    refine ⟨chart.second_plane x, ?_⟩
    apply (chart.right_halfplane _ (chart.second_plane x)).mp
    rwa [chart.right_inverse]
  obtain ⟨U₀, open₀, z₀, only_two⟩ := P.edge_neighborhood_two_facets F G shared hz not_vertex
  let U : Set Space := U₀ ∩ (chart.left ⁻¹' V ∩ chart.right ⁻¹' V)
  have openU : IsOpen U := open₀.inter
    ((openV.preimage chart.left.continuous_of_finiteDimensional).inter
      (openV.preimage chart.right.continuous_of_finiteDimensional))
  have zU : z ∈ U := ⟨z₀, origin, by change chart.right z ∈ V; rwa [← chart.joined hz]⟩
  refine ⟨⟨V, openV, origin, first_in, second_in, U, openU, zU, ?_⟩⟩
  intro x hx
  rcases only_two ⟨hx.1.1, hx.2⟩ with first | second
  · exact ⟨chart.left x, hx.1.2.1, chart.fold_left first⟩
  · exact ⟨chart.right x, hx.1.2.2, chart.fold_right second⟩

namespace Neighborhood

variable {chart} {z : Space} (near : chart.Neighborhood z)

theorem on_surface : chart.fold.map '' near.domain ⊆ frontier P.body := by
  rintro _ ⟨x, hx, rfl⟩
  by_cases positive : 0 ≤ chart.fold.height x
  · rw [chart.fold.map_of_nonnegative positive]
    exact F.subset_frontier (near.first_in x hx positive)
  · rw [chart.fold.map_of_nonpositive (le_of_not_ge positive)]
    exact G.subset_frontier (near.second_in x hx (le_of_not_ge positive))

theorem injective : Set.InjOn chart.fold.map near.domain :=
  chart.injective_on_facets near.domain near.first_in near.second_in

end Neighborhood
end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
