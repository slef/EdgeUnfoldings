import SixVertexUnfolding.Geometry.EdgeFlatNeighborhood
import SixVertexUnfolding.Geometry.StraightShortestPaths
import SixVertexUnfolding.Geometry.SurfacePathReversal

/-! The inverse of the local edge folding is continuous on both closed facets.
Every surface path confined to these facets is at least as long as its unfolded chord. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set
open scoped ENNReal NNReal

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

/-- Unfold the first facet by its placement and the second by the joined placement. -/
noncomputable def unfold (x : Space) : Plane := by
  classical
  exact if x ∈ F.val then chart.left x else chart.right x

theorem unfold_of_first {x : Space} (hx : x ∈ F.val) : chart.unfold x = chart.left x := if_pos hx

theorem unfold_of_second {x : Space} (hx : x ∈ G.val) : chart.unfold x = chart.right x := by
  by_cases first : x ∈ F.val
  · rw [chart.unfold_of_first first, chart.joined ⟨first, hx⟩]
  · exact if_neg first

/-- Agreement on the shared edge makes the inverse continuous on the two-facet union. -/
theorem unfold_continuousOn : ContinuousOn chart.unfold (F.val ∪ G.val) := by
  apply ContinuousOn.union_of_isClosed _ _ F.isClosed G.isClosed
  · exact chart.left.continuous_of_finiteDimensional.continuousOn.congr (fun x hx => chart.unfold_of_first hx)
  · exact chart.right.continuous_of_finiteDimensional.continuousOn.congr (fun x hx => chart.unfold_of_second hx)

theorem fold_unfold {x : Space} (hx : x ∈ F.val ∪ G.val) : chart.fold.map (chart.unfold x) = x := by
  rcases hx with first | second
  · rw [chart.unfold_of_first first, chart.fold_left first]
  · rw [chart.unfold_of_second second, chart.fold_right second]

/-- On a genuine neighborhood, unfolding and folding are mutually inverse. -/
theorem Neighborhood.unfold_fold {z : Space} (near : chart.Neighborhood z) {x : Plane}
    (hx : x ∈ near.domain) : chart.unfold (chart.fold.map x) = x := by
  by_cases positive : 0 ≤ chart.fold.height x
  · rw [chart.fold.map_of_nonnegative positive, chart.unfold_of_first (near.first_in x hx positive), chart.left_inverse]
  · rw [chart.fold.map_of_nonpositive (le_of_not_ge positive),
      chart.unfold_of_second (near.second_in x hx (le_of_not_ge positive)), chart.right_inverse]

/-- A route in two closed facets with endpoints on different facets crosses their shared set. -/
theorem path_meets_hinge {a b : Space} (path : P.SurfacePath a b)
    (contained : ∀ t, path.curve t ∈ F.val ∪ G.val) (ha : a ∈ F.val) (hb : b ∈ G.val) :
    ∃ t, path.curve t ∈ F.val ∩ G.val := by
  have crossing := isPreconnected_closed_iff.mp (isPreconnected_range path.curve.continuous)
    F.val G.val F.isClosed G.isClosed
    (by rintro x ⟨t, rfl⟩; exact contained t)
    ⟨a, ⟨0, path.curve.source⟩, ha⟩ ⟨b, ⟨1, path.curve.target⟩, hb⟩
  obtain ⟨x, ⟨t, rfl⟩, shared⟩ := crossing
  exact ⟨t, shared⟩

/-- A two-facet route bounds the chord between its two unfolded endpoints. -/
theorem cross_chord_le_length {a b : Space} (path : P.SurfacePath a b)
    (contained : ∀ t, path.curve t ∈ F.val ∪ G.val) (ha : a ∈ F.val) (hb : b ∈ G.val) :
    edist (chart.left a) (chart.right b) ≤ path.length := by
  obtain ⟨t, shared⟩ := path_meets_hinge path contained ha hb
  have first := chart.left_rigid a (subset_affineSpan ℝ _ ha) _ (subset_affineSpan ℝ _ shared.1)
  have second := chart.right_rigid _ (subset_affineSpan ℝ _ shared.2) b (subset_affineSpan ℝ _ hb)
  have comparison : edist (chart.left a) (chart.right b) ≤
      edist a (path.curve t) + edist (path.curve t) b := by
    calc
      edist (chart.left a) (chart.right b) ≤ edist (chart.left a) (chart.left (path.curve t)) +
          edist (chart.left (path.curve t)) (chart.right b) := edist_triangle _ _ _
      _ = edist a (path.curve t) + edist (path.curve t) b := by
        rw [edist_dist, first, chart.joined shared, edist_dist, second, edist_dist a, edist_dist (path.curve t)]
  exact comparison.trans (path.two_chords_le_length t)

/-- Any continuous path inside the two facets is no shorter than its planar developed chord. -/
theorem unfolded_chord_le_length {a b : Space} (path : P.SurfacePath a b)
    (contained : ∀ t, path.curve t ∈ F.val ∪ G.val) :
    edist (chart.unfold a) (chart.unfold b) ≤ path.length := by
  have ha : a ∈ F.val ∪ G.val := path.curve.source ▸ contained 0
  have hb : b ∈ F.val ∪ G.val := path.curve.target ▸ contained 1
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [chart.unfold_of_first ha, chart.unfold_of_first hb, edist_dist,
      chart.left_rigid a (subset_affineSpan ℝ _ ha) b (subset_affineSpan ℝ _ hb), ← edist_dist]
    exact path.chord_le_length
  · rw [chart.unfold_of_first ha, chart.unfold_of_second hb]
    exact chart.cross_chord_le_length path contained ha hb
  · rw [chart.unfold_of_second ha, chart.unfold_of_first hb, edist_comm]
    have reverse := chart.cross_chord_le_length path.reverse (fun t => contained (unitInterval.symm t)) hb ha
    rwa [SurfacePath.reverse_length] at reverse
  · rw [chart.unfold_of_second ha, chart.unfold_of_second hb, edist_dist,
      chart.right_rigid a (subset_affineSpan ℝ _ ha) b (subset_affineSpan ℝ _ hb), ← edist_dist]
    exact path.chord_le_length

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
