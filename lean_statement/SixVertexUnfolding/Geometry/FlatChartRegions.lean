import SixVertexUnfolding.Geometry.FlatChartCoordinates

/-! Open surface regions and their boundary limits in a genuine flat chart.
The neighborhood coverage in `FlatChart` supplies the inverse direction. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FlatChart

open Set Filter Topology

variable {P : ConvexPolyhedron} {z : Space} (chart : P.FlatChart z)

/-- The chart, with its boundary membership recorded in the codomain. -/
noncomputable def surfaceMap : C(chart.domain, frontier P.body) :=
  ⟨fun x => ⟨chart.map x, chart.on_surface x.property⟩,
    (chart.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The planar points of the chart that belong to a specified surface region. -/
def pullback (S : Set (frontier P.body)) : Set Plane :=
  Subtype.val '' (chart.surfaceMap ⁻¹' S)

theorem mem_pullback (S : Set (frontier P.body)) (x : Plane) (hx : x ∈ chart.domain) :
    x ∈ chart.pullback S ↔ chart.surfaceMap ⟨x, hx⟩ ∈ S := by
  constructor
  · rintro ⟨y, member, equal⟩
    have same : y = ⟨x, hx⟩ := Subtype.ext equal
    simpa only [same] using member
  · exact fun member => ⟨⟨x, hx⟩, member, rfl⟩

theorem pullback_open {S : Set (frontier P.body)} (openS : IsOpen S) :
    IsOpen (chart.pullback S) :=
  chart.open_domain.isOpenMap_subtype_val _ (openS.preimage chart.surfaceMap.continuous)

theorem pullback_disjoint {S R : Set (frontier P.body)} (separate : Disjoint S R) :
    Disjoint (chart.pullback S) (chart.pullback R) := by
  apply disjoint_left.mpr
  rintro x ⟨y, hy, rfl⟩ inside
  exact disjoint_left.mp separate hy ((chart.mem_pullback R y y.property).mp inside)

/-- A planar boundary point inside the chart maps to an actual surface boundary point. -/
theorem frontier_pullback {S : Set (frontier P.body)} (openS : IsOpen S)
    (x : Plane) (hx : x ∈ chart.domain) (boundary : x ∈ frontier (chart.pullback S)) :
    chart.surfaceMap ⟨x, hx⟩ ∈ frontier S := by
  have limit : (⟨x, hx⟩ : chart.domain) ∈ closure (chart.surfaceMap ⁻¹' S) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    exact boundary.1
  refine ⟨chart.surfaceMap.continuous.closure_preimage_subset S limit, ?_⟩
  rw [openS.interior_eq]
  intro inside
  exact boundary.2 ((chart.pullback_open openS).interior_eq.symm ▸
    (chart.mem_pullback S x hx).mpr inside)

/-- Inverse coordinates are continuous at the center in the actual boundary topology. -/
theorem coordinates_continuousAt_center (b : frontier P.body) (at_center : (b : Space) = z) :
    ContinuousAt (fun x : frontier P.body => chart.coordinates x) b := by
  obtain ⟨U, openU, center, covers⟩ := chart.covers
  let image : Set (frontier P.body) := Subtype.val ⁻¹' (chart.map '' chart.domain)
  have neighborhood : image ∈ 𝓝 b := by
    apply mem_of_superset ((openU.preimage continuous_subtype_val).mem_nhds
      (show (b : Space) ∈ U from at_center.symm ▸ center))
    intro x hx
    exact covers ⟨hx, x.property⟩
  have member : (b : Space) ∈ chart.map '' chart.domain :=
    ⟨chart.origin, chart.origin_mem, chart.at_origin.trans at_center.symm⟩
  have within : ContinuousWithinAt (fun x : frontier P.body => chart.coordinates x) image b :=
    (chart.coordinates_continuousOn b member).comp continuous_subtype_val.continuousWithinAt
      (fun _ hx => hx)
  exact within.continuousAt neighborhood

/-- Every surface limit at the chart center is also a limit in planar coordinates. -/
theorem center_mem_closure_pullback (S : Set (frontier P.body)) (b : frontier P.body)
    (at_center : (b : Space) = z) (limit : b ∈ closure S) :
    chart.origin ∈ closure (chart.pullback S) := by
  obtain ⟨U, openU, center, covers⟩ := chart.covers
  have near : ∀ᶠ x : frontier P.body in 𝓝 b, (x : Space) ∈ chart.map '' chart.domain := by
    apply mem_of_superset ((openU.preimage continuous_subtype_val).mem_nhds
      (show (b : Space) ∈ U from at_center.symm ▸ center))
    intro x hx
    exact covers ⟨hx, x.property⟩
  letI : NeBot (𝓝[S] b) := mem_closure_iff_nhdsWithin_neBot.mp limit
  have mapped : chart.coordinates b ∈ closure (chart.pullback S) := by
    have tend : Tendsto (fun x : frontier P.body => chart.coordinates x)
        (𝓝[S] b) (𝓝 (chart.coordinates b)) :=
      (chart.coordinates_continuousAt_center b at_center).continuousWithinAt
    apply mem_closure_of_tendsto tend
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds near] with x inside hx
    apply (chart.mem_pullback S _ (chart.coordinates_mem hx)).mpr
    have same : chart.surfaceMap ⟨chart.coordinates x, chart.coordinates_mem hx⟩ = x :=
      Subtype.ext (chart.map_coordinates hx)
    simpa only [same] using inside
  have coordinate : chart.coordinates b = chart.origin := by
    rw [show (b : Space) = chart.map chart.origin from at_center.trans chart.at_origin.symm]
    exact chart.coordinates_map chart.origin_mem
  rwa [coordinate] at mapped

end SixVertexUnfolding.ConvexPolyhedron.FlatChart
