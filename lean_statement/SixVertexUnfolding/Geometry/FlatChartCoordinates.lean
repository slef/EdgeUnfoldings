import SixVertexUnfolding.Geometry.SurfaceFlatCharts
import SixVertexUnfolding.Geometry.SurfaceDistanceTopology

/-! Flat charts have continuous inverse coordinates in the existing boundary
topology. Their metric assertions therefore describe genuine local charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FlatChart

open Set Filter
open scoped Topology

variable {P : ConvexPolyhedron} {z : Space} (chart : P.FlatChart z)

theorem image_on_surface : chart.map '' chart.domain ⊆ frontier P.body := by
  rintro _ ⟨x, hx, rfl⟩
  exact chart.on_surface hx

/-- Metric preservation rules out identifications in the planar domain. -/
theorem injective : Set.InjOn chart.map chart.domain := by
  intro x hx y hy same
  apply dist_eq_zero.mp
  rw [← chart.distance x hx y hy, same, P.surfaceDist_self (chart.on_surface hy)]

/-- The chart is a bijection onto its actual surface image. -/
noncomputable def imageEquiv : chart.domain ≃ chart.map '' chart.domain :=
  Equiv.ofBijective (fun x => ⟨chart.map x, ⟨x, x.property, rfl⟩⟩)
    ⟨fun x y same => Subtype.ext (chart.injective x.property y.property (congrArg Subtype.val same)),
      fun y => by obtain ⟨x, hx, equal⟩ := y.property; exact ⟨⟨x, hx⟩, Subtype.ext equal⟩⟩

theorem imageEquiv_apply (x : chart.domain) : (chart.imageEquiv x : Space) = chart.map x := rfl

theorem map_inverse (x : chart.map '' chart.domain) : chart.map (chart.imageEquiv.symm x) = x :=
  congrArg Subtype.val (chart.imageEquiv.apply_symm_apply x)

/-- Inverse coordinate distances are exactly the intrinsic distances of their surface points. -/
theorem inverse_distance (x y : chart.map '' chart.domain) :
    dist (chart.imageEquiv.symm x) (chart.imageEquiv.symm y) = P.surfaceDist x y := by
  change dist (chart.imageEquiv.symm x : Plane) (chart.imageEquiv.symm y : Plane) = _
  rw [← chart.distance _ (chart.imageEquiv.symm x).property _ (chart.imageEquiv.symm y).property,
    chart.map_inverse, chart.map_inverse]

/-- The inverse coordinates are continuous for the actual Euclidean subspace topology. -/
theorem inverse_continuous : Continuous chart.imageEquiv.symm := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε positive
  have distance_continuous : Continuous (fun y : chart.map '' chart.domain => P.surfaceDist x y) :=
    ((P.surfaceDist_continuousOn (chart.image_on_surface x.property)).mono chart.image_on_surface).restrict
  have near : ∀ᶠ y : chart.map '' chart.domain in 𝓝 x, P.surfaceDist x y < ε :=
    distance_continuous.continuousAt.eventually_lt_const (show P.surfaceDist x x < ε by
      rw [P.surfaceDist_self (chart.image_on_surface x.property)]; exact positive)
  filter_upwards [near] with y hy
  rw [chart.inverse_distance, P.surfaceDist_comm]
  exact hy

/-- The chart and its continuous inverse form an explicit homeomorphism onto the surface image. -/
noncomputable def homeomorphImage : chart.domain ≃ₜ chart.map '' chart.domain where
  toEquiv := chart.imageEquiv
  continuous_toFun := (chart.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := chart.inverse_continuous

/-- Coordinates are used only on the chart image; the value elsewhere is a harmless default. -/
noncomputable def coordinates (x : Space) : Plane := by
  classical
  exact if hx : x ∈ chart.map '' chart.domain then chart.imageEquiv.symm ⟨x, hx⟩ else chart.origin

theorem coordinates_mem {x : Space} (hx : x ∈ chart.map '' chart.domain) :
    chart.coordinates x ∈ chart.domain := by
  classical
  simpa only [coordinates, dif_pos hx] using (chart.imageEquiv.symm ⟨x, hx⟩).property

theorem map_coordinates {x : Space} (hx : x ∈ chart.map '' chart.domain) :
    chart.map (chart.coordinates x) = x := by
  classical
  simpa only [coordinates, dif_pos hx] using chart.map_inverse ⟨x, hx⟩

theorem coordinates_map {x : Plane} (hx : x ∈ chart.domain) : chart.coordinates (chart.map x) = x :=
  chart.injective (chart.coordinates_mem ⟨x, hx, rfl⟩) hx (chart.map_coordinates ⟨x, hx, rfl⟩)

/-- The distance formula can be used directly for surface points in the chart image. -/
theorem coordinates_distance {x y : Space} (hx : x ∈ chart.map '' chart.domain)
    (hy : y ∈ chart.map '' chart.domain) :
    dist (chart.coordinates x) (chart.coordinates y) = P.surfaceDist x y := by
  rw [← chart.distance _ (chart.coordinates_mem hx) _ (chart.coordinates_mem hy),
    chart.map_coordinates hx, chart.map_coordinates hy]

theorem coordinates_continuousOn : ContinuousOn chart.coordinates (chart.map '' chart.domain) := by
  rw [continuousOn_iff_continuous_restrict]
  convert continuous_subtype_val.comp chart.inverse_continuous using 1
  funext x
  classical
  simp only [restrict_apply, coordinates, dif_pos x.property]
  rfl

end SixVertexUnfolding.ConvexPolyhedron.FlatChart
