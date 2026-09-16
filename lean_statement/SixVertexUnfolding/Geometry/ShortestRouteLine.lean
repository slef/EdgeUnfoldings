import SixVertexUnfolding.Geometry.ShortestFlatCoordinates
import SixVertexUnfolding.Geometry.GeodesicCurvePaths
import SixVertexUnfolding.Geometry.CutRayCoordinates
import SixVertexUnfolding.Geometry.FlatChartRegions
import SixVertexUnfolding.Geometry.PlaneOrientation

/-! Near an interior nonvertex point, the entire shortest-route trace
lies on one line in a flat chart. Compactness excludes distant portions
of the route returning to the neighborhood. -/

namespace SixVertexUnfolding

open Set

/-- A line through two distinct planar points has a nonzero normal. -/
theorem plane_line_normal (p q : Plane) (different : p ≠ q) :
    ∃ normal : Plane, normal ≠ 0 ∧ ∀ t : ℝ,
      inner ℝ normal (AffineMap.lineMap p q t) = inner ℝ normal p := by
  let normal : Plane := !₂[-(q 1 - p 1), q 0 - p 0]
  have nonzero : normal ≠ 0 := by
    intro zero
    have first := congrArg (fun x : Plane => x 0) zero
    have second := congrArg (fun x : Plane => x 1) zero
    change -(q 1 - p 1) = 0 at first
    change q 0 - p 0 = 0 at second
    apply different
    ext i
    fin_cases i
    · change p 0 = q 0
      linarith
    · change p 1 = q 1
      linarith
  refine ⟨normal, nonzero, ?_⟩
  intro t
  have same : inner ℝ normal q = inner ℝ normal p := by
    simp only [plane_inner_coordinates]
    change -(q 1 - p 1) * q 0 + (q 0 - p 0) * q 1 =
      -(q 1 - p 1) * p 0 + (q 0 - p 0) * p 1
    ring
  rw [AffineMap.lineMap_apply_module, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, same]
  ring

namespace ConvexPolyhedron

/-- The whole route trace, restricted to a small chart disk, is contained in one line. -/
theorem shortest_route_line_chart (P : ConvexPolyhedron) (a b : frontier P.body)
    (different : a ≠ b) (f : P.BoundaryCurve) (member : f ∈ P.geodesicFiber a b)
    (m : unitInterval) (after_start : 0 < m) (before_end : m < 1)
    (nonvertex : (f m : Space) ∉ P.vertices) :
    ∃ chart : P.FlatChart (f m : Space), ∃ normal : Plane, ∃ height radius : ℝ,
      normal ≠ 0 ∧ 0 < radius ∧ Metric.ball chart.origin radius ⊆ chart.domain ∧
      ∀ x, x ∈ Metric.ball chart.origin radius →
        chart.map x ∈ (Subtype.val : frontier P.body → Space) '' range f →
          inner ℝ normal x = height := by
  let path := P.surfacePathOfCurve f
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f member.1
  obtain ⟨chart, s, t, sm, mt, contained, straight⟩ :=
    path.exists_local_affine_coordinates shortest finite speed m after_start before_end nonvertex
  have injective : Function.Injective path.curve := by
    intro u v same
    exact P.geodesicFiber_injective a b different f member (Subtype.ext same)
  have endpoints_different : chart.coordinates (path.curve s) ≠ chart.coordinates (path.curve t) := by
    intro same
    have positions := congrArg chart.map same
    rw [chart.map_coordinates (contained s ⟨le_rfl, sm.le.trans mt.le⟩),
      chart.map_coordinates (contained t ⟨sm.le.trans mt.le, le_rfl⟩)] at positions
    exact (sm.trans mt).ne (injective positions)
  obtain ⟨normal, nonzero, on_line⟩ := plane_line_normal _ _ endpoints_different
  let missing : Set Space := path.curve '' (Ioo s t)ᶜ
  have closed_missing : IsClosed missing :=
    (isOpen_Ioo.isClosed_compl.isCompact.image path.curve.continuous).isClosed
  have center_not_missing : path.curve m ∉ missing := by
    rintro ⟨u, outside, equal⟩
    exact outside (injective equal ▸ show m ∈ Ioo s t from ⟨sm, mt⟩)
  have open_near : IsOpen (chart.domain ∩ chart.map ⁻¹' missingᶜ) :=
    chart.open_domain.inter (closed_missing.isOpen_compl.preimage chart.continuous)
  have center_near : chart.origin ∈ chart.domain ∩ chart.map ⁻¹' missingᶜ :=
    ⟨chart.origin_mem, by simpa only [mem_preimage, chart.at_origin] using center_not_missing⟩
  obtain ⟨radius, positive, near⟩ := Metric.isOpen_iff.mp open_near chart.origin center_near
  refine ⟨chart, normal, inner ℝ normal (chart.coordinates (path.curve s)), radius,
    nonzero, positive, fun x hx => (near hx).1, ?_⟩
  intro x hx on_route
  obtain ⟨_, ⟨u, rfl⟩, at_x⟩ := on_route
  have middle : u ∈ Ioo s t := by
    by_contra outside
    exact (near hx).2 ⟨u, outside, at_x⟩
  have coordinates : chart.coordinates (path.curve u) = x := by
    change chart.coordinates (f u : Space) = x
    rw [at_x]
    exact chart.coordinates_map (near hx).1
  rw [← coordinates, straight u ⟨middle.1.le, middle.2.le⟩]
  exact on_line _

end ConvexPolyhedron
end SixVertexUnfolding
