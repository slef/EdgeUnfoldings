import SixVertexUnfolding.Geometry.JunctionGapChart
import SixVertexUnfolding.Geometry.CircularGapSum

/-! The actual incident triangles cover a full disk in a junction's
flat chart. Their surface maps agree with that chart throughout the disk. -/

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionFan

open Set Real

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

/-- Some actual incident triangle places the surface chart point at these coordinates. -/
def chartPlaces (x : Plane) : Prop :=
  ∃ inside : x ∈ fan.order.chart.domain,
    ∃ m : circularGapMidpoints fan.order.angles fan.order.first fan.order.last,
      (fan.triangles m).placed.Places
        ⟨fan.order.chart.map x, fan.order.chart.on_surface inside⟩ x

theorem chartPlaces_origin : fan.chartPlaces fan.order.chart.origin := by
  let m : circularGapMidpoints fan.order.angles fan.order.first fan.order.last :=
    ⟨(fan.order.angles fan.order.last + (fan.order.angles fan.order.first + 2 * π)) / 2, Or.inr rfl⟩
  let D := fan.triangles m
  refine ⟨fan.order.chart.origin_mem, m, ?_⟩
  apply (D.placed.places_iff_ray _ _).mpr
  refine ⟨0, false, 1, ?_, ?_⟩
  · apply Subtype.ext
    have endpoint := congrArg Prod.snd (D.member 0).1.2
    rw [T.closedEdgeTarget_zero] at endpoint
    exact (congrArg (fun b : frontier P.body => (b : Space)) endpoint).trans fan.order.chart.at_origin.symm
  · change AffineMap.lineMap (D.motion D.model.first)
      (AffineMap.lineMap (D.motion D.model.left) (D.motion D.model.right) 0) 1 = _
    rw [AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, D.at_junction]

/-- The finite angular sectors give a genuine planar neighborhood, including all sector boundaries. -/
theorem exists_chart_disk :
    ∃ ε > 0, ∀ x ∈ Metric.ball fan.order.chart.origin ε, fan.chartPlaces x := by
  classical
  let θ := fan.order.angles
  let m (i : Fin fan.order.chart.sources.ncard) :
      circularGapMidpoints θ fan.order.first fan.order.last :=
    (circularGapMidpointEquiv θ fan.order.increasing fan.order.bounds
      fan.order.first fan.order.last fan.order.at_last) i
  have sectors (i : Fin fan.order.chart.sources.ncard) :
      ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε,
        ∀ φ ∈ Icc (θ i) (circularGapEnd θ fan.order.first i),
          fan.chartPlaces (fan.order.chart.origin + ρ • direction φ) := by
    obtain ⟨ε, positive, covered⟩ := fan.exists_gap_chart_sector (m i)
      (circularGapEnd_gap θ fan.order.first fan.order.last i fan.order.at_last) rfl
    refine ⟨ε, positive, ?_⟩
    intro ρ hr φ hφ
    obtain ⟨inside, placed⟩ := covered ρ hr φ hφ
    exact ⟨inside, m i, placed⟩
  choose ε positive sector using sectors
  obtain ⟨j, _, minimal⟩ := Finset.univ.exists_min_image ε
    (show (Finset.univ : Finset (Fin fan.order.chart.sources.ncard)).Nonempty from
      ⟨fan.order.first, Finset.mem_univ _⟩)
  refine ⟨ε j, positive j, ?_⟩
  intro x hx
  by_cases center : x = fan.order.chart.origin
  · exact center.symm ▸ fan.chartPlaces_origin
  let ρ := dist x fan.order.chart.origin
  have rp : 0 < ρ := dist_pos.mpr center
  have short (i : Fin fan.order.chart.sources.ncard) : ρ < ε i :=
    (Metric.mem_ball.mp hx).trans_le (minimal i (Finset.mem_univ _))
  obtain ⟨φ, low, high, expression⟩ := circle_point_angle rp (show dist x fan.order.chart.origin = ρ from rfl)
  rcases circular_gaps_cover_direction θ fan.order.increasing fan.order.bounds
      fan.order.first fan.order.last ⟨low, high⟩ with
    ⟨i, k, next, in_gap⟩ | ⟨ψ, in_gap, same_direction⟩
  · have gap_end : circularGapEnd θ fan.order.first i = θ k := by
      have inside : i.val + 1 < fan.order.chart.sources.ncard := by omega
      rw [circularGapEnd, dif_pos inside]
      congr 1
      exact Fin.ext next.symm
    have placed := sector i ρ ⟨rp, short i⟩ φ (by rwa [gap_end])
    exact expression.symm ▸ placed
  · have gap_end : circularGapEnd θ fan.order.first fan.order.last = θ fan.order.first + 2 * π := by
      simp [circularGapEnd, fan.order.at_last]
    have placed := sector fan.order.last ρ ⟨rp, short _⟩ ψ (by rwa [gap_end])
    have representation : x = fan.order.chart.origin + ρ • direction ψ := expression.trans (by rw [same_direction])
    exact representation.symm ▸ placed

end SixVertexUnfolding.ConvexPolyhedron.JunctionFan
