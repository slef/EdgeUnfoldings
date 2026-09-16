import SixVertexUnfolding.Geometry.JunctionFan
import SixVertexUnfolding.Geometry.GapKiteStep

/-! The kite used by the planar inequalities is exactly the union of
the two actual triangle developments in their common junction chart. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Real Set Wedge

namespace IncidentTriangles

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v}
    {chart : P.CutVoronoiChart a (T.vertexTarget u)} {θ : ℝ}

/-- The two triangle images keep their distinct planar source copies. -/
def developedKite (D : IncidentTriangles T edge chart θ) : Set Plane :=
  convexHull ℝ ({D.motion D.model.first, D.motion D.model.left, D.motion D.model.right} : Set Plane) ∪
    convexHull ℝ ({D.motion D.model.second, D.motion D.model.left, D.motion D.model.right} : Set Plane)

end IncidentTriangles

namespace JunctionFan

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

/-- The actual two source labels are exactly the endpoints of the assigned gap. -/
theorem gap_source_pair
    (m : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    {α β : ℝ} (gap : IsCircularGap fan.order.angles fan.order.first fan.order.last α β)
    (midpoint : (m : ℝ) = (α + β) / 2) :
    let D := fan.triangles m
    ({D.motion D.model.first, D.motion D.model.second} : Set Plane) =
      {fan.order.chart.origin + P.surfaceDist a (T.vertexTarget u) • direction α,
        fan.order.chart.origin + P.surfaceDist a (T.vertexTarget u) • direction β} := by
  dsimp only
  let D := fan.triangles m
  obtain ⟨ordered, width, _, _, first, second, empty_gap⟩ := circular_gap_spec
    fan.order.sites fan.order.angles fan.order.increasing fan.order.bounds fan.order.chart.origin
    (P.surfaceDist a (T.vertexTarget u)) fan.order.position fan.order.first fan.order.last
    fan.order.at_first fan.order.at_last fan.order.two gap
  have on_ray (ρ : ℝ) (hr : ρ ∈ Ioo (0 : ℝ) fan.order.radius) :
      fan.order.chart.map (fan.order.chart.origin + ρ • direction ((α + β) / 2)) ∈
        openSegment ℝ (T.vertexTarget u : Space) ((fan.order.neighbors m).val : Space) := by
    rw [← midpoint]
    exact fan.order.rays m ρ hr
  have left := fan.order.chart.incident_branch_source T (fan.order.neighbors m).property rfl
    D.first (fun t => (D.member t).1) D.first_label ordered width first second empty_gap
    fan.order.radius_positive on_ray
  have right := fan.order.chart.incident_branch_source T (fan.order.neighbors m).property rfl
    D.second (fun t => (D.member t).2) D.second_label ordered width first second empty_gap
    fan.order.radius_positive on_ray
  have different : D.motion D.model.first ≠ D.motion D.model.second :=
    D.motion.injective.ne D.model.distinct_sources
  rcases left with l | l <;> rcases right with r | r
  · exact (different (l.trans r.symm)).elim
  · rw [l, r]
  · rw [l, r, pair_comm]
  · exact (different (l.trans r.symm)).elim

/-- No surrogate kite is used: both full developed triangles form exactly this gap kite. -/
theorem developed_kite_eq
    (m : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    {α β : ℝ} (gap : IsCircularGap fan.order.angles fan.order.first fan.order.last α β)
    (midpoint : (m : ℝ) = (α + β) / 2) :
    (fan.triangles m).developedKite = gapKite fan.order.chart.origin
      (P.surfaceDist a (T.vertexTarget u))
      (dist (u : Space) ((fan.order.neighbors m).val : Space)) α β := by
  have pair := fan.gap_source_pair m gap midpoint
  let z := fan.order.chart.origin
  let y := z + dist (u : Space) ((fan.order.neighbors m).val : Space) • direction m
  have union_pairs (p q : Plane) :
      convexHull ℝ ({p, z, y} : Set Plane) ∪ convexHull ℝ ({q, z, y} : Set Plane) =
        ⋃ s ∈ ({p, q} : Set Plane), convexHull ℝ ({s, z, y} : Set Plane) := by simp
  unfold IncidentTriangles.developedKite
  rw [(fan.triangles m).at_junction, (fan.triangles m).at_neighbor]
  change convexHull ℝ ({_, z, y} : Set Plane) ∪ convexHull ℝ ({_, z, y} : Set Plane) = _
  rw [union_pairs, pair, ← union_pairs]
  dsimp [z, y]
  rw [midpoint]
  unfold gapKite
  rw [union_comm]
  apply congrArg₂ (fun A B : Set Plane => A ∪ B)
  · apply congrArg (convexHull ℝ)
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  · apply congrArg (convexHull ℝ)
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto

end JunctionFan
end SixVertexUnfolding.ConvexPolyhedron
