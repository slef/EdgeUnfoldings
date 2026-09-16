import SixVertexUnfolding.Geometry.RadialStripDevelopments
import SixVertexUnfolding.Geometry.OpenCutEdgeStrips

/-! The metric triangle construction is an actual local flat development
at every point of an open strip, including points on original hinges. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A planar disk in an actual flat surface chart, developed isometrically by the given map. -/
structure LocalFlatDisk {P : ConvexPolyhedron} (region : Set (frontier P.body))
    (planar : Set Plane) (H : region ≃ₜ planar) (b : region) where
  chart : P.FlatChart (b.val : Space)
  radius : ℝ
  positive : 0 < radius
  in_domain : Metric.ball chart.origin radius ⊆ chart.domain
  inclusion : C(Metric.ball chart.origin radius, region)
  located : ∀ x, ((inclusion x).val : Space) = chart.map (x : Plane)
  center : inclusion ⟨chart.origin, Metric.mem_ball_self positive⟩ = b
  isometry : Isometry (fun x => (H (inclusion x) : Plane))

namespace RadialStripTriangle

variable {P : ConvexPolyhedron} {routes : C(unitInterval, P.BoundaryCurve)} {p l r : Plane}
  (D : RadialStripTriangle routes p l r)

set_option maxHeartbeats 600000 in
/-- On an open surface region contained in the strip, every nonvertex point has an isometric flat disk. -/
theorem local_flat_disk (U : Set (frontier P.body)) (openU : IsOpen U)
    (contained : U ⊆ range (closedRouteStripMap routes))
    (b : frontier P.body) (bU : b ∈ U) (nonvertex : (b : Space) ∉ P.vertices) :
    Nonempty (LocalFlatDisk _ _ D.homeomorph ⟨b, contained bU⟩) := by
  obtain ⟨chart⟩ := P.exists_flat_chart b.property nonvertex
  let surface : C(chart.domain, frontier P.body) :=
    ⟨fun x => ⟨chart.map x, chart.on_surface x.property⟩,
      (chart.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have center_mem : surface ⟨chart.origin, chart.origin_mem⟩ ∈ U := by
    have same : surface ⟨chart.origin, chart.origin_mem⟩ = b := Subtype.ext chart.at_origin
    rwa [same]
  obtain ⟨r₁, positive₁, in_domain⟩ := Metric.isOpen_iff.mp chart.open_domain chart.origin chart.origin_mem
  obtain ⟨r₂, positive₂, in_U⟩ := Metric.isOpen_iff.mp (openU.preimage surface.continuous)
    ⟨chart.origin, chart.origin_mem⟩ center_mem
  let radius := min r₁ r₂
  have positive : 0 < radius := lt_min positive₁ positive₂
  have domain : Metric.ball chart.origin radius ⊆ chart.domain := by
    intro x hx
    apply in_domain
    exact lt_of_lt_of_le (show dist x chart.origin < min r₁ r₂ from hx) (min_le_left _ _)
  have member (x : Metric.ball chart.origin radius) :
      (⟨chart.map x, chart.on_surface (domain x.property)⟩ : frontier P.body) ∈ U := by
    change surface ⟨(x : Plane), domain x.property⟩ ∈ U
    apply in_U
    change dist (x : Plane) chart.origin < r₂
    exact lt_of_lt_of_le x.property (min_le_right _ _)
  let inclusion : C(Metric.ball chart.origin radius, range (closedRouteStripMap routes)) :=
    ⟨fun x => ⟨⟨chart.map x, chart.on_surface (domain x.property)⟩, contained (member x)⟩,
      ((chart.continuous.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩
  refine ⟨{
    chart := chart
    radius := radius
    positive := positive
    in_domain := domain
    inclusion := inclusion
    located := fun _ => rfl
    center := ?_
    isometry := D.flat_patches chart _ (convex_ball _ _) domain inclusion (fun _ => rfl) }⟩
  exact Subtype.ext (Subtype.ext chart.at_origin)

end RadialStripTriangle

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The chosen branch's triangle is an actual local isometry everywhere in the open surface strip. -/
theorem cut_edge_strip_local_flat_disk (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge)
    (routes : C(unitInterval, P.BoundaryCurve)) (agrees : ∀ t, routes (interiorTime t) = S.first t)
    (p l r : Plane) (D : RadialStripTriangle routes p l r)
    (b : frontier P.body) (inside : b ∈ routeStrip S.first) :
    ∃ hb : b ∈ range (closedRouteStripMap routes), Nonempty (LocalFlatDisk _ _ D.homeomorph ⟨b, hb⟩) := by
  have contained : routeStrip S.first ⊆ range (closedRouteStripMap routes) := by
    rw [← closure_routeStrip_eq S.first routes agrees]
    exact subset_closure
  have outside := graph.routeStrip_outside_cutSet small_faces a _
    (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.first S.first_member b inside
  exact ⟨contained inside, D.local_flat_disk (routeStrip S.first)
    (graph.cut_edge_first_strip_open small_faces a T edge S) contained b inside
    (fun vertex => outside.2 (Or.inr ⟨vertex, outside.1⟩))⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
