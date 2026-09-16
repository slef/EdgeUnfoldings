import SixVertexUnfolding.Geometry.NextWedgeParameters
import SixVertexUnfolding.Geometry.JunctionEdgeTransitions

/-! The incoming wedge of an incident edge is determined by the actual
metric triangle. Every transition preserving the two roots carries the
returned wedge to this same incoming wedge, including reflected charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron.IncidentTriangles

open Real Set EuclideanGeometry Wedge

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v}
    {first_chart : P.CutVoronoiChart a (T.vertexTarget u)}
    {second_chart : P.CutVoronoiChart a (T.vertexTarget v)} {θ φ : ℝ}
    (D : IncidentTriangles T edge first_chart θ)
    (E : IncidentTriangles T edge.symm second_chart φ)

/-- The symmetric wedge for entering along this actual incident edge. -/
def incomingWedge (ω : ℝ) : Set Plane :=
  {x | x - first_chart.origin ∈ polarRegion (P.surfaceDist a (T.vertexTarget u)) ω
    (θ - angle D.model.first D.model.left D.model.right)
    (θ + angle D.model.first D.model.left D.model.right)}

/-- Triangle corner agreement identifies the entire returned wedge across
an edge. This works for the same motion that aligns the full triangle maps. -/
theorem next_wedge_image (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (old_root : motion first_chart.origin =
      second_chart.origin + dist (v : Space) (u : Space) • direction φ)
    (next_root : motion (first_chart.origin + dist (u : Space) (v : Space) • direction θ) =
      second_chart.origin)
    {radius Θ : ℝ} (radius_eq : radius = P.surfaceDist a (T.vertexTarget v))
    (corner_eq : π - Θ = angle D.model.first D.model.right D.model.left) (ω : ℝ) :
    motion '' {x | x - (first_chart.origin + dist (u : Space) (v : Space) • direction θ) ∈
      polarRegion radius ω (Θ + θ) (2 * π - Θ + θ)} = E.incomingWedge ω := by
  have length_positive : 0 < dist (u : Space) (v : Space) := by
    apply dist_pos.mpr
    intro same
    exact edge.ne (Subtype.ext same)
  have half : π - Θ = angle E.model.first E.model.left E.model.right :=
    corner_eq.trans (D.model.reverse_angles E.model).2.2
  have on_axis : motion ((first_chart.origin + dist (u : Space) (v : Space) • direction θ) +
      dist (u : Space) (v : Space) • direction (θ + π)) =
        second_chart.origin + dist (u : Space) (v : Space) • direction φ := by
    rw [next_root_back_ray, old_root, dist_comm (v : Space) (u : Space)]
  have result := centered_wedge_image motion
    (first_chart.origin + dist (u : Space) (v : Space) • direction θ) second_chart.origin
    length_positive next_root on_axis radius ω (π - Θ)
  rw [show θ + π - (π - Θ) = Θ + θ by ring,
    show θ + π + (π - Θ) = 2 * π - Θ + θ by ring, radius_eq, half] at result
  simpa only [radius_eq, incomingWedge] using result

end SixVertexUnfolding.ConvexPolyhedron.IncidentTriangles
