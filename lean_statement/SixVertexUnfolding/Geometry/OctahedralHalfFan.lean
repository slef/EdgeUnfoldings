import SixVertexUnfolding.Geometry.HalfFanMetric
import SixVertexUnfolding.Geometry.OctahedralSelection

/-! The half-fan angular estimates for developed patches of the actual six-vertex solid. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles EuclideanGeometry Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- A developed petal apex is seen within half the fan angle sum from either equator endpoint.
The distance premise is supplied by opposite-side flattening of the two triangles. -/
theorem developed_petal_angle_bound (source : Fin 6) (i : Fin 4) (W V U : Plane)
    (wu : dist W U = dist (graph.vertex (opposite source) : Space) (graph.vertex (fanNeighbor source i)))
    (vu : dist V U = dist (graph.vertex source : Space) (graph.vertex (fanNeighbor source i)))
    (longer : dist (graph.vertex (opposite source) : Space) (graph.vertex source) ≤ dist W V)
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π) :
    2 * angle U W V < graph.totalAngleAt (opposite source) := by
  let w : Space := graph.vertex (opposite source)
  let v : Space := graph.vertex source
  let u : Space := graph.vertex (fanNeighbor source i)
  have uv : fanNeighbor source i ≠ source := fanNeighbor_ne_source source i
  have uw : fanNeighbor source i ≠ opposite source :=
    (by decide : ∀ s j, fanNeighbor s j ≠ opposite s) source i
  have wv : w ≠ v := fun same => opposite_ne source (graph.vertex.injective (Subtype.ext same))
  have wu_ne : w ≠ u := fun same => uw (graph.vertex.injective (Subtype.ext same)).symm
  have fan_link := graph.vertex_link_bound small_faces (opposite source) (fanNeighbor source i) source
    uw (opposite_ne source).symm (by simpa only [opposite_opposite] using uv)
  change 2 * angle u w v < graph.totalAngleAt (opposite source) at fan_link
  by_cases nonobtuse : dist w u ^ 2 ≤ dist v u ^ 2 + dist w v ^ 2
  · have bound := HalfFan.viewing_angle_le w v u W V U wu vu longer wu_ne wv nonobtuse
    linarith
  · have acute := HalfFan.viewing_angle_acute w v u W V U wu vu longer wu_ne wv
      (lt_of_not_ge nonobtuse)
    have source_link := graph.vertex_link_bound small_faces source (fanNeighbor source i) (opposite source)
      uv (opposite_ne source) uw
    change 2 * angle u v w < graph.totalAngleAt source at source_link
    have beta_obtuse : π / 2 < angle u v w := by
      have law := law_cos u v w
      simp only [dist_comm u w, dist_comm u v, ← sq] at law
      by_contra not_obtuse
      have cosine : 0 ≤ cos (angle u v w) :=
        cos_nonneg_of_neg_pi_div_two_le_of_le
          (by linarith [angle_nonneg u v w, pi_pos]) (le_of_not_gt not_obtuse)
      have product := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (dist_nonneg : 0 ≤ dist v u)) (dist_nonneg : 0 ≤ dist w v)) cosine
      linarith
    have source_low : graph.curvature source < π := by
      unfold curvature
      linarith
    have fan_low : graph.curvature (opposite source) ≤ π := by
      rcases alternative with high | low
      · linarith
      · exact low
    unfold curvature at fan_low
    linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
