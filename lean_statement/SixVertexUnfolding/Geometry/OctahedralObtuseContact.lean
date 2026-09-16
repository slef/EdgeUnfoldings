import SixVertexUnfolding.Geometry.OctahedralPatch
import SixVertexUnfolding.Geometry.ContactProjectionAt

/-! The contact projection obstruction forces the actual source curvature below pi. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles EuclideanGeometry Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- An obtuse triangle angle at the source forces its curvature below pi, by the strict closed-link bound. -/
theorem source_curvature_lt_pi_of_obtuse (source : Fin 6) (i : Fin 4)
    (obtuse : dist (graph.vertex source : Space) (graph.vertex (fanNeighbor source i)) ^ 2 +
      dist (graph.vertex (opposite source) : Space) (graph.vertex source) ^ 2 <
        dist (graph.vertex (opposite source) : Space) (graph.vertex (fanNeighbor source i)) ^ 2) :
    graph.curvature source < π := by
  let w : Space := graph.vertex (opposite source)
  let v : Space := graph.vertex source
  let u : Space := graph.vertex (fanNeighbor source i)
  have link := graph.vertex_link_bound small_faces source (fanNeighbor source i) (opposite source)
    (fanNeighbor_ne_source source i) (opposite_ne source)
    ((by decide : ∀ s j, fanNeighbor s j ≠ opposite s) source i)
  change 2 * angle u v w < graph.totalAngleAt source at link
  have beta_obtuse : π / 2 < angle u v w := by
    have law := law_cos u v w
    simp only [dist_comm u w, dist_comm u v, ← sq] at law
    change dist v u ^ 2 + dist w v ^ 2 < dist w u ^ 2 at obtuse
    by_contra not_obtuse
    have cosine : 0 ≤ cos (angle u v w) := cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [angle_nonneg u v w, pi_pos]) (le_of_not_gt not_obtuse)
    have product := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (dist_nonneg : 0 ≤ dist v u)) (dist_nonneg : 0 ≤ dist w v)) cosine
    linarith
  unfold curvature
  linarith

namespace DevelopedPatch

variable {graph small_faces} {source : Fin 6} {sector : Fin 4}
variable (patch : graph.DevelopedPatch source sector)

include small_faces in
/-- Only the contact containment remains geometric here; outward flattening supplies the pole-distance comparison. -/
theorem source_curvature_lt_pi_of_contact_containment (p : Plane)
    (apex_ne : patch.apex ≠ patch.right) (equal_radius : dist p patch.right = dist patch.apex patch.right)
    (different : patch.apex ≠ p) (t : ℝ) (lower : 0 ≤ t) (upper : t ≤ 1)
    (contained : patch.apex ∈ convexHull ℝ
      ({patch.right, patch.pole, patch.right + t • (p - patch.right)} : Set Plane))
    (not_pole : patch.apex ≠ patch.pole) : graph.curvature source < π := by
  have metric := Contact.contact_metric_obtuse_at patch.right patch.pole patch.apex p apex_ne
    equal_radius different t lower upper contained not_pole
  apply graph.source_curvature_lt_pi_of_obtuse small_faces source (sector + 1)
  rw [patch.petal_right, patch.fan_right] at metric
  have squared := sq_le_sq₀ (dist_nonneg : 0 ≤ dist (graph.vertex (opposite source) : Space) (graph.vertex source))
    (dist_nonneg : 0 ≤ dist patch.pole patch.apex)
  have comparison := squared.mpr patch.pole_distance_ge
  linarith

end DevelopedPatch
end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
