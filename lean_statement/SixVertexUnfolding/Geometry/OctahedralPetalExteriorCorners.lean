import SixVertexUnfolding.Geometry.OctahedralStrictCorners
import SixVertexUnfolding.Geometry.OctahedralPlacedTopology
import SixVertexUnfolding.Geometry.RadialTriangleCorners
import SixVertexUnfolding.Geometry.ClockwiseQuadrilateralAngles

/-! A ray into a petal leaves at least the complementary two-face angle outside its patch. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- At a left endpoint, the pocket corner contains the complement of the adjoining patch. -/
theorem petal_left_exterior_corner (i : Fin 4) (p : Plane)
    (member : p ∈ net.placedTriangle (true, i)) (different : p ≠ (net.patch i).left) :
    2 * π - (net.patch i).leftCorner ≤ clockwiseCorner 0 (net.patch i).left p := by
  let θ := graph.openingAngle (opposite source) slit i.castSucc
  let f := angle 0 (net.patch i).left (net.patch i).right
  let R := dist (graph.vertex (opposite source) : Space)
    (graph.vertex (openingVertex (opposite source) slit i.castSucc))
  have bounds := (net.patch i).left_face_angle_bounds
  rw [net.patch_pole i] at bounds
  have corner : (net.patch i).leftCorner = f + angle (net.patch i).right (net.patch i).left (net.patch i).apex := by
    simp only [DevelopedPatch.leftCorner, net.patch_pole, f]
  have base_pos := dist_pos.mpr (ne₁₂_of_not_collinear (net.patch i).petal_noncollinear)
  have apex_pos := dist_pos.mpr (ne₁₃_of_not_collinear (net.patch i).petal_noncollinear).symm
  have translated := triangle_sub_vertex (net.patch i).left (net.patch i).right (net.patch i).apex p
    (by simpa only [net.placedTriangle_hull, if_true] using member)
  rw [net.patch_base_direction_left, net.patch_apex_direction_left] at translated
  have pole : 0 - (net.patch i).left = R • direction (θ + π) := by
    simp only [net.patch_left, openingPoint, θ, R, direction_add_pi, smul_neg, zero_sub]
  unfold clockwiseCorner
  rw [pole]
  have estimate := counterclockwiseAngle_from_later_ray
    (dist (net.patch i).apex (net.patch i).left) (dist (net.patch i).left (net.patch i).right) R
    (θ + π - (net.patch i).leftCorner) (θ + π - f) (θ + π)
    apex_pos base_pos (graph.opening_radius_pos _ _ _)
    (by dsimp [f]; linarith [bounds.2.2.1])
    (by dsimp [f]; linarith [bounds.2.2.2])
    (by dsimp [f]; linarith [bounds.1])
    (by linarith [(net.patch i).leftCorner_lt_two_pi])
    (p - (net.patch i).left) (sub_ne_zero.mpr different)
    (by simpa only [Set.pair_comm, θ, f] using translated)
  linarith

/-- The mirrored exterior corner at a right endpoint satisfies the same complement bound. -/
theorem petal_right_exterior_corner (i : Fin 4) (p : Plane)
    (member : p ∈ net.placedTriangle (true, i)) (different : p ≠ (net.patch i).right) :
    2 * π - (net.patch i).rightCorner ≤ clockwiseCorner p (net.patch i).right 0 := by
  let θ := graph.openingAngle (opposite source) slit i.succ
  let f := angle 0 (net.patch i).right (net.patch i).left
  let R := dist (graph.vertex (opposite source) : Space)
    (graph.vertex (openingVertex (opposite source) slit i.succ))
  have bounds := (net.patch i).right_face_angle_bounds
  rw [net.patch_pole i] at bounds
  have corner : (net.patch i).rightCorner = f + angle (net.patch i).left (net.patch i).right (net.patch i).apex := by
    simp only [DevelopedPatch.rightCorner, net.patch_pole, f]
  have base_pos := dist_pos.mpr (ne₁₂_of_not_collinear (net.patch i).petal_noncollinear)
  have apex_pos := dist_pos.mpr (ne₂₃_of_not_collinear (net.patch i).petal_noncollinear).symm
  have translated := triangle_sub_vertex (net.patch i).right (net.patch i).left (net.patch i).apex p
    (by simpa only [net.placedTriangle_hull, if_true, Set.insert_comm] using member)
  rw [net.patch_base_direction_right, net.patch_apex_direction_right] at translated
  have pole : 0 - (net.patch i).right = R • direction (θ - π) := by
    simp only [net.patch_right, openingPoint, θ, R, direction_sub_pi, smul_neg, zero_sub]
  unfold clockwiseCorner
  rw [pole]
  have estimate := counterclockwiseAngle_to_earlier_ray
    (dist (net.patch i).left (net.patch i).right) (dist (net.patch i).apex (net.patch i).right) R
    (θ - π + f) (θ - π + (net.patch i).rightCorner) (θ - π)
    base_pos apex_pos (graph.opening_radius_pos _ _ _)
    (by dsimp [f]; linarith [bounds.2.2.1])
    (by dsimp [f]; linarith [bounds.2.2.2])
    (by dsimp [f]; linarith [bounds.1])
    (by linarith [(net.patch i).rightCorner_lt_two_pi])
    (p - (net.patch i).right) (sub_ne_zero.mpr different) translated
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
