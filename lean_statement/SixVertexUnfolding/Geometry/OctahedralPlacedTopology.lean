import SixVertexUnfolding.Geometry.OctahedralJunctionTriangles
import SixVertexUnfolding.Geometry.TriangleTopology
import SixVertexUnfolding.Geometry.TriangleBoundary

/-! Closedness, convexity, nonempty interior, and boundary density for all eight actual placed triangles. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles OctahedralNet

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem placedTriangle_hull (index : FaceIndex) : net.placedTriangle index =
    convexHull ℝ ({(net.patch index.2).left, (net.patch index.2).right,
      if index.1 then (net.patch index.2).apex else (net.patch index.2).pole} : Set Plane) := by
  obtain ⟨petal, i⟩ := index
  have rotate (a b c : Plane) : ({a, b, c} : Set Plane) = {b, c, a} := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  cases petal
  · change net.fan.place i '' graph.triangle (fanTriangle (opposite source) (slit + i)) = _
    rw [net.fan_triangle, rotate]
    rfl
  · change net.petal i '' graph.triangle (fanTriangle source (slit + i)) = _
    rw [net.petal_triangle, rotate]
    rfl

theorem placedTriangle_noncollinear (index : FaceIndex) :
    ¬ Collinear ℝ ({(net.patch index.2).left, (net.patch index.2).right,
      if index.1 then (net.patch index.2).apex else (net.patch index.2).pole} : Set Plane) := by
  obtain ⟨petal, i⟩ := index
  cases petal
  · exact (net.patch i).fan_noncollinear
  · exact (net.patch i).petal_noncollinear

theorem placedTriangle_convex (index : FaceIndex) : Convex ℝ (net.placedTriangle index) := by
  rw [net.placedTriangle_hull]
  exact convex_convexHull ℝ _

theorem placedTriangle_closed (index : FaceIndex) : IsClosed (net.placedTriangle index) := by
  rw [net.placedTriangle_hull]
  exact (Set.toFinite _).isClosed_convexHull ℝ

theorem placedTriangle_regular (index : FaceIndex) :
    closure (interior (net.placedTriangle index)) = net.placedTriangle index := by
  rw [net.placedTriangle_hull]
  exact planar_triangle_regular _ _ _ (net.placedTriangle_noncollinear index)

theorem placedTriangle_interior_nonempty (index : FaceIndex) : (interior (net.placedTriangle index)).Nonempty := by
  rw [net.placedTriangle_hull]
  exact planar_triangle_interior_nonempty _ _ _ (net.placedTriangle_noncollinear index)

theorem Separated.interior_disjoint_closed {a b : FaceIndex} (safe : net.Separated a b) :
    Disjoint (interior (net.placedTriangle a)) (net.placedTriangle b) := by
  have closed_safe := Disjoint.closure_right safe isOpen_interior
  rwa [net.placedTriangle_regular] at closed_safe

theorem patch_left_mem (petal : Bool) (i : Fin 4) : (net.patch i).left ∈ net.placedTriangle (petal, i) := by
  rw [net.placedTriangle_hull]
  exact subset_convexHull ℝ _ (by simp)

theorem patch_right_mem (petal : Bool) (i : Fin 4) : (net.patch i).right ∈ net.placedTriangle (petal, i) := by
  rw [net.placedTriangle_hull]
  exact subset_convexHull ℝ _ (by simp)

theorem fan_pole_mem (i : Fin 4) : (0 : Plane) ∈ net.placedTriangle (false, i) := by
  rw [net.placedTriangle_hull]
  apply subset_convexHull ℝ _
  simp [net.patch_pole]

theorem petal_apex_mem (i : Fin 4) : (net.patch i).apex ∈ net.placedTriangle (true, i) := by
  rw [net.placedTriangle_hull]
  exact subset_convexHull ℝ _ (by simp)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
