import SixVertexUnfolding.Geometry.OctahedralObtuseContact
import SixVertexUnfolding.Geometry.OctahedralJunctionBoundary
import SixVertexUnfolding.Geometry.OctahedralPlacedTopology

/-! In the actual development, the first contact obstruction needs only its stated containment. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles Real

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem petal_apex_ne_right (i : Fin 4) : (net.patch i).apex ≠ (net.patch i).right := by
  intro same
  apply (net.patch i).petal_noncollinear
  simpa [same] using collinear_pair ℝ (net.patch i).left (net.patch i).right

theorem petal_apex_ne_pole (i : Fin 4) : (net.patch i).apex ≠ (net.patch i).pole := by
  have original_ne : (graph.vertex (opposite source) : Space) ≠ (graph.vertex source : Space) :=
    fun same => opposite_ne source (graph.vertex.injective (Subtype.ext same))
  have positive := lt_of_lt_of_le (dist_pos.mpr original_ne) (net.patch i).pole_distance_ge
  intro same
  rw [same, dist_self] at positive
  linarith

theorem neighboring_apex_copies_distinct (i : Fin 3) : (net.patch i.castSucc).apex ≠ (net.patch i.succ).apex := by
  intro same
  have center := net.neighboring_petals_meet_only_at_vertex i (net.patch i.castSucc).apex
    (net.petal_apex_mem i.castSucc) (by rw [same]; exact net.petal_apex_mem i.succ)
  exact net.petal_apex_ne_right i.castSucc center

theorem neighboring_apex_radii_equal (i : Fin 3) :
    dist (net.patch i.succ).apex (net.patch i.castSucc).right =
      dist (net.patch i.castSucc).apex (net.patch i.castSucc).right := by
  rw [(net.patch i.castSucc).petal_right, net.consecutive_patch_corner, (net.patch i.succ).petal_left]
  have next : (i.castSucc : Fin 4) + 1 = i.succ := by fin_cases i <;> decide
  rw [add_assoc, next]

/-- The equal radii, distinct copied apexes, and nondegeneracy are all derived from this net.
The sole substantive contact premise is containment in the closed contact triangle. -/
theorem source_curvature_lt_pi_of_junction_containment (i : Fin 3) (t : ℝ)
    (lower : 0 ≤ t) (upper : t ≤ 1)
    (contained : (net.patch i.castSucc).apex ∈ convexHull ℝ
      ({(net.patch i.castSucc).right, (net.patch i.castSucc).pole,
        (net.patch i.castSucc).right + t • ((net.patch i.succ).apex - (net.patch i.castSucc).right)} : Set Plane)) :
    graph.curvature source < π :=
  (net.patch i.castSucc).source_curvature_lt_pi_of_contact_containment (small_faces := small_faces)
    (net.patch i.succ).apex (net.petal_apex_ne_right i.castSucc) (net.neighboring_apex_radii_equal i)
    (net.neighboring_apex_copies_distinct i) t lower upper contained (net.petal_apex_ne_pole i.castSucc)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
