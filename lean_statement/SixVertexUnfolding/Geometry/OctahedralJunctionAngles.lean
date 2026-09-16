import SixVertexUnfolding.Geometry.OctahedralJunctionChain

/-! The developed junction chain has exactly the original vertex's angle sum. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles EuclideanGeometry

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem junction_angle_sum (i : Fin 3) :
    (∑ k : Fin 4, (net.junctionChain i).corner k) =
      graph.totalAngleAt (fanNeighbor source ((slit + i.castSucc) + 1)) := by
  rw [Fin.sum_univ_four]
  change angle (net.patch i.castSucc).apex (net.patch i.castSucc).right (net.patch i.castSucc).left +
    angle (net.patch i.castSucc).left (net.patch i.castSucc).right (net.patch i.castSucc).pole +
    angle (net.patch i.castSucc).pole (net.patch i.castSucc).right (net.patch i.succ).right +
    angle (net.patch i.succ).right (net.patch i.castSucc).right (net.patch i.succ).apex = _
  rw [(net.patch i.castSucc).petal_angle_at_right, (net.patch i.castSucc).fan_angle_at_right,
    net.consecutive_patch_corner, net.patch_pole, ← net.patch_pole i.succ,
    (net.patch i.succ).fan_angle_at_left, (net.patch i.succ).petal_angle_at_left]
  have next : slit + i.succ = (slit + i.castSucc) + 1 := by
    rw [add_assoc, show (i.castSucc : Fin 4) + 1 = i.succ by fin_cases i <;> decide]
  rw [next]
  simp only [add_assoc, show (1 : Fin 4) + 1 = 2 from rfl]
  rw [graph.totalAngleAt_eq_fan_angles]
  simpa only [add_assoc] using junction_angle_incidence
    (fun a b c => angle (graph.vertex a : Space) (graph.vertex b : Space) (graph.vertex c : Space))
    (fun a b c => angle_comm _ _ _) source (slit + i.castSucc)

/-- All six pairs among the four triangles around this actual uncut equator vertex are safe. -/
theorem junction_nonoverlap (i : Fin 3) (j k : Fin 4) (different : j ≠ k) :
    Disjoint (interior ((net.junctionChain i).triangle j))
      (interior ((net.junctionChain i).triangle k)) := by
  apply (net.junctionChain i).nonoverlap _ j k different
  rw [net.junction_angle_sum]
  exact graph.totalAngleAt_lt_two_pi small_faces _

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
