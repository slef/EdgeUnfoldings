import SixVertexUnfolding.Geometry.OctahedralDevelopment
import SixVertexUnfolding.Geometry.OctahedralPatchCorners
import SixVertexUnfolding.Geometry.OctahedralFanHinges
import SixVertexUnfolding.Geometry.FourTriangleSeparation
import SixVertexUnfolding.OctahedralJunctionIncidence

/-! At each uncut equator vertex, the two adjacent patches form one four-triangle chain. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles EuclideanGeometry

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem consecutive_patch_corner (i : Fin 3) : (net.patch i.castSucc).right = (net.patch i.succ).left := by
  rw [net.patch_right, net.patch_left]
  rfl

theorem consecutive_patch_outward (i : Fin 3) :
    OppositeHingeSides (net.patch i.castSucc).right (net.patch i.castSucc).pole
      (net.patch i.castSucc).left (net.patch i.succ).right := by
  rw [net.patch_right, net.patch_pole, net.patch_left, net.patch_right]
  apply (oppositeHingeSides_swap 0 _ _ _ ?_).mpr
  · exact graph.opening_hinge_outward (opposite source) slit i
  · apply dist_pos.mp
    rw [graph.openingPoint_radius]
    exact graph.opening_radius_pos _ _ _

/-- The rays are: previous petal apex, previous equator vertex, fan pole,
next equator vertex, next petal apex. -/
noncomputable def junctionChain (i : Fin 3) : FourTriangleChain where
  center := (net.patch i.castSucc).right
  ray := ![(net.patch i.castSucc).apex, (net.patch i.castSucc).left,
    (net.patch i.castSucc).pole, (net.patch i.succ).right, (net.patch i.succ).apex]
  noncollinear := by
    intro k
    have corner := net.consecutive_patch_corner i
    have pole : (net.patch i.castSucc).pole = (net.patch i.succ).pole := by rw [net.patch_pole, net.patch_pole]
    fin_cases k
    · change ¬ Collinear ℝ ({(net.patch i.castSucc).right, (net.patch i.castSucc).apex, (net.patch i.castSucc).left} : Set Plane)
      have reorder : ({(net.patch i.castSucc).right, (net.patch i.castSucc).apex, (net.patch i.castSucc).left} : Set Plane) =
          {(net.patch i.castSucc).left, (net.patch i.castSucc).right, (net.patch i.castSucc).apex} := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [reorder]
      exact (net.patch i.castSucc).petal_noncollinear
    · change ¬ Collinear ℝ ({(net.patch i.castSucc).right, (net.patch i.castSucc).left, (net.patch i.castSucc).pole} : Set Plane)
      rw [Set.insert_comm]
      exact (net.patch i.castSucc).fan_noncollinear
    · change ¬ Collinear ℝ ({(net.patch i.castSucc).right, (net.patch i.castSucc).pole, (net.patch i.succ).right} : Set Plane)
      rw [corner, pole]
      have reorder : ({(net.patch i.succ).left, (net.patch i.succ).pole, (net.patch i.succ).right} : Set Plane) =
          {(net.patch i.succ).left, (net.patch i.succ).right, (net.patch i.succ).pole} := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [reorder]
      exact (net.patch i.succ).fan_noncollinear
    · change ¬ Collinear ℝ ({(net.patch i.castSucc).right, (net.patch i.succ).right, (net.patch i.succ).apex} : Set Plane)
      rw [corner]
      exact (net.patch i.succ).petal_noncollinear
  outward := by
    intro k
    fin_cases k
    · change OppositeHingeSides (net.patch i.castSucc).right (net.patch i.castSucc).left
        (net.patch i.castSucc).apex (net.patch i.castSucc).pole
      have distinct : (net.patch i.castSucc).left ≠ (net.patch i.castSucc).right := by
        intro same
        apply (net.patch i.castSucc).fan_noncollinear
        simpa [same] using collinear_pair ℝ (net.patch i.castSucc).right (net.patch i.castSucc).pole
      rw [oppositeHingeSides_swap _ _ _ _ distinct, OppositeHingeSides, real_inner_comm]
      exact (net.patch i.castSucc).outward
    · exact net.consecutive_patch_outward i
    · change OppositeHingeSides (net.patch i.castSucc).right (net.patch i.succ).right
        (net.patch i.castSucc).pole (net.patch i.succ).apex
      rw [net.consecutive_patch_corner, net.patch_pole, ← net.patch_pole i.succ]
      exact (net.patch i.succ).outward

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
