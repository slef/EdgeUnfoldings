import SixVertexUnfolding.Geometry.OctahedralFanCoordinates
import SixVertexUnfolding.Geometry.RadialHinges

/-! The prescribed opened fan has the required outward orientation at all three internal hinges. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

theorem opening_radius_pos (pole : Fin 6) (slit : Fin 4) (j : Fin 5) :
    0 < dist (graph.vertex pole : Space) (graph.vertex (openingVertex pole slit j)) := by
  apply dist_pos.mpr
  intro same
  have distinct : ∀ pole slit j, openingVertex pole slit j ≠ pole := by decide
  exact distinct pole slit j (graph.vertex.injective (Subtype.ext same)).symm

theorem opening_hinge_outward (pole : Fin 6) (slit : Fin 4) (i : Fin 3) :
    OppositeHingeSides 0 (graph.openingPoint pole slit i.succ.castSucc)
      (graph.openingPoint pole slit i.castSucc.castSucc) (graph.openingPoint pole slit i.succ.succ) := by
  apply radial_hinge_opposite _ _ _ _ _ _ (graph.opening_radius_pos _ _ _)
    (graph.opening_radius_pos _ _ _) (graph.opening_radius_pos _ _ _)
  · rw [show i.succ.castSucc = i.castSucc.succ from rfl, graph.openingAngle_step]
    exact graph.fanAngle_pos _ _
  · rw [show i.succ.castSucc = i.castSucc.succ from rfl, graph.openingAngle_step]
    exact graph.fanAngle_lt_pi _ _
  · rw [graph.openingAngle_step]; exact graph.fanAngle_pos _ _
  · rw [graph.openingAngle_step]; exact graph.fanAngle_lt_pi _ _

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
