import SixVertexUnfolding.Geometry.PlacedRayTargets

/-! Along the interior of a tree edge the two route branches are
distinct. Their only retained meeting is the common triangle base. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutEdgeTriangles

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : CutEdgeTriangles T edge)

theorem routes_interior_injective (s : unitInterval) (positive : 0 < s) (before : s < 1) :
    Function.Injective (fun side => D.routes side s) := by
  let t : Ioo (0 : ℝ) 1 := ⟨s, positive, before⟩
  have first : D.first s = D.strips.first t := (D.agrees t).1
  have second : D.second s = D.strips.second t := (D.agrees t).2
  have distinct : D.first s ≠ D.second s := by rw [first, second]; exact D.strips.distinct t
  intro side other same
  cases side <;> cases other
  · rfl
  · exact (distinct same).elim
  · exact (distinct same.symm).elim
  · rfl

end CutEdgeTriangles

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

/-- At an interior edge parameter, any two placements of the same nonsource point agree. -/
theorem interior_ray_placements_agree {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : PlacedCutEdgeTriangles T edge)
    {s : unitInterval} (positive : 0 < s) (before : s < 1)
    {b : frontier P.body} {x y : Plane} (not_source : b ≠ a)
    (first : D.PlacesOnRay s b x) (second : D.PlacesOnRay s b y) : x = y := by
  obtain ⟨side, time, first_point, first_position⟩ := first
  obtain ⟨other_side, other_time, second_point, second_position⟩ := second
  have first_member := D.routes_member side s
  have second_member := D.routes_member other_side s
  have different : a ≠ T.closedEdgeTarget edge s := by
    intro same
    have cut := T.closedEdgeTarget_cut edge s
    rw [← same] at cut
    exact P.source_not_cutSet a cut
  have first_injective := P.geodesicFiber_injective a _ different (D.routes side s) first_member
  have second_injective := P.geodesicFiber_injective a _ different (D.routes other_side s) second_member
  have meet := (graph.closed_cut_rays_intersection small_faces a _ _
    (T.closedEdgeTarget_cut edge s) (T.closedEdgeTarget_cut edge s) (D.routes side s) (D.routes other_side s)
    first_member second_member b).mp ⟨⟨time, first_point⟩, ⟨other_time, second_point⟩⟩
  rcases meet with source | ⟨_, at_target⟩ | ⟨same_route, _⟩
  · exact (not_source source).elim
  · have first_last : time = 1 := first_injective
      ((first_point.trans at_target).trans (congrArg Prod.snd first_member.2).symm)
    have second_last : other_time = 1 := second_injective
      ((second_point.trans at_target).trans (congrArg Prod.snd second_member.2).symm)
    rw [first_last] at first_position
    rw [second_last] at second_position
    change AffineMap.lineMap _ (AffineMap.lineMap (D.motion D.model.left) (D.motion D.model.right) (s : ℝ))
      (1 : ℝ) = x at first_position
    change AffineMap.lineMap _ (AffineMap.lineMap (D.motion D.model.left) (D.motion D.model.right) (s : ℝ))
      (1 : ℝ) = y at second_position
    rw [AffineMap.lineMap_apply_one] at first_position second_position
    exact first_position.symm.trans second_position
  · have same_side := D.routes_interior_injective s positive before same_route
    subst other_side
    have same_time := first_injective (first_point.trans second_point.symm)
    rw [same_time] at first_position
    exact first_position.symm.trans second_position

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
