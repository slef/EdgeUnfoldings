import SixVertexUnfolding.Geometry.TerminalSourceImage

/-! Bounded face sequences give finiteness of the actual normalized shortest
routes, not merely finiteness of possible distance values. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- There are finitely many constant-speed shortest routes whose interiors avoid vertices. -/
theorem finite_vertex_free_shortest_routes (P : ConvexPolyhedron) (a b : Space) :
    {path : P.SurfacePath a b | path.IsShortest ∧ path.length ≠ ⊤ ∧
      LipschitzWith path.length.toNNReal path.curve ∧
      ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices}.Finite := by
  classical
  let routes := {path : P.SurfacePath a b | path.IsShortest ∧ path.length ≠ ⊤ ∧
    LipschitzWith path.length.toNNReal path.curve ∧
    ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices}
  have coded (route : routes) := route.val.exists_terminal_source_code route.property.1 route.property.2.1
    route.property.2.2.1 route.property.2.2.2
  choose code start before formula using coded
  have injective : Function.Injective code := by
    intro first second equal
    apply Subtype.ext
    apply first.val.eq_of_curve_eq second.val
    apply first.val.agree_of_terminal_source_code second.val first.property.1 second.property.1
      first.property.2.1 second.property.2.1 first.property.2.2.1 second.property.2.2.1
      first.property.2.2.2 (code first) (start first) (start second) (before first) (before second) (formula first)
    have same_face := congrArg (fun c : P.FaceSequence => c.face c.last) equal.symm
    have same_source := congrArg (fun c : P.FaceSequence => c.sourceImage a) equal.symm
    simpa only [same_face, same_source] using formula second
  letI : Finite routes := Finite.of_injective code injective
  exact Set.toFinite routes

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- In every canonical six-vertex model, distinct endpoints admit only finitely many normalized shortest routes. -/
theorem finite_shortest_routes (a b : Space) (different : a ≠ b) :
    {path : P.SurfacePath a b | path.IsShortest ∧ path.length ≠ ⊤ ∧
      LipschitzWith path.length.toNNReal path.curve}.Finite := by
  apply (P.finite_vertex_free_shortest_routes a b).subset
  intro path hp
  exact ⟨hp.1, hp.2.1, hp.2.2,
    graph.shortest_lipschitz_avoids_vertices small_faces path different hp.1 hp.2.1 hp.2.2⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
