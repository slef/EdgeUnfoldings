import SixVertexUnfolding.Geometry.GlobalCutTreeKites

/-! Name either of the two actual triangles without duplicating its
surface map. The Boolean records a side, not a new geometric choice. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutEdgeTriangles

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : CutEdgeTriangles T edge)

def routes : Bool → C(unitInterval, P.BoundaryCurve)
  | false => D.first
  | true => D.second

def apex : Bool → Plane
  | false => D.model.first
  | true => D.model.second

def triangle (side : Bool) : RadialStripTriangle (D.routes side) (D.apex side) D.model.left D.model.right :=
  match side with
  | false => D.first_triangle
  | true => D.second_triangle

theorem routes_member (side : Bool) (s : unitInterval) :
    D.routes side s ∈ P.geodesicFiber a (T.closedEdgeTarget edge s) := by
  cases side
  · exact (D.member s).1
  · exact (D.member s).2

end CutEdgeTriangles

namespace PlacedCutEdgeTriangles

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : PlacedCutEdgeTriangles T edge)

/-- The actual radial development of the chosen side, in its chosen frame. -/
noncomputable def sideTriangle (side : Bool) :
    RadialStripTriangle (D.routes side) (D.motion (D.apex side))
      (D.motion D.model.left) (D.motion D.model.right) := (D.triangle side).move D.motion

/-- All placements of a surface point carried by this labelled pair of triangles. -/
def Places (b : frontier P.body) (x : Plane) : Prop :=
  ∃ side : Bool, ∃ inside : b ∈ range (closedRouteStripMap (D.routes side)),
    ((D.sideTriangle side).homeomorph ⟨b, inside⟩ : Plane) = x

/-- Retain the terminal edge parameter when a placement is on one particular ray. -/
def PlacesOnRay (s : unitInterval) (b : frontier P.body) (x : Plane) : Prop :=
  ∃ side : Bool, ∃ t : unitInterval, D.routes side s t = b ∧
    triangleFanMap (D.motion (D.apex side)) (D.motion D.model.left)
      (D.motion D.model.right) (s, t) = x

theorem places_iff_ray (b : frontier P.body) (x : Plane) :
    D.Places b x ↔ ∃ s, D.PlacesOnRay s b x := by
  constructor
  · rintro ⟨side, ⟨⟨s, t⟩, at_point⟩, placed⟩
    refine ⟨s, side, t, at_point, ?_⟩
    subst b
    rw [(D.sideTriangle side).radial] at placed
    exact placed
  · rintro ⟨s, side, t, at_point, placed⟩
    refine ⟨side, ⟨(s, t), at_point⟩, ?_⟩
    subst b
    exact ((D.sideTriangle side).radial (s, t)).trans placed

theorem places_mem_kite {b : frontier P.body} {x : Plane} (placed : D.Places b x) : x ∈ D.kite := by
  obtain ⟨side, inside, rfl⟩ := placed
  cases side
  · exact Or.inl ((D.sideTriangle false).homeomorph ⟨b, inside⟩).property
  · exact Or.inr ((D.sideTriangle true).homeomorph ⟨b, inside⟩).property

theorem exists_placement_iff (b : frontier P.body) : (∃ x, D.Places b x) ↔ b ∈ D.region := by
  constructor
  · rintro ⟨x, side, inside, _⟩
    cases side
    · exact Or.inl inside
    · exact Or.inr inside
  · rintro (inside | inside)
    · exact ⟨_, false, inside, rfl⟩
    · exact ⟨_, true, inside, rfl⟩

end PlacedCutEdgeTriangles
end SixVertexUnfolding.ConvexPolyhedron
