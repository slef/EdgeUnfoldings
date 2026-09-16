import SixVertexUnfolding.Geometry.VertexFanTriangles
import SixVertexUnfolding.Geometry.PrescribedTrianglePlacement

/-! Rigid placements of the actual corner triangles at their prescribed polar coordinates. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open Set

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n)

theorem exists_opening_facet_placement (slit i : Fin n) :
    ∃ place : Space →ᵃ[ℝ] Plane,
      place pole = 0 ∧
      place (fan.neighbor (slit + i)) = fan.openingPoint slit i.castSucc ∧
      place (fan.neighbor ((slit + i) + 1)) = fan.openingPoint slit i.succ ∧
      ∀ x ∈ (fan.face (slit + i)).val, ∀ y ∈ (fan.face (slit + i)).val,
        dist (place x) (place y) = dist x y := by
  apply (fan.face (slit + i)).exists_placement_at_triangle pole
    (fan.neighbor (slit + i)) (fan.neighbor ((slit + i) + 1))
  · exact (fan.adjacent _).ne
  · exact (fan.adjacent _).ne
  · exact fan.successive_distinct _
  · exact fan.pole_mem _
  · exact fan.left_mem _
  · exact fan.right_mem _
  · rw [fan.openingPoint_radius, fan.openingVertex_start]
  · rw [fan.openingPoint_radius, fan.openingVertex_end]
  · exact fan.openingPoint_base slit i

/-- Face placements with a common vertex and successive ray copies. -/
structure Development (slit : Fin n) where
  place : Fin n → Space →ᵃ[ℝ] Plane
  at_pole : ∀ i, place i pole = 0
  at_left : ∀ i, place i (fan.neighbor (slit + i)) = fan.openingPoint slit i.castSucc
  at_right : ∀ i, place i (fan.neighbor ((slit + i) + 1)) = fan.openingPoint slit i.succ
  rigid : ∀ i, ∀ x ∈ (fan.face (slit + i)).val,
    ∀ y ∈ (fan.face (slit + i)).val, dist (place i x) (place i y) = dist x y

theorem exists_development (slit : Fin n) : Nonempty (fan.Development slit) := by
  classical
  choose place at_pole at_left at_right rigid using fan.exists_opening_facet_placement slit
  exact ⟨⟨place, at_pole, at_left, at_right, rigid⟩⟩

namespace Development

variable {fan} {slit : Fin n} (net : fan.Development slit)

theorem placed_triangle (i : Fin n) :
    net.place i '' fan.triangle (slit + i) = fan.openingTriangle slit i := by
  rw [triangle, (net.place i).image_convexHull,
    image_insert_eq, image_insert_eq, image_singleton, net.at_pole, net.at_left, net.at_right]
  rfl

end Development
end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
