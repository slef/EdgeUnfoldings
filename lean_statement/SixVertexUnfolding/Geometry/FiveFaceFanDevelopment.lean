import SixVertexUnfolding.Geometry.FiveFaceFanTriangles
import SixVertexUnfolding.Geometry.PrescribedTrianglePlacement

/-! Rigid placements of the actual five faces at their prescribed polar coordinates. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan

open Set

variable {P : ConvexPolyhedron} {pole : P.Vertex} (fan : P.FiveFaceFan pole)

theorem exists_opening_facet_placement (slit i : Fin 5) :
    ∃ place : Space →ᵃ[ℝ] Plane,
      place pole = 0 ∧
      place (fan.neighbor (slit + i)) = fan.openingPoint slit i.castSucc ∧
      place (fan.neighbor ((slit + i) + 1)) = fan.openingPoint slit i.succ ∧
      ∀ x ∈ (fan.face (slit + i)).val, ∀ y ∈ (fan.face (slit + i)).val,
        dist (place x) (place y) = dist x y := by
  apply (fan.face (slit + i)).exists_placement_at_triangle pole
    (fan.neighbor (slit + i)) (fan.neighbor ((slit + i) + 1))
  · exact (fan.not_pole _).symm
  · exact (fan.not_pole _).symm
  · exact fan.distinct.ne ((by decide : ∀ j : Fin 5, j ≠ j + 1) (slit + i))
  · exact fan.pole_mem_face _
  · exact fan.left_mem_face _
  · exact fan.right_mem_face _
  · rw [fan.openingPoint_radius, fan.openingVertex_start]
  · rw [fan.openingPoint_radius, fan.openingVertex_end]
  · exact fan.openingPoint_base slit i

/-- Five face placements with a common vertex and six successive ray copies. -/
structure Development (slit : Fin 5) where
  place : Fin 5 → Space →ᵃ[ℝ] Plane
  at_pole : ∀ i, place i pole = 0
  at_left : ∀ i, place i (fan.neighbor (slit + i)) = fan.openingPoint slit i.castSucc
  at_right : ∀ i, place i (fan.neighbor ((slit + i) + 1)) = fan.openingPoint slit i.succ
  rigid : ∀ i, ∀ x ∈ (fan.face (slit + i)).val,
    ∀ y ∈ (fan.face (slit + i)).val, dist (place i x) (place i y) = dist x y

theorem exists_development (slit : Fin 5) : Nonempty (fan.Development slit) := by
  classical
  choose place at_pole at_left at_right rigid using fan.exists_opening_facet_placement slit
  exact ⟨⟨place, at_pole, at_left, at_right, rigid⟩⟩

namespace Development

variable {fan} {slit : Fin 5} (net : fan.Development slit)

theorem placed_triangle (i : Fin 5) :
    net.place i '' fan.triangle (slit + i) = fan.openingTriangle slit i := by
  rw [triangle, (net.place i).image_convexHull,
    image_insert_eq, image_insert_eq, image_singleton, net.at_pole, net.at_left, net.at_right]
  rfl

end Development
end SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan
