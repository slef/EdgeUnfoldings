import SixVertexUnfolding.Geometry.UniversalVertexFigure
import SixVertexUnfolding.Geometry.NonvertexFacetNeighborhoods

/-! The constructed five-ray figure describes the entire actual
surface near the vertex, with the same ordinary spatial sector angles. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set InnerProductGeometry

/-- Transverse normalization preserves the actual angle between two incident edges. -/
theorem VertexFigure.direction_angle {P : ConvexPolyhedron} {source : P.Vertex}
    (figure : P.VertexFigure source) (u v : P.Vertex) (us : u ≠ source) (vs : v ≠ source) :
    angle (figure.direction u) (figure.direction v) =
      angle ((u : Space) - source) ((v : Space) - source) := by
  rw [VertexFigure.direction, VertexFigure.direction,
    angle_smul_left_of_pos _ _ (inv_pos.mpr (figure.gap_pos u.property (fun same => us (Subtype.ext same)))),
    angle_smul_right_of_pos _ _ (inv_pos.mpr (figure.gap_pos v.property (fun same => vs (Subtype.ext same))))]

/-- The five original triangles contain the whole surface in an open neighborhood of the vertex. -/
theorem universal_vertex_five_sector_neighborhood (P : ConvexPolyhedron) (size : P.vertices.card = 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v) :
    ∃ order : Fin 5 ≃ {v : P.Vertex // v ≠ source}, ∃ U : Set Space,
      IsOpen U ∧ (source : Space) ∈ U ∧
      U ∩ frontier P.body ⊆ ⋃ i : Fin 5,
        convexHull ℝ ({(source : Space), ((order i).val : Space), ((order (i + 1)).val : Space)} : Set Space) := by
  obtain ⟨order, faces, vertices⟩ := P.universal_vertex_face_order size small_faces source universal
  have covers := P.universal_vertex_fan_covers small_faces source universal order faces vertices
  obtain ⟨U, openU, sourceU, incident⟩ := P.incident_facets_neighborhood source
  refine ⟨order, U, openU, sourceU, ?_⟩
  rintro x ⟨near, surface⟩
  obtain ⟨F, member⟩ := P.boundary_point_in_face surface
  obtain ⟨i, rfl⟩ := (covers F).mp (incident x near F member)
  apply mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rwa [← vertices i, ← (faces i).eq_convexHull_vertices]

end SixVertexUnfolding.ConvexPolyhedron
