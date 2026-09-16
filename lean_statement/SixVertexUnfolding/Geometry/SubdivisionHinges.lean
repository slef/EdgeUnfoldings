import SixVertexUnfolding.Geometry.OctahedralNetPlacement
import SixVertexUnfolding.Geometry.CommonFacetHinge

/-! Subdivision hinges between distinct carrier facets are original edges with matching placements. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles OctahedralNet

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- Every whole facet occurs among the eight carrier facets, also when two triangles share a carrier. -/
theorem netFace_surjective_all (source : Fin 6) (slit : Fin 4) :
    Function.Surjective (graph.netFace small_faces source slit) := by
  intro F
  have present := (graph.exists_facet_iff small_faces _).mp ⟨F, rfl⟩
  have occurs : ∃ t, carrier graph.kind t = F.vertexLabels graph.vertex := by
    rcases facet_cases graph.kind _ present with ⟨t, carrier_eq, _⟩ | ⟨q, _, carrier_eq⟩
    · exact ⟨t, carrier_eq⟩
    · exact ⟨quadPieces q 0, carrier_eq 0⟩
  obtain ⟨t, labels⟩ := occurs
  obtain ⟨index, at_triangle⟩ := (triangle_bijective source slit).2 t
  refine ⟨index, Face.vertexLabels_injective graph.vertex ?_⟩
  change (graph.triangleFace small_faces (OctahedralNet.triangle source slit index)).vertexLabels graph.vertex = _
  rw [graph.triangleFace_labels, at_triangle, labels]

namespace Development

variable {graph small_faces} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The seven construction steps agree along their shared subdivision segments. -/
theorem joined_subdivision_hinge (x y : FaceIndex) (edge : hinges.Adj x y) :
    Set.EqOn (net.place x) (net.place y)
      (graph.labeledHull (OctahedralTriangles.vertices (OctahedralNet.triangle source slit x) ∩ OctahedralTriangles.vertices (OctahedralNet.triangle source slit y))) := by
  rcases hinge_cases x y edge with ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩
  · rw [fan_common_vertices, labeledHull]
    simp only [Finset.coe_pair, Set.image_insert_eq, Set.image_singleton, convexHull_pair]
    exact net.fan.joined i
  · rw [Finset.inter_comm, fan_common_vertices, labeledHull]
    simp only [Finset.coe_pair, Set.image_insert_eq, Set.image_singleton, convexHull_pair]
    intro p member
    exact (net.fan.joined i p member).symm
  · rw [petal_common_vertices, labeledHull]
    simp only [Finset.coe_pair, Set.image_insert_eq, Set.image_singleton, convexHull_pair]
    exact net.petal_joined i
  · rw [Finset.inter_comm, petal_common_vertices, labeledHull]
    simp only [Finset.coe_pair, Set.image_insert_eq, Set.image_singleton, convexHull_pair]
    intro p member
    exact (net.petal_joined i p member).symm

/-- A retained step between different original facets is their whole original edge. -/
theorem original_subdivision_hinge (x y : FaceIndex) (edge : hinges.Adj x y)
    (different : graph.netFace small_faces source slit x ≠ graph.netFace small_faces source slit y) :
    P.ShareEdge (graph.netFace small_faces source slit x) (graph.netFace small_faces source slit y) ∧
      Set.EqOn (net.place x) (net.place y)
        ((graph.netFace small_faces source slit x).val ∩ (graph.netFace small_faces source slit y).val) := by
  obtain ⟨a, b, distinct, common⟩ := Finset.card_eq_two.mp (hinge_common_card source slit x y edge)
  have member (v : Fin 6) (h : v ∈ ({a, b} : Finset (Fin 6))) :
      (graph.vertex v : Space) ∈ (graph.netFace small_faces source slit x).val ∧
      (graph.vertex v : Space) ∈ (graph.netFace small_faces source slit y).val := by
    rw [← common] at h
    have inside (index : FaceIndex) (hv : v ∈ OctahedralTriangles.vertices (OctahedralNet.triangle source slit index)) :
        (graph.vertex v : Space) ∈ (graph.netFace small_faces source slit index).val := by
      apply graph.triangle_subset_face small_faces
      exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩
    exact ⟨inside x (Finset.mem_inter.mp h).1, inside y (Finset.mem_inter.mp h).2⟩
  have at_a := member a (by simp)
  have at_b := member b (by simp)
  have intersection := Face.intersection_eq_segment_of_common_vertices _ _ different
    (graph.vertex a) (graph.vertex b) (graph.vertex.injective.ne distinct) at_a.1 at_b.1 at_a.2 at_b.2
  have joined := net.joined_subdivision_hinge x y edge
  rw [common, labeledHull] at joined
  simp only [Finset.coe_pair, Set.image_insert_eq, Set.image_singleton, convexHull_pair] at joined
  refine ⟨?_, by rwa [intersection]⟩
  change affineDimension (_ ∩ _) = 1
  rw [intersection, ← convexHull_pair, affineDimension_convexHull]
  exact affineDimension_pair (fun same => distinct (graph.vertex.injective (Subtype.ext same)))

end Development
end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
