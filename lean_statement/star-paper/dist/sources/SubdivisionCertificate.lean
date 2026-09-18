import SixVertexUnfolding.Geometry.SubdivisionHinges
import SixVertexUnfolding.Geometry.ContractedHinges
import SixVertexUnfolding.Geometry.OctahedralAllPairs
import SixVertexUnfolding.Geometry.OctahedralReassembly

/-! A consistent selected subdivision gives a certificate on rigid, whole original facets. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles OctahedralNet

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- After whole-facet consistency is checked, no rigidity, hinge, tree, or nonoverlap obligation remains. -/
theorem hasEdgeUnfolding_of_consistent_subdivision
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (consistent : ∀ x y : FaceIndex, graph.netFace small_faces source slit x = graph.netFace small_faces source slit y →
      Set.EqOn (net.place x) (net.place y) (graph.netFace small_faces source slit y).val) : P.HasEdgeUnfolding := by
  classical
  let face := graph.netFace small_faces source slit
  have onto := graph.netFace_surjective_all small_faces source slit
  choose representative at_face using onto
  let placement (F : P.Face) := net.place (representative F)
  have agree (i : FaceIndex) : Set.EqOn (placement (face i)) (net.place i) (face i).val :=
    consistent (representative (face i)) i (at_face (face i))
  have rigid (F : P.Face) : ∀ x ∈ F.val, ∀ y ∈ F.val,
      dist (placement F x) (placement F y) = dist x y := by
    have proof := net.rigid_netFace (representative F)
    rw [at_face F] at proof
    exact proof
  have connected := contractedHinges_connected OctahedralNet.hinges face OctahedralNet.connected
    (graph.netFace_surjective_all small_faces source slit)
  obtain ⟨hinges, retained, tree⟩ := connected.exists_isTree_le
  apply graph.hasEdgeUnfolding_of_subdivision small_faces placement hinges tree
  · intro F G edge
    obtain ⟨different, x, y, original, rfl, rfl⟩ := retained edge
    exact (net.original_subdivision_hinge x y original different).1
  · exact rigid
  · intro F G edge p member
    obtain ⟨different, x, y, original, rfl, rfl⟩ := retained edge
    exact (agree x member.1).trans
      (((net.original_subdivision_hinge x y original different).2 member).trans (agree y member.2).symm)
  · have placed (i : FaceIndex) : placement (face i) '' graph.triangle (OctahedralNet.triangle source slit i) =
        net.placedTriangle i :=
      ((agree i).mono (graph.triangle_subset_face small_faces _)).image_eq
    intro t u different
    obtain ⟨i, rfl⟩ := (triangle_bijective source slit).2 t
    obtain ⟨j, rfl⟩ := (triangle_bijective source slit).2 u
    change Disjoint (interior (placement (face i) '' graph.triangle (OctahedralNet.triangle source slit i)))
      (interior (placement (face j) '' graph.triangle (OctahedralNet.triangle source slit j)))
    rw [placed, placed]
    exact net.selected_triangles_nonoverlap source_order maximal i j (fun same => different (same ▸ rfl))

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
