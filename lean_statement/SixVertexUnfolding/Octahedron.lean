import SixVertexUnfolding.Geometry.OctahedralNetPlacement

/-! The original-edge octahedron certificate, with its remaining geometric comparisons explicit. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}

/-- Proving the remaining eighteen triangle comparisons completes the public original-edge certificate.
Every other obligation, including original facets and the retained hinge tree, is already discharged. -/
theorem hasEdgeUnfolding_of_remaining_pairs (net : graph.Development small_faces source slit)
    (octahedral : graph.kind = .octahedron)
    (mixed : ∀ i j : Fin 4, i ≠ j →
      Disjoint (interior (net.fan.place i '' graph.triangle (fanTriangle (opposite source) (slit + i))))
        (interior (net.petal j '' graph.triangle (fanTriangle source (slit + j)))))
    (petals : ∀ i j : Fin 4, i ≠ j →
      Disjoint (interior (net.petal i '' graph.triangle (fanTriangle source (slit + i))))
        (interior (net.petal j '' graph.triangle (fanTriangle source (slit + j))))) : P.HasEdgeUnfolding := by
  let index := graph.netFaceEquiv small_faces octahedral source slit
  let place (F : P.Face) := net.place (index.symm F)
  let hinges := OctahedralNet.hinges.comap index.symm
  have tree : hinges.IsTree :=
    (SimpleGraph.Iso.comap index.symm OctahedralNet.hinges).isTree_iff.mpr OctahedralNet.isTree
  have placed (i : OctahedralNet.FaceIndex) : place (index i) = net.place i := by
    simp only [place, index.symm_apply_apply]
  have face_at (i : OctahedralNet.FaceIndex) : index i = graph.netFace small_faces source slit i := rfl
  have hinge_at (i j : OctahedralNet.FaceIndex) : hinges.Adj (index i) (index j) ↔ OctahedralNet.hinges.Adj i j := by
    change OctahedralNet.hinges.Adj (index.symm (index i)) (index.symm (index j)) ↔ _
    rw [index.symm_apply_apply, index.symm_apply_apply]
  refine ⟨{
    place := fun F => place F
    hinges := hinges
    tree := tree
    original_edges := ?_
    rigid := ?_
    joined := ?_
    nonoverlap := ?_
  }⟩
  · intro F G adjacent
    obtain ⟨i, rfl⟩ := index.surjective F
    obtain ⟨j, rfl⟩ := index.surjective G
    exact graph.net_hinge_original small_faces octahedral source slit i j ((hinge_at i j).mp adjacent)
  · intro F
    obtain ⟨i, rfl⟩ := index.surjective F
    rw [placed]
    simpa only [face_at] using net.rigid_netFace i
  · intro F G adjacent
    obtain ⟨i, rfl⟩ := index.surjective F
    obtain ⟨j, rfl⟩ := index.surjective G
    have joined := net.joined_netFace octahedral i j ((hinge_at i j).mp adjacent)
    rw [placed, placed]
    simpa only [face_at] using joined
  · intro F G different
    obtain ⟨i, rfl⟩ := index.surjective F
    obtain ⟨j, rfl⟩ := index.surjective G
    have safe := net.nonoverlap_of_remaining_pairs octahedral mixed petals i j
      (fun same => different (congrArg index same))
    rw [placed, placed]
    simpa only [face_at] using safe

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
