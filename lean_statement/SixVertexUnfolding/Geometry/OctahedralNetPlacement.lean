import SixVertexUnfolding.Geometry.OctahedralNetFaces

/-! The eight constructed maps satisfy the original-facet rigidity and hinge obligations. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles OctahedralNet

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The actual affine map at a fan or petal position of the constructed net. -/
def place (index : FaceIndex) : Space →ᵃ[ℝ] Plane := if index.1 then net.petal index.2 else net.fan.place index.2

/-- Every indexed map is rigid on its whole original carrier facet. -/
theorem rigid_netFace (index : FaceIndex) :
    ∀ x ∈ (graph.netFace small_faces source slit index).val,
      ∀ y ∈ (graph.netFace small_faces source slit index).val,
        dist (net.place index x) (net.place index y) = dist x y := by
  obtain ⟨petal, i⟩ := index
  cases petal
  · exact net.fan.rigid i
  · exact net.petal_rigid i

variable (octahedral : graph.kind = .octahedron)

include octahedral in
/-- The prescribed seven hinges agree on the entire intersections of their original facets. -/
theorem joined_netFace (x y : FaceIndex) (adjacent : hinges.Adj x y) :
    ∀ p ∈ (graph.netFace small_faces source slit x).val ∩ (graph.netFace small_faces source slit y).val,
      net.place x p = net.place y p := by
  have fan_joined (i : Fin 3) :
      ∀ p ∈ (graph.netFace small_faces source slit (false, i.castSucc)).val ∩
        (graph.netFace small_faces source slit (false, i.succ)).val,
          net.place (false, i.castSucc) p = net.place (false, i.succ) p := by
    rw [graph.netFace_intersection_pair small_faces octahedral source slit _ _ _ _ (fan_common_vertices source slit i)]
    exact net.fan.joined i
  have petal_joined (i : Fin 4) :
      ∀ p ∈ (graph.netFace small_faces source slit (false, i)).val ∩
        (graph.netFace small_faces source slit (true, i)).val,
          net.place (false, i) p = net.place (true, i) p := by
    rw [graph.netFace_intersection_pair small_faces octahedral source slit _ _ _ _ (petal_common_vertices source slit i)]
    exact net.petal_joined i
  rcases hinge_cases x y adjacent with ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩
  · exact fan_joined i
  · intro p hp
    exact (fan_joined i p ⟨hp.2, hp.1⟩).symm
  · exact petal_joined i
  · intro p hp
    exact (petal_joined i p ⟨hp.2, hp.1⟩).symm

include octahedral in
/-- Only the twelve nonattached mixed pairs and six petal pairs remain to prove nonoverlap. -/
theorem nonoverlap_of_remaining_pairs
    (mixed : ∀ i j : Fin 4, i ≠ j →
      Disjoint (interior (net.fan.place i '' graph.triangle (fanTriangle (opposite source) (slit + i))))
        (interior (net.petal j '' graph.triangle (fanTriangle source (slit + j)))))
    (petals : ∀ i j : Fin 4, i ≠ j →
      Disjoint (interior (net.petal i '' graph.triangle (fanTriangle source (slit + i))))
        (interior (net.petal j '' graph.triangle (fanTriangle source (slit + j))))) :
    ∀ x y : FaceIndex, x ≠ y →
      Disjoint (interior (net.place x '' (graph.netFace small_faces source slit x).val))
        (interior (net.place y '' (graph.netFace small_faces source slit y).val)) := by
  rintro ⟨left, i⟩ ⟨right, j⟩ different
  rw [graph.netFace_eq_triangle small_faces octahedral, graph.netFace_eq_triangle small_faces octahedral]
  cases left <;> cases right
  · exact net.fan.nonoverlap i j (fun same => different (Prod.ext rfl same))
  · by_cases same : i = j
    · subst j
      exact net.attached_pair_nonoverlap i
    · exact mixed i j same
  · by_cases same : j = i
    · subst j
      exact (net.attached_pair_nonoverlap i).symm
    · exact (mixed j i same).symm
  · exact petals i j (fun same => different (Prod.ext rfl same))

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
