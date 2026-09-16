import SixVertexUnfolding.Geometry.ClosedCutSet

/-! The same cut set viewed in ambient three-space, for intersections
with genuine original-face segments. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- The previously defined cut set, with the boundary subtype forgotten. -/
def cutSetInSpace (P : ConvexPolyhedron) (a : frontier P.body) : Set Space :=
  Subtype.val '' P.cutSet a

theorem mem_cutSetInSpace (P : ConvexPolyhedron) (a b : frontier P.body) :
    (b : Space) ∈ P.cutSetInSpace a ↔ b ∈ P.cutSet a := by
  constructor
  · rintro ⟨c, hc, same⟩
    exact (Subtype.ext same : c = b) ▸ hc
  · exact fun member => ⟨b, member, rfl⟩

theorem cutSetInSpace_subset_boundary (P : ConvexPolyhedron) (a : frontier P.body) :
    P.cutSetInSpace a ⊆ frontier P.body := by
  rintro _ ⟨b, _, rfl⟩
  exact b.property

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem cutSetInSpace_compact (a : frontier P.body) : IsCompact (P.cutSetInSpace a) :=
  (graph.cutSet_compact small_faces a).image continuous_subtype_val

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
