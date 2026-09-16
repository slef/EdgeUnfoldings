import SixVertexUnfolding.Geometry.FacetCornerNeighbors
import Mathlib.Geometry.Euclidean.Triangle

/-! Ordinary interior angles of original faces. The definition uses the
two original edges at a corner; it is zero away from that face. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

open Set EuclideanGeometry

variable {P : ConvexPolyhedron} (F : P.Face)

/-- The two original edges bounding a face at one of its vertices. -/
structure CornerNeighbors (v : P.Vertex) where
  left : P.Vertex
  right : P.Vertex
  distinct : left ≠ right
  at_vertex : (v : Space) ∈ F.val
  left_mem : (left : Space) ∈ F.val
  right_mem : (right : Space) ∈ F.val
  left_edge : P.edgeGraph.Adj v left
  right_edge : P.edgeGraph.Adj v right
  exhaust : ∀ w : P.Vertex, (w : Space) ∈ F.val → P.edgeGraph.Adj v w →
    w = left ∨ w = right

/-- Every corner of a triangular or quadrilateral face has such a pair. -/
theorem cornerNeighbors_nonempty
    (small : (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (v : P.Vertex) (on_face : (v : Space) ∈ F.val) : Nonempty (F.CornerNeighbors v) := by
  obtain ⟨b, edge, bF⟩ := F.exists_corner_edge small v on_face
  obtain ⟨c, different, edge_c, cF, exhaust⟩ :=
    F.exists_other_corner_neighbor small v b edge on_face bF
  exact ⟨⟨b, c, different.symm, on_face, bF, cF, edge, edge_c, exhaust⟩⟩

/-- The ordinary face angle; absent corners contribute zero to sums. -/
noncomputable def cornerAngle (v : P.Vertex) : ℝ := by
  classical
  exact if h : Nonempty (F.CornerNeighbors v) then
    angle ((Classical.choice h).left : Space) v (Classical.choice h).right else 0

theorem cornerAngle_of_not_mem (v : P.Vertex) (outside : (v : Space) ∉ F.val) :
    F.cornerAngle v = 0 := by
  classical
  have empty : ¬ Nonempty (F.CornerNeighbors v) := fun ⟨pair⟩ => outside pair.at_vertex
  simp only [cornerAngle, dif_neg empty]

/-- Computing the face angle is independent of the chosen ordering of its two edges. -/
theorem cornerAngle_eq
    (small : (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (v b c : P.Vertex) (distinct : b ≠ c)
    (vF : (v : Space) ∈ F.val) (bF : (b : Space) ∈ F.val) (cF : (c : Space) ∈ F.val)
    (vb : P.edgeGraph.Adj v b) (vc : P.edgeGraph.Adj v c) :
    F.cornerAngle v = angle (b : Space) v c := by
  classical
  have exists_pair := F.cornerNeighbors_nonempty small v vF
  rw [cornerAngle, dif_pos exists_pair]
  let pair := Classical.choice exists_pair
  change angle (pair.left : Space) v pair.right = angle (b : Space) v c
  rcases pair.exhaust b bF vb with rfl | rfl <;>
    rcases pair.exhaust c cF vc with rfl | rfl
  · exact (distinct rfl).elim
  · rfl
  · exact angle_comm _ _ _
  · exact (distinct rfl).elim

end SixVertexUnfolding.ConvexPolyhedron.Face
