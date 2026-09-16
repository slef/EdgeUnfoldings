import SixVertexUnfolding.OctahedronNine
import SixVertexUnfolding.Geometry.OctahedralRemotePairs

/-! The remaining octahedron geometry is confined to the local pairs, opposite petals, and finite cuts. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The two closed remote petals miss the corresponding closed finite slit segments. -/
structure FiniteCutsClear : Prop where
  last : Disjoint (net.placedTriangle (true, 1)) (segment ℝ 0 (graph.openingPoint (opposite source) slit 4))
  first : Disjoint (net.placedTriangle (true, 2)) (segment ℝ 0 (graph.openingPoint (opposite source) slit 0))

/-- The local slit lemma supplies these three nonoverlap conclusions. -/
structure LocalPairs : Prop where
  petals : net.Separated (true, 0) (true, 3)
  left : net.Separated (true, 0) (false, 3)
  right : net.Separated (true, 3) (false, 0)

/-- The two opposite-petal comparisons, for this same development. -/
structure OppositePetals : Prop where
  even : net.Separated (true, 0) (true, 2)
  odd : net.Separated (true, 1) (true, 3)

/-- The boundary argument discharges all four remote pairs from these three geometric inputs. -/
theorem remainingNine_of_core (local_pairs : net.LocalPairs) (opposite_pairs : net.OppositePetals)
    (cuts : net.FiniteCutsClear) : net.RemainingNine where
  slit_petals := local_pairs.petals
  slit_left := local_pairs.left
  slit_right := local_pairs.right
  opposite_even := opposite_pairs.even
  opposite_odd := opposite_pairs.odd
  remote := by
    intro i
    fin_cases i
    · exact net.remote_zero local_pairs.left opposite_pairs.even
    · exact net.remote_one cuts.last opposite_pairs.odd
    · exact net.remote_two cuts.first opposite_pairs.even
    · exact net.remote_three local_pairs.right opposite_pairs.odd

/-- Finishing the three remaining geometric lemmas yields the unchanged original-edge unfolding predicate. -/
theorem hasEdgeUnfolding_of_core (octahedral : graph.kind = .octahedron)
    (local_pairs : net.LocalPairs) (opposite_pairs : net.OppositePetals) (cuts : net.FiniteCutsClear) :
    P.HasEdgeUnfolding :=
  net.hasEdgeUnfolding_of_nine_comparisons octahedral (net.remainingNine_of_core local_pairs opposite_pairs cuts)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
