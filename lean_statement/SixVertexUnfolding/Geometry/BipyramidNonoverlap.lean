import SixVertexUnfolding.Geometry.BipyramidPetals
import SixVertexUnfolding.Geometry.BipyramidPlacedFaces
import SixVertexUnfolding.Geometry.BoundaryBarrier

/-! Every face pair in the bipyramid development has disjoint planar interiors. -/

namespace SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices.Development

variable {P : ConvexPolyhedron} {B : P.BipyramidVertices}
    {triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3}
    {source : Fin 3} (net : B.Development triangles source)

/-- Opposite petals are separated, in either ordering of the two caps. -/
theorem opposite_petals_disjoint (size : P.vertices.card = 5) (upper : Bool) (i j : Fin 3)
    (first_petal : i ≠ source) (second_petal : j ≠ source) :
    Disjoint (interior (net.faceImage upper i)) (interior (net.faceImage (!upper) j)) := by
  cases upper
  · exact (net.cross_petals_disjoint size j i second_petal first_petal).symm
  · exact net.cross_petals_disjoint size i j first_petal second_petal

/-- A petal cannot enter the opposite base through its three occupied boundary edges. -/
theorem base_petal_disjoint (size : P.vertices.card = 5) (upper : Bool) (missing : Fin 3)
    (petal : missing ≠ source) :
    Disjoint (interior (net.faceImage upper source))
      (interior (net.faceImage (!upper) missing)) := by
  obtain ⟨i, j, different, pair⟩ := equator_complement_pair source
  have isource : i ≠ source := (Set.ext_iff.mp pair i).mpr (Or.inl rfl)
  have jsource : j ≠ source := (Set.ext_iff.mp pair j).mpr (Or.inr rfl)
  let neighbors : Fin 3 → Set Plane :=
    ![net.faceImage upper i, net.faceImage upper j, net.faceImage (!upper) source]
  apply disjoint_interiors_of_boundary_cover (net.faceImage upper source)
    (net.faceImage (!upper) missing) neighbors (net.faceImage_closed upper source)
    (net.faceImage_convex (!upper) missing) (net.faceImage_interior_nonempty (!upper) missing)
  · intro inclusion
    exact net.opposite_pole_outside_base upper (inclusion (net.pole_mem_faceImage (!upper) missing))
  · intro k
    fin_cases k
    · exact net.faceImage_regular upper i
    · exact net.faceImage_regular upper j
    · exact net.faceImage_regular (!upper) source
  · intro x boundary
    rcases net.base_boundary_covered upper i j isource jsource different boundary with hi | hj | hb
    · exact Set.mem_iUnion.mpr ⟨0, hi⟩
    · exact Set.mem_iUnion.mpr ⟨1, hj⟩
    · exact Set.mem_iUnion.mpr ⟨2, hb⟩
  · intro k
    fin_cases k
    · exact (net.opposite_petals_disjoint size upper i missing isource petal).symm
    · exact (net.opposite_petals_disjoint size upper j missing jsource petal).symm
    · exact (net.cap (!upper)).nonoverlap missing source petal

/-- All nine pairs with one face from each cap are separated. -/
theorem all_cross_pairs_disjoint (size : P.vertices.card = 5) (i j : Fin 3) :
    Disjoint (interior (net.faceImage true i)) (interior (net.faceImage false j)) := by
  by_cases first_base : i = source
  · subst i
    by_cases second_base : j = source
    · subst j
      exact net.bases_safe
    · exact net.base_petal_disjoint size true j second_base
  · by_cases second_base : j = source
    · subst j
      exact (net.base_petal_disjoint size false i first_base).symm
    · exact net.cross_petals_disjoint size i j first_base second_base

include net in
/-- The constructed development is an original-edge unfolding of the whole bipyramid. -/
theorem hasEdgeUnfolding (size : P.vertices.card = 5) : P.HasEdgeUnfolding := by
  apply net.hasEdgeUnfolding_of_cross_pairs
  intro i j _
  exact net.all_cross_pairs_disjoint size i j

end SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices.Development
