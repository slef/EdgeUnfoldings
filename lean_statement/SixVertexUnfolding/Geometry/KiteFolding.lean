import SixVertexUnfolding.Geometry.PlacedKiteBase
import SixVertexUnfolding.Geometry.ClosedCoverMaps

/-! Fold the whole paired kite back to its actual surface region.
The inverse maps agree along the base; different source copies are
allowed to fold to the same original source. -/

namespace SixVertexUnfolding.ConvexPolyhedron.PlacedCutEdgeTriangles

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v}

structure Folding (D : PlacedCutEdgeTriangles T edge) where
  map : C(D.kite, frontier P.body)
  on_side : ∀ (side : Bool) (x : D.sideRegion side),
    map ⟨x, D.side_subset_kite side x.property⟩ = ((D.sideTriangle side).homeomorph.symm x).val
  rigid_pieces : HasFiniteRigidPieces D.kite (fun x => (map x : Space))

variable (D : PlacedCutEdgeTriangles T edge)

theorem kite_eq_sides : (⋃ side : Bool, D.sideRegion side) = D.kite := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨side, inside⟩
    exact D.side_subset_kite side inside
  · rintro (first | second)
    · exact ⟨false, first⟩
    · exact ⟨true, second⟩

/-- The entire kite has a continuous finite rigid folding, proved from its two triangles. -/
theorem exists_folding : Nonempty (D.Folding) := by
  classical
  let maps (side : Bool) : C(D.sideRegion side, frontier P.body) :=
    ⟨fun x => ((D.sideTriangle side).homeomorph.symm x).val,
      continuous_subtype_val.comp (D.sideTriangle side).homeomorph.symm.continuous⟩
  have closed (side : Bool) : IsClosed (D.sideRegion side) := by
    have finite : ({D.motion (D.apex side), D.motion D.model.left, D.motion D.model.right} : Set Plane).Finite := by simp
    exact (finite.isCompact_convexHull ℝ).isClosed
  obtain ⟨glued, agrees⟩ := glue_finite_closed_maps D.sideRegion closed maps
    (fun side other x first second => D.side_folds_agree side other x first second)
  let fold : C(D.kite, frontier P.body) :=
    ⟨fun x => glued ((Homeomorph.setCongr D.kite_eq_sides).symm x),
      glued.continuous.comp (Homeomorph.setCongr D.kite_eq_sides).symm.continuous⟩
  have on_side (side : Bool) (x : D.sideRegion side) :
      fold ⟨x, D.side_subset_kite side x.property⟩ = ((D.sideTriangle side).homeomorph.symm x).val :=
    agrees side x
  have formulas (side : Bool) := (D.sideTriangle side).rigid_pieces
  choose pieces finite_pieces rigid selected using formulas
  refine ⟨⟨fold, on_side, ⋃ side, pieces side, finite_iUnion finite_pieces, ?_, ?_⟩⟩
  · intro f member
    obtain ⟨side, member⟩ := mem_iUnion.mp member
    exact rigid side f member
  · intro x
    have covered : x.val ∈ ⋃ side, D.sideRegion side := D.kite_eq_sides.symm ▸ x.property
    obtain ⟨side, inside⟩ := mem_iUnion.mp covered
    obtain ⟨f, member, formula⟩ := selected side ⟨x, inside⟩
    refine ⟨f, mem_iUnion.mpr ⟨side, member⟩, ?_⟩
    have fold_value := on_side side ⟨x, inside⟩
    change (fold x : Space) = f x
    rw [fold_value]
    exact formula

namespace Folding

variable {D : PlacedCutEdgeTriangles T edge} (fold : D.Folding)

/-- Every point of the kite folds to a point represented by that same triangle map. -/
theorem places (x : D.kite) : D.Places (fold.map x) x.val := by
  have covered : x.val ∈ ⋃ side, D.sideRegion side := D.kite_eq_sides.symm ▸ x.property
  obtain ⟨side, inside⟩ := mem_iUnion.mp covered
  let original := (D.sideTriangle side).homeomorph.symm ⟨x, inside⟩
  have at_point : fold.map x = original.val := fold.on_side side ⟨x, inside⟩
  rw [at_point]
  refine ⟨side, original.property, ?_⟩
  exact congrArg Subtype.val ((D.sideTriangle side).homeomorph.apply_symm_apply ⟨x, inside⟩)

/-- Folding a represented point recovers its actual original surface value. -/
theorem map_of_placement {b : frontier P.body} {x : Plane} (placed : D.Places b x) :
    fold.map ⟨x, D.places_mem_kite placed⟩ = b := by
  obtain ⟨side, inside, same⟩ := placed
  subst x
  rw [fold.on_side side]
  exact congrArg Subtype.val ((D.sideTriangle side).homeomorph.symm_apply_apply ⟨b, inside⟩)

end Folding
end SixVertexUnfolding.ConvexPolyhedron.PlacedCutEdgeTriangles
