import SixVertexUnfolding.Geometry.FullRouteSourceCode
import SixVertexUnfolding.Geometry.FaceDevelopmentInverses
import SixVertexUnfolding.Geometry.ClosedCutEdgeRoutes
import SixVertexUnfolding.Geometry.ClosedRouteStrips
import SixVertexUnfolding.Geometry.TriangleFanParameters

/-! A radial strip over a cut edge inside a face is assembled from a
finite list of rigid face placements. Closure includes its endpoint rays. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Every point of the closed strip uses one of finitely many rigid face placements. -/
theorem closed_strip_face_pieces (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
    (F : P.Face)
    (unique_face : ∀ t, ∀ G : P.Face, (T.openEdgeTarget edge t : Space) ∈ G.val → G = F)
    (p : Plane) (terminal : ∀ t : Ioo (0 : ℝ) 1, P.HasTerminalSource (routes (interiorTime t)) F p) :
    ∀ z, ∃ piece : P.FaceDevelopmentPiece F,
      (closedRouteStripMap routes z : Space) ∈ piece.face.val ∧
      piece.place (closedRouteStripMap routes z) =
        triangleFanMap p (P.faceCoordinates F u) (P.faceCoordinates F v) z := by
  let surface := closedRouteStripMap routes
  let planar := triangleFanMap p (P.faceCoordinates F u) (P.faceCoordinates F v)
  let good (piece : P.FaceDevelopmentPiece F) : Set (unitInterval × unitInterval) :=
    {z | (surface z : Space) ∈ piece.face.val ∧ piece.place (surface z) = planar z}
  have surface_cont : Continuous (fun z => (surface z : Space)) :=
    continuous_subtype_val.comp surface.continuous
  have closed (piece : P.FaceDevelopmentPiece F) : IsClosed (good piece) :=
    (piece.face.isClosed.preimage surface_cont).inter
      (isClosed_eq (piece.place.continuous_of_finiteDimensional.comp surface_cont) planar.continuous)
  let inclusion : Ioo (0 : ℝ) 1 × unitInterval → unitInterval × unitInterval :=
    Prod.map interiorTime id
  have dense : DenseRange inclusion := interiorTime_dense.prodMap denseRange_id
  have interior (z : Ioo (0 : ℝ) 1 × unitInterval) : inclusion z ∈ ⋃ piece, good piece := by
    have start : routes (interiorTime z.1) 0 = a := congrArg Prod.fst (member _).2
    have finish : routes (interiorTime z.1) 1 = T.openEdgeTarget edge z.1 :=
      congrArg Prod.snd (member _).2
    obtain ⟨piece, inside, placed⟩ := graph.full_route_developed_pieces small_faces
      (routes (interiorTime z.1)) (member _).1
      (by simpa only [start, finish] using T.openEdgeTarget_different edge z.1)
      F (by simpa only [finish] using unique_face z.1) p (terminal z.1) z.2
    refine mem_iUnion.mpr ⟨piece, inside, ?_⟩
    change piece.place (routes (interiorTime z.1) z.2) =
      AffineMap.lineMap p (AffineMap.lineMap (P.faceCoordinates F u) (P.faceCoordinates F v) (z.1 : ℝ)) (z.2 : ℝ)
    rw [placed, finish, ← AffineMap.apply_lineMap]
    rfl
  intro z
  have covered : z ∈ ⋃ piece, good piece :=
    dense.induction_on z (isClosed_iUnion_of_finite closed) interior
  exact mem_iUnion.mp covered

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
