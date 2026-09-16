import SixVertexUnfolding.Geometry.FiniteFaceSequences
import SixVertexUnfolding.Geometry.ShortestDevelopedLine
import SixVertexUnfolding.Geometry.OctahedralVertexAvoidance

/-! Every vertex-free shortest route is represented by one of finitely many
fixed developments. This is a finite branch statement, not yet a cut-locus theorem. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace SurfacePath

variable {P : ConvexPolyhedron} {a b : Space}

/-- A fixed face-sequence development realizes the exact length and endpoint faces of this route. -/
theorem exists_fixed_development (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices) :
    ∃ code : P.FaceSequence,
      a ∈ (code.face code.first).val ∧ b ∈ (code.face code.last).val ∧
      code.distanceValue a b = path.length.toReal := by
  obtain ⟨itinerary, bounded⟩ := path.exists_face_itinerary shortest finite
  let code : P.FaceSequence := ⟨⟨⟨itinerary.count, by omega⟩, itinerary.face⟩,
    itinerary.positive, itinerary.successive_faces_adjacent avoids⟩
  let net : itinerary.Development := {
    place := code.place
    rigid := code.rigid
    joined := code.joined
    outward := code.outward }
  have source : a ∈ (code.face code.first).val := by
    have contained := itinerary.inside code.first 0
      ⟨by change itinerary.time 0 ≤ 0; rw [itinerary.first], unitInterval.nonneg'⟩
    simpa only [path.curve.source] using contained
  have target : b ∈ (code.face code.last).val := by
    have end_time : itinerary.time code.last.succ = 1 := by
      rw [show code.last.succ = Fin.last itinerary.count from Fin.ext (by
        dsimp [FaceSequence.last, FaceSequence.count, code]; have := itinerary.positive; omega)]
      exact itinerary.last
    have contained := itinerary.inside code.last 1 ⟨unitInterval.le_one', end_time.ge⟩
    simpa only [path.curve.target] using contained
  exact ⟨code, source, target, net.developed_chord_length shortest finite speed avoids⟩

/-- A vertex-free shortest route's intrinsic distance is among the finite developed values. -/
theorem surfaceDist_mem_developed_values (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices) :
    P.surfaceDist a b ∈ P.developedDistanceValues a b := by
  obtain ⟨code, _, _, length⟩ := path.exists_fixed_development shortest finite speed avoids
  refine ⟨code, ?_⟩
  change code.distanceValue a b = P.surfaceDist a b
  rw [length, surfaceDist, ← path.length_eq_surfaceEDist shortest]

end SurfacePath

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a b : Space}

include graph small_faces in
/-- For the four canonical models, intrinsic distance is one of finitely many fixed planar formulas. -/
theorem surfaceDist_mem_developed_values (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body)
    (different : a ≠ b) : P.surfaceDist a b ∈ P.developedDistanceValues a b := by
  obtain ⟨path, shortest, finite, speed, _, avoids⟩ :=
    graph.exists_vertex_avoiding_shortest_path small_faces ha hb different
  exact path.surfaceDist_mem_developed_values shortest finite speed avoids

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
