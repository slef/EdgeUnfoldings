import SixVertexUnfolding.Geometry.TerminalSourceData
import SixVertexUnfolding.Geometry.GeodesicFibers

/-! Active sources are developed copies belonging to actual shortest routes
to a fixed target. Unused face-sequence candidates are excluded. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- The terminal sources of the actual shortest routes from `a` to `b`. -/
def activeSources (P : ConvexPolyhedron) (a b : frontier P.body) (F : P.Face) : Set Plane :=
  {source | ∃ f ∈ P.geodesicFiber a b, P.HasTerminalSource f F source}

/-- All active sources give the same distance at the original target. -/
theorem activeSource_distance (P : ConvexPolyhedron) (a b : frontier P.body) (F : P.Face)
    (source : Plane) (active : source ∈ P.activeSources a b F) :
    P.surfaceDist a b = dist source (P.faceCoordinates F b) := by
  obtain ⟨f, hf, terminal⟩ := active
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  simpa only [first, last] using terminal.distance hf.1

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Every active source is one of the finitely many developed face-sequence candidates. -/
theorem activeSources_subset (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    P.activeSources a b F ⊆ P.sourceImages a F := by
  rintro source ⟨f, hf, terminal⟩
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨other, member, actual⟩ := graph.exists_terminal_source small_faces f hf.1
    (by simpa only [first, last] using different) F (by simpa only [last] using unique_face)
  rw [terminal.unique actual]
  simpa only [first] using member

include graph small_faces in
/-- Only finitely many actual source copies occur at an interior-face target. -/
theorem activeSources_finite (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    (P.activeSources a b F).Finite :=
  (P.sourceImages_finite a F).subset (graph.activeSources_subset small_faces a b different F unique_face)

include graph small_faces in
/-- At least one actual source copy occurs at an interior-face target. -/
theorem activeSources_nonempty (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    (P.activeSources a b F).Nonempty := by
  obtain ⟨f, hf⟩ := P.geodesicFiber_nonempty a b
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨source, _, terminal⟩ := graph.exists_terminal_source small_faces f hf.1
    (by simpa only [first, last] using different) F (by simpa only [last] using unique_face)
  exact ⟨source, f, hf, terminal⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
