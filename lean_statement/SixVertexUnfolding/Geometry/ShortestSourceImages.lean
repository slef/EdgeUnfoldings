import SixVertexUnfolding.Geometry.FiniteSourceImages
import SixVertexUnfolding.Geometry.ShortestFiniteDevelopments

/-! On a point belonging to a unique facet, intrinsic distance is distance
from one of finitely many developed source copies in that facet's plane. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace SurfacePath

variable {P : ConvexPolyhedron} {a b : Space}

/-- A vertex-free shortest route selects a source image in the endpoint's unique facet. -/
theorem exists_source_image (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve)
    (avoids : ∀ t : unitInterval, 0 < t → t < 1 → path.curve t ∉ P.vertices)
    (F : P.Face) (unique : ∀ G : P.Face, b ∈ G.val → G = F) :
    ∃ source ∈ P.sourceImages a F, P.surfaceDist a b = dist source (P.faceCoordinates F b) := by
  obtain ⟨code, _, target, distance⟩ := path.exists_fixed_development shortest finite speed avoids
  have last_face := unique (code.face code.last) target
  refine ⟨code.sourceImage a, ⟨⟨code, last_face⟩, rfl⟩, ?_⟩
  rw [surfaceDist, ← path.length_eq_surfaceEDist shortest, ← distance,
    code.distanceValue_eq_source_distance a b target, last_face]

end SurfacePath

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a b : Space}

include graph small_faces in
/-- The four canonical models have a finite source-image formula at every unique-face point. -/
theorem exists_source_image (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body)
    (different : a ≠ b) (F : P.Face) (unique : ∀ G : P.Face, b ∈ G.val → G = F) :
    ∃ source ∈ P.sourceImages a F, P.surfaceDist a b = dist source (P.faceCoordinates F b) := by
  obtain ⟨path, shortest, finite, speed, _, avoids⟩ :=
    graph.exists_vertex_avoiding_shortest_path small_faces ha hb different
  exact path.exists_source_image shortest finite speed avoids F unique

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
