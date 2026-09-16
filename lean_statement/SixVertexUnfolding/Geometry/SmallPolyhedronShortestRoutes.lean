import SixVertexUnfolding.Geometry.SmallPolyhedronVertexAvoidance
import SixVertexUnfolding.Geometry.FinitelyManyShortestRoutes
import SixVertexUnfolding.Geometry.ShortestFiniteDevelopments
import SixVertexUnfolding.Geometry.ShortestSourceImages
import SixVertexUnfolding.Geometry.GeodesicFibers

/-! Apply all-vertex avoidance to the existing finite-development and
nonbranching arguments. These results now cover the universal-vertex
solids as well as the earlier four canonical graph models. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a b : Space}

include size small_faces in
/-- Distinct endpoints admit only finitely many normalized shortest routes. -/
theorem small_finite_shortest_routes (different : a ≠ b) :
    {path : P.SurfacePath a b | path.IsShortest ∧ path.length ≠ ⊤ ∧
      LipschitzWith path.length.toNNReal path.curve}.Finite := by
  apply (P.finite_vertex_free_shortest_routes a b).subset
  intro path hp
  exact ⟨hp.1, hp.2.1, hp.2.2,
    small_shortest_lipschitz_avoids_vertices size small_faces path different hp.1 hp.2.1 hp.2.2⟩

include size small_faces in
/-- Each compact normalized geodesic fiber between distinct endpoints is finite. -/
theorem small_geodesicFiber_finite (a b : frontier P.body) (different : a ≠ b) :
    (P.geodesicFiber a b).Finite := by
  have paths := small_finite_shortest_routes size small_faces
    (fun h : (a : Space) = (b : Space) => different (Subtype.ext h))
  apply (paths.image SurfacePath.boundaryCurve).subset
  intro f hf
  obtain ⟨path, shortest, finite, speed, same⟩ := P.geodesicFiber_path a b f hf
  exact ⟨path, ⟨shortest, finite, speed⟩, same⟩

include size small_faces in
/-- Intrinsic distance is one of the finite original-face development formulas. -/
theorem small_surfaceDist_mem_developed_values
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) (different : a ≠ b) :
    P.surfaceDist a b ∈ P.developedDistanceValues a b := by
  obtain ⟨path, shortest, finite, speed, _, avoids⟩ :=
    small_exists_vertex_avoiding_shortest_path size small_faces ha hb different
  exact path.surfaceDist_mem_developed_values shortest finite speed avoids

include size small_faces in
/-- At a unique-face target, one of the finite source copies gives the exact distance. -/
theorem small_exists_source_image
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique : ∀ G : P.Face, b ∈ G.val → G = F) :
    ∃ source ∈ P.sourceImages a F, P.surfaceDist a b = dist source (P.faceCoordinates F b) := by
  obtain ⟨path, shortest, finite, speed, _, avoids⟩ :=
    small_exists_vertex_avoiding_shortest_path size small_faces ha hb different
  exact path.exists_source_image shortest finite speed avoids F unique

include size small_faces in
/-- Two shortest routes with the same endpoints coincide if they meet internally. -/
theorem small_shortest_routes_agree_of_meeting
    (first second : P.SurfacePath a b) (different : a ≠ b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (m : unitInterval) (after_start : 0 < m) (before_end : m < 1)
    (meet : first.curve m = second.curve m) : ∀ t, first.curve t = second.curve t :=
  first.agree_of_interior_meeting second first_shortest second_shortest first_finite second_finite
    first_speed second_speed
    (small_shortest_lipschitz_avoids_vertices size small_faces first different first_shortest
      first_finite first_speed) m after_start before_end meet

include size small_faces in
/-- Distinct shortest routes have disjoint open traces. -/
theorem small_distinct_shortest_routes_disjoint
    (first second : P.SurfacePath a b) (different : a ≠ b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (distinct_routes : ¬ ∀ t, first.curve t = second.curve t) :
    Disjoint (first.curve '' Ioo (0 : unitInterval) 1) (second.curve '' Ioo (0 : unitInterval) 1) :=
  first.disjoint_open_traces second different first_shortest second_shortest first_finite second_finite
    first_speed second_speed
    (small_shortest_lipschitz_avoids_vertices size small_faces first different first_shortest
      first_finite first_speed) distinct_routes

end SixVertexUnfolding.ConvexPolyhedron
