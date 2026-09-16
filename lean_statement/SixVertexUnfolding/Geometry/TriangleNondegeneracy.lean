import SixVertexUnfolding.Geometry.TetrahedronFaces

/-! Genuine vertices give nondegenerate triangles; tetrahedron vertices are not coplanar. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Three different genuine vertices satisfy the strict triangle inequality. -/
theorem vertex_triangle_strict (P : ConvexPolyhedron) (a b c : P.Vertex)
    (ab : a ≠ b) (bc : b ≠ c) :
    dist (a : Space) c < dist (a : Space) b + dist (b : Space) c := by
  apply dist_lt_dist_add_dist_iff.mpr
  intro between
  rcases P.vertex_in_segment_is_endpoint b.property (P.vertices_subset_body a.property)
    (P.vertices_subset_body c.property) between.mem_segment with left | right
  · exact ab (Subtype.ext left)
  · exact bc (Subtype.ext right.symm)

/-- A distance-preserving copy of three different original vertices is not collinear. -/
theorem placed_triangle_noncollinear (P : ConvexPolyhedron) (a b c : P.Vertex)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (A B C : Plane)
    (AB : dist A B = dist (a : Space) b) (AC : dist A C = dist (a : Space) c)
    (BC : dist B C = dist (b : Space) c) : ¬ Collinear ℝ ({A, B, C} : Set Plane) := by
  intro collinear
  rcases collinear.wbtw_or_wbtw_or_wbtw with middle_B | middle_C | middle_A
  · have equal := dist_add_dist_eq_iff.mpr middle_B
    rw [AB, BC, AC] at equal
    exact (P.vertex_triangle_strict a b c ab bc).ne equal.symm
  · have equal := dist_add_dist_eq_iff.mpr middle_C
    rw [BC, dist_comm C A, AC, dist_comm B A, AB] at equal
    have strict := P.vertex_triangle_strict b c a bc ac.symm
    rw [dist_comm (b : Space) (a : Space), dist_comm (c : Space) (a : Space)] at strict
    exact strict.ne equal.symm
  · have equal := dist_add_dist_eq_iff.mpr middle_A
    rw [dist_comm C A, AC, AB, dist_comm C B, BC] at equal
    have strict := P.vertex_triangle_strict c a b ac.symm ab
    rw [dist_comm (c : Space) (b : Space), dist_comm (c : Space) (a : Space)] at strict
    exact strict.ne equal.symm

/-- The vertex opposite a tetrahedron facet does not lie even in that facet's affine plane. -/
theorem opposite_vertex_outside_face_span (P : ConvexPolyhedron) (size : P.vertices.card = 4)
    (v : P.Vertex) : (v : Space) ∉ affineSpan ℝ (P.oppositeFace size v).val := by
  intro in_plane
  have in_face : (v : Space) ∈ (P.oppositeFace size v).val := by
    rw [← (P.oppositeFace size v).body_inter_affineSpan]
    exact ⟨P.vertices_subset_body v.property, in_plane⟩
  exact (P.vertex_mem_oppositeFace size v v).mp in_face rfl

/-- Any one of four genuine tetrahedron vertices lies outside the plane of the other three. -/
theorem tetrahedron_vertex_outside_triangle_span (P : ConvexPolyhedron)
    (size : P.vertices.card = 4) (a b c d : P.Vertex)
    (ad : a ≠ d) (bd : b ≠ d) (cd : c ≠ d) :
    (d : Space) ∉ affineSpan ℝ ({(a : Space), (b : Space), (c : Space)} : Set Space) := by
  intro in_plane
  apply P.opposite_vertex_outside_face_span size d
  apply affineSpan_mono ℝ (show ({(a : Space), (b : Space), (c : Space)} : Set Space) ⊆
    (P.oppositeFace size d).val from ?_) in_plane
  rintro x (rfl | rfl | rfl)
  exacts [(P.vertex_mem_oppositeFace size d a).mpr ad,
    (P.vertex_mem_oppositeFace size d b).mpr bd, (P.vertex_mem_oppositeFace size d c).mpr cd]

end SixVertexUnfolding.ConvexPolyhedron
