import SixVertexUnfolding.Geometry.PocketContainment
import SixVertexUnfolding.Geometry.InteriorSegmentAvoidance

/-! A face corner inside an open region supplies a true face-interior seed by boundary density. -/

namespace SixVertexUnfolding

/-- Any point of a regular closed face lying in the region interior supplies a face-interior seed. -/
theorem convex_face_in_region_of_corner (region face : Set Plane)
    (closed : IsClosed region) (convex : Convex ℝ face)
    (regular : closure (interior face) = face) (safe : Disjoint (interior face) (frontier region))
    (corner : Plane) (on_face : corner ∈ face) (inside : corner ∈ interior region) : face ⊆ region := by
  have in_closure : corner ∈ closure (interior face) := by rwa [regular]
  obtain ⟨seed, in_region, in_face⟩ := mem_closure_iff.mp in_closure (interior region) isOpen_interior inside
  exact convex_face_in_closed_region region face closed convex regular safe seed in_face in_region

/-- A separated closed point cannot touch a segment leading into a face, except at its other endpoint. -/
theorem point_avoids_segment_to_interior (face blocked : Set Plane) (convex : Convex ℝ face)
    (safe : Disjoint (interior face) blocked) (a p x : Plane)
    (endpoint : a ∈ face) (inside : p ∈ interior face) (in_blocked : x ∈ blocked) (different : x ≠ a) :
    x ∉ segment ℝ a p := by
  have avoids := segment_avoids_of_interior_endpoint face {x} convex
    (safe.mono_right (Set.singleton_subset_iff.mpr in_blocked)) p a inside endpoint
    (show a ∉ ({x} : Set Plane) from Ne.symm different)
  intro member
  exact Set.disjoint_left.mp avoids (by rwa [segment_symm ℝ p a]) (Set.mem_singleton x)

end SixVertexUnfolding
