import SixVertexUnfolding.Geometry.BipyramidMetric
import SixVertexUnfolding.Geometry.PlacedTriangle

/-! The placed bases, their boundary neighbors, and the poles outside the opposite bases. -/

namespace SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices.Development

variable {P : ConvexPolyhedron} {B : P.BipyramidVertices}
    {triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3}
    {source : Fin 3} (net : B.Development triangles source)

/-- The whole planar image of one original face in this development. -/
def faceImage (upper : Bool) (missing : Fin 3) : Set Plane :=
  (net.cap upper).place missing '' (B.face triangles upper missing).val

theorem faceImage_convex (upper : Bool) (missing : Fin 3) : Convex ℝ (net.faceImage upper missing) :=
  (B.face triangles upper missing).convex.affine_image ((net.cap upper).place missing)

theorem faceImage_closed (upper : Bool) (missing : Fin 3) : IsClosed (net.faceImage upper missing) :=
  (B.face triangles upper missing).placed_face_closed ((net.cap upper).place missing)

theorem faceImage_regular (upper : Bool) (missing : Fin 3) :
    closure (interior (net.faceImage upper missing)) = net.faceImage upper missing :=
  (B.face triangles upper missing).placed_face_regular ((net.cap upper).place missing)
    ((net.cap upper).rigid missing)

theorem faceImage_interior_nonempty (upper : Bool) (missing : Fin 3) :
    (interior (net.faceImage upper missing)).Nonempty :=
  (B.face triangles upper missing).placed_face_interior_nonempty ((net.cap upper).place missing)
    ((net.cap upper).rigid missing)

/-- The common pole copy belongs to every triangle on its cap. -/
theorem pole_mem_faceImage (upper : Bool) (missing : Fin 3) :
    (net.cap upper).place source (B.poleVertex upper) ∈ net.faceImage upper missing := by
  rw [← net.petal_pole_agreement upper missing]
  exact ⟨B.poleVertex upper, B.pole_mem_face triangles upper missing, rfl⟩

/-- A retained equator vertex belongs to every face which contains that original vertex. -/
theorem equator_mem_faceImage (upper : Bool) (missing i : Fin 3)
    (in_face : i ≠ missing) (in_base : i ≠ source) :
    (net.cap upper).place source (B.equatorVertex i) ∈ net.faceImage upper missing := by
  rw [← net.petal_equator_agreement upper missing i in_face in_base]
  exact ⟨B.equatorVertex i, (B.equator_mem_face triangles upper missing i).mpr in_face, rfl⟩

/-- Name the two equator endpoints of either central base. -/
theorem base_vertices (upper : Bool) (i j : Fin 3)
    (isource : i ≠ source) (jsource : j ≠ source) (different : i ≠ j) :
    (B.face triangles upper source).val ∩ (P.vertices : Set Space) =
      {(B.poleVertex upper : Space), (B.equatorVertex i : Space), (B.equatorVertex j : Space)} := by
  have pair : {k : Fin 3 | k ≠ source} = {i, j} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  rw [B.face_vertices, faceVertices, pair, Set.image_insert_eq, Set.image_singleton]

theorem base_image_hull (upper : Bool) (i j : Fin 3)
    (isource : i ≠ source) (jsource : j ≠ source) (different : i ≠ j) :
    net.faceImage upper source = convexHull ℝ
      {((net.cap upper).place source (B.poleVertex upper)),
        ((net.cap upper).place source (B.equatorVertex i)),
        ((net.cap upper).place source (B.equatorVertex j))} :=
  (B.face triangles upper source).placed_triangle_hull ((net.cap upper).place source)
    (B.poleVertex upper) (B.equatorVertex i) (B.equatorVertex j)
    (base_vertices (B := B) upper i j isource jsource different)

/-- The two bases have disjoint interiors in either ordering. -/
theorem bases_disjoint (upper : Bool) :
    Disjoint (interior (net.faceImage upper source)) (interior (net.faceImage (!upper) source)) := by
  cases upper
  · exact net.bases_safe.symm
  · exact net.bases_safe

/-- The three retained neighboring faces cover every boundary point of a central base. -/
theorem base_boundary_covered (upper : Bool) (i j : Fin 3)
    (isource : i ≠ source) (jsource : j ≠ source) (different : i ≠ j) :
    frontier (net.faceImage upper source) ⊆ net.faceImage upper i ∪
      (net.faceImage upper j ∪ net.faceImage (!upper) source) := by
  let place := (net.cap upper).place source
  have pole_in := B.pole_mem_face triangles upper source
  have i_in := (B.equator_mem_face triangles upper source i).mpr isource
  have j_in := (B.equator_mem_face triangles upper source j).mpr jsource
  have distinct_equator : B.equatorVertex i ≠ B.equatorVertex j :=
    fun same => different (B.equator_injective same)
  have noncollinear := P.placed_triangle_noncollinear (B.poleVertex upper) (B.equatorVertex i)
    (B.equatorVertex j) (B.pole_ne_equator upper i) (B.pole_ne_equator upper j) distinct_equator
    (place (B.poleVertex upper)) (place (B.equatorVertex i)) (place (B.equatorVertex j))
    ((net.cap upper).rigid source _ pole_in _ i_in)
    ((net.cap upper).rigid source _ pole_in _ j_in)
    ((net.cap upper).rigid source _ i_in _ j_in)
  have edges := (B.face triangles upper source).placed_triangle_frontier place
    (B.poleVertex upper) (B.equatorVertex i) (B.equatorVertex j)
    (base_vertices (B := B) upper i j isource jsource different) noncollinear
  have i_opposite : place (B.equatorVertex i) ∈ net.faceImage (!upper) source := by
    change (net.cap upper).place source (B.equatorVertex i) ∈ _
    rw [net.base_equator_agreement upper i isource]
    exact net.equator_mem_faceImage (!upper) source i isource isource
  have j_opposite : place (B.equatorVertex j) ∈ net.faceImage (!upper) source := by
    change (net.cap upper).place source (B.equatorVertex j) ∈ _
    rw [net.base_equator_agreement upper j jsource]
    exact net.equator_mem_faceImage (!upper) source j jsource jsource
  intro x boundary
  rcases edges boundary with pole_i | pole_j | equator
  · exact Or.inr (Or.inl ((net.faceImage_convex upper j).segment_subset
      (net.pole_mem_faceImage upper j) (net.equator_mem_faceImage upper j i different isource) pole_i))
  · exact Or.inl ((net.faceImage_convex upper i).segment_subset
      (net.pole_mem_faceImage upper i) (net.equator_mem_faceImage upper i j different.symm jsource) pole_j)
  · exact Or.inr (Or.inr ((net.faceImage_convex (!upper) source).segment_subset i_opposite j_opposite equator))

/-- The opposite pole lies outside a central base: otherwise its whole base would overlap. -/
theorem opposite_pole_outside_base (upper : Bool) :
    (net.cap (!upper)).place source (B.poleVertex (!upper)) ∉ net.faceImage upper source := by
  intro inside
  obtain ⟨i, j, different, pair⟩ := equator_complement_pair source
  have isource : i ≠ source := (Set.ext_iff.mp pair i).mpr (Or.inl rfl)
  have jsource : j ≠ source := (Set.ext_iff.mp pair j).mpr (Or.inr rfl)
  have i_in : (net.cap (!upper)).place source (B.equatorVertex i) ∈ net.faceImage upper source := by
    have member := net.equator_mem_faceImage upper source i isource isource
    rwa [net.base_equator_agreement upper i isource] at member
  have j_in : (net.cap (!upper)).place source (B.equatorVertex j) ∈ net.faceImage upper source := by
    have member := net.equator_mem_faceImage upper source j jsource jsource
    rwa [net.base_equator_agreement upper j jsource] at member
  have inclusion : net.faceImage (!upper) source ⊆ net.faceImage upper source := by
    rw [net.base_image_hull (!upper) i j isource jsource different]
    apply convexHull_min _ (net.faceImage_convex upper source)
    rintro x (rfl | rfl | rfl)
    exacts [inside, i_in, j_in]
  obtain ⟨x, x_other⟩ := net.faceImage_interior_nonempty (!upper) source
  exact Set.disjoint_left.mp (net.bases_disjoint upper) (interior_mono inclusion x_other) x_other

end SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices.Development
