import SixVertexUnfolding.Geometry.VertexNeighborOrder
import SixVertexUnfolding.Geometry.FacetCornerNeighborhood
import SixVertexUnfolding.Geometry.NonvertexFacetNeighborhoods

/-! A cyclic list of actual corner triangles covering a whole surface
neighborhood of a vertex. These triangles may be proper parts of faces. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

structure VertexFaceFan (P : ConvexPolyhedron) (pole : P.Vertex) (n : ℕ) [NeZero n] where
  order : Fin n ≃ P.edgeGraph.neighborSet pole
  face : Fin n → P.Face
  consecutive : ∀ i, (P.neighborLink pole).Adj (order i) (order (i + 1))
  pole_mem : ∀ i, (pole : Space) ∈ (face i).val
  left_mem : ∀ i, ((order i).val : Space) ∈ (face i).val
  right_mem : ∀ i, ((order (i + 1)).val : Space) ∈ (face i).val

theorem exists_vertex_face_fan (P : ConvexPolyhedron) (size : P.vertices.card ≤ 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (pole : P.Vertex) {n : ℕ} [NeZero n] (degree : P.edgeGraph.degree pole = n) :
    Nonempty (P.VertexFaceFan pole n) := by
  obtain ⟨order, consecutive⟩ := P.neighborLink_cyclic_order size small_faces pole degree
  choose faces on_face using fun i => (consecutive i).2
  exact ⟨⟨order, faces, consecutive, fun i => (on_face i).1,
    fun i => (on_face i).2.1, fun i => (on_face i).2.2⟩⟩

namespace VertexFaceFan

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n)

def neighbor (i : Fin n) : P.Vertex := (fan.order i).val

theorem adjacent (i : Fin n) : P.edgeGraph.Adj pole (fan.neighbor i) := (fan.order i).property

theorem neighbors_distinct : Function.Injective fan.neighbor :=
  fun _ _ same => fan.order.injective (Subtype.ext same)

theorem successive_distinct (i : Fin n) : fan.neighbor i ≠ fan.neighbor (i + 1) :=
  fun same => (fan.consecutive i).1 (Subtype.ext same)

theorem neighbor_ne_pole (i : Fin n) : (fan.neighbor i : Space) ≠ pole :=
  fun same => (fan.adjacent i).ne (Subtype.ext same.symm)

def triangle (i : Fin n) : Set Space :=
  convexHull ℝ ({(pole : Space), (fan.neighbor i : Space), (fan.neighbor (i + 1) : Space)} : Set Space)

theorem triangle_subset_face (i : Fin n) : fan.triangle i ⊆ (fan.face i).val := by
  apply convexHull_min _ (fan.face i).convex
  rintro x (rfl | rfl | rfl)
  exacts [fan.pole_mem i, fan.left_mem i, fan.right_mem i]

theorem triangle_noncollinear (i : Fin n) :
    ¬ Collinear ℝ ({(fan.neighbor i : Space), (pole : Space),
      (fan.neighbor (i + 1) : Space)} : Set Space) :=
  P.no_three_collinear_vertices (fan.neighbor i).property pole.property
    (fan.neighbor (i + 1)).property (fan.neighbor_ne_pole i)
    (fun same => fan.successive_distinct i (Subtype.ext same))
    (fan.neighbor_ne_pole (i + 1)).symm

variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- The listed faces exhaust every incident original face. -/
theorem covers (F : P.Face) : (pole : Space) ∈ F.val ↔ F ∈ range fan.face := by
  have three : 3 ≤ n := by
    have count := Nat.card_congr fan.order
    have lower := P.edgeGraph_min_degree pole
    rw [Nat.card_fin, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at count
    omega
  have two (v : P.edgeGraph.neighborSet pole) : ((P.neighborLink pole).neighborSet v).ncard = 2 := by
    obtain ⟨c, d, different, neighbors⟩ := P.neighborLink_two_neighbors small_faces pole v
    rw [neighbors, Set.ncard_pair different]
  constructor
  · intro poleF
    obtain ⟨b, pb, bF⟩ := F.exists_corner_edge (small_faces F) pole poleF
    obtain ⟨c, cb, pc, cF, _⟩ := F.exists_other_corner_neighbor (small_faces F) pole b pb poleF bF
    let B : P.edgeGraph.neighborSet pole := ⟨b, pb⟩
    let C : P.edgeGraph.neighborSet pole := ⟨c, pc⟩
    let i := fan.order.symm B
    have at_i : fan.order i = B := fan.order.apply_symm_apply B
    have adjacent : (P.neighborLink pole).Adj B C :=
      ⟨fun same => cb (congrArg Subtype.val same).symm, F, poleF, bF, cF⟩
    have member : C ∈ (P.neighborLink pole).neighborSet (fan.order i) := by
      rw [at_i]; exact adjacent
    rw [spanning_cycle_neighbors (P.neighborLink pole) three two fan.order fan.consecutive i] at member
    have at_b : fan.neighbor i = b := congrArg Subtype.val at_i
    rcases member with previous | next
    · have at_c : fan.neighbor (i - 1) = c := (congrArg Subtype.val previous).symm
      refine ⟨i - 1, ?_⟩
      apply (fan.face (i - 1)).eq_of_three_vertices F pole c b pc.ne pb.ne cb
        (fan.pole_mem _) (by simpa only [← at_c] using fan.left_mem (i - 1))
        (by simpa only [sub_add_cancel, ← at_b] using fan.right_mem (i - 1)) poleF cF bF
    · have at_c : fan.neighbor (i + 1) = c := (congrArg Subtype.val next).symm
      refine ⟨i, ?_⟩
      exact (fan.face i).eq_of_three_vertices F pole b c pb.ne pc.ne cb.symm
        (fan.pole_mem _) (at_b ▸ fan.left_mem i) (at_c ▸ fan.right_mem i) poleF bF cF
  · rintro ⟨i, rfl⟩
    exact fan.pole_mem i

include small_faces in
/-- The actual corner triangles cover the entire surface near the pole. -/
theorem surface_neighborhood :
    ∃ U : Set Space, IsOpen U ∧ (pole : Space) ∈ U ∧
      U ∩ frontier P.body ⊆ ⋃ i : Fin n, fan.triangle i := by
  have local_cover (i : Fin n) := (fan.face i).corner_triangle_neighborhood (small_faces _)
    pole (fan.neighbor i) (fan.neighbor (i + 1)) (fan.adjacent i) (fan.adjacent (i + 1))
    (fan.successive_distinct i) (fan.pole_mem i) (fan.left_mem i) (fan.right_mem i)
  choose U openU poleU inside using local_cover
  obtain ⟨V, openV, poleV, incident⟩ := P.incident_facets_neighborhood pole
  refine ⟨V ∩ ⋂ i, U i, openV.inter (isOpen_iInter_of_finite openU),
    ⟨poleV, mem_iInter.mpr poleU⟩, ?_⟩
  rintro x ⟨⟨near, allU⟩, surface⟩
  obtain ⟨F, member⟩ := P.boundary_point_in_face surface
  obtain ⟨i, rfl⟩ := (fan.covers small_faces F).mp (incident x near F member)
  exact mem_iUnion.mpr ⟨i, inside i ⟨mem_iInter.mp allU i, member⟩⟩

end VertexFaceFan
end SixVertexUnfolding.ConvexPolyhedron
