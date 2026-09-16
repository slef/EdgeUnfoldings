import SixVertexUnfolding.Geometry.GeodesicBranchIsolation

/-! Unique routes remain unique under small target motions inside a face.
Compactness prevents new distant routes, and source recovery prevents nearby splitting. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Uniqueness of a shortest route persists near any distinct target belonging to just one face. -/
theorem unique_geodesics_nearby (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F)
    (unique_route : (P.geodesicFiber a b).Subsingleton) :
    ∃ V : Set (frontier P.body), IsOpen V ∧ b ∈ V ∧
      ∀ c ∈ V, (P.geodesicFiber a c).Subsingleton := by
  obtain ⟨f, hf⟩ := P.geodesicFiber_nonempty a b
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨W, openW, fW, isolated⟩ := graph.geodesic_branch_isolation small_faces f
    (by simpa only [first, last] using different) F (by simpa only [last] using unique_face)
  obtain ⟨N, openN, abN, contains⟩ := P.geodesic_family_upper_continuous (a, b) W openW
    (fun g geodesic ends => unique_route ⟨geodesic, ends⟩ hf ▸ fW)
  refine ⟨(fun c => (a, c)) ⁻¹' N, openN.preimage (continuous_const.prodMk continuous_id), abN, ?_⟩
  intro c cN g hg h hh
  have gW := contains g hg.1 (hg.2 ▸ cN)
  have hW := contains h hh.1 (hh.2 ▸ cN)
  exact isolated g gW h hW hg.1 hh.1
    ((congrArg Prod.fst hg.2).trans first.symm)
    ((congrArg Prod.fst hh.2).trans first.symm)
    ((congrArg Prod.snd hg.2).trans (congrArg Prod.snd hh.2).symm)

include graph small_faces in
/-- Within the boundary, distinct targets with one incident face and a unique route form an open set. -/
theorem unique_geodesics_in_face_open (a : frontier P.body) (F : P.Face) :
    IsOpen {b : frontier P.body | a ≠ b ∧
      (∀ G : P.Face, (b : Space) ∈ G.val → G = F) ∧ (P.geodesicFiber a b).Subsingleton} := by
  apply isOpen_iff_forall_mem_open.mpr
  intro b hb
  obtain ⟨V, openV, bV, routes⟩ := graph.unique_geodesics_nearby small_faces a b hb.1 F hb.2.1 hb.2.2
  obtain ⟨U, openU, bU, faces⟩ := P.unique_face_neighborhood F hb.2.1
  let W : Set (frontier P.body) := V ∩ ((Subtype.val ⁻¹' U) ∩ {c | a ≠ c})
  refine ⟨W, ?_, openV.inter ((openU.preimage continuous_subtype_val).inter
    (isClosed_eq continuous_const continuous_id).isOpen_compl), ⟨bV, bU, hb.1⟩⟩
  intro c hc
  exact ⟨hc.2.2, (faces _ ⟨hc.2.1, c.property⟩).2, routes c hc.1⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
