import SixVertexUnfolding.Geometry.SmallPolyhedronShortestRoutes
import SixVertexUnfolding.Geometry.ContinuousFiniteChoice
import SixVertexUnfolding.Geometry.UniqueFaceNeighborhoods

/-! Away from equal-distance source-copy loci, intrinsic distance on a
unique-face neighborhood is one fixed planar distance formula. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a b : Space}

include size small_faces in
/-- Distinct source-image distances force one fixed local formula for intrinsic distance. -/
theorem small_locally_one_source_image (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body)
    (different : a ≠ b) (F : P.Face) (unique : ∀ G : P.Face, b ∈ G.val → G = F)
    (no_ties : ∀ p ∈ P.sourceImages a F, ∀ q ∈ P.sourceImages a F, p ≠ q →
      dist p (P.faceCoordinates F b) ≠ dist q (P.faceCoordinates F b)) :
    ∃ source ∈ P.sourceImages a F, ∃ U : Set Space, IsOpen U ∧ b ∈ U ∧
      ∀ x ∈ U ∩ frontier P.body, P.surfaceDist a x = dist source (P.faceCoordinates F x) := by
  classical
  let copies := P.sourceImages a F
  letI : Fintype copies := (P.sourceImages_finite a F).fintype
  obtain ⟨V, openV, bV, in_face⟩ := P.unique_face_neighborhood F unique
  let S := (V ∩ ({a}ᶜ : Set Space)) ∩ frontier P.body
  have inS : b ∈ S := ⟨⟨bV, different.symm⟩, hb⟩
  let f := P.surfaceDist a
  let g (p : copies) (x : Space) := dist (p : Plane) (P.faceCoordinates F x)
  have continuous_f : ContinuousOn f S :=
    (P.surfaceDist_continuousOn ha).mono (fun _ hx => hx.2)
  have continuous_g (p : copies) : ContinuousOn (g p) S :=
    (continuous_const.dist (P.faceCoordinates F).continuous_of_finiteDimensional).continuousOn
  have selected (x : Space) (hx : x ∈ S) : ∃ p : copies, f x = g p x := by
    obtain ⟨p, hp, distance⟩ := small_exists_source_image size small_faces ha hx.2
      (fun same => hx.1.2 same.symm) F (in_face x ⟨hx.1.1, hx.2⟩).2
    exact ⟨⟨p, hp⟩, distance⟩
  obtain ⟨p, at_b⟩ := selected b inS
  have separated (q : copies) (different_copy : q ≠ p) : g p b ≠ g q b :=
    no_ties p p.property q q.property (fun same => different_copy (Subtype.ext same.symm))
  obtain ⟨W, openW, bW, constant⟩ := continuous_finite_choice_local S f g continuous_f continuous_g
    selected b inS p at_b separated
  refine ⟨p, p.property, (W ∩ V) ∩ ({a}ᶜ : Set Space),
    (openW.inter openV).inter isClosed_singleton.isOpen_compl, ⟨⟨bW, bV⟩, different.symm⟩, ?_⟩
  intro x hx
  exact constant x ⟨hx.1.1.1, ⟨⟨hx.1.1.2, hx.1.2⟩, hx.2⟩⟩

end SixVertexUnfolding.ConvexPolyhedron
