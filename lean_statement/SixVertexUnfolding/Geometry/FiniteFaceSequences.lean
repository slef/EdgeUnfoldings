import SixVertexUnfolding.Geometry.FaceChainDevelopment

/-! There are only finitely many bounded face sequences. Choose each one's
outward development once, independently of the endpoints of any route. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A bounded nonempty face sequence whose successive faces agree or share an edge. -/
def FaceSequence (P : ConvexPolyhedron) :=
  {data : Σ n : Fin (2 * Nat.card P.Face + 2), Fin n.val → P.Face //
    0 < data.1.val ∧ ∀ i j, i.val + 1 = j.val →
      data.2 i = data.2 j ∨ P.ShareEdge (data.2 i) (data.2 j)}

instance (P : ConvexPolyhedron) : Finite P.FaceSequence := by
  unfold FaceSequence
  infer_instance

namespace FaceSequence

variable {P : ConvexPolyhedron} (code : P.FaceSequence)

def count : ℕ := code.val.1.val

def face : Fin code.count → P.Face := code.val.2

theorem positive : 0 < code.count := code.property.1

theorem bounded : code.count ≤ 2 * Nat.card P.Face + 1 := by
  have bound := code.val.1.isLt
  change code.val.1.val ≤ _
  omega

theorem adjacent (i j : Fin code.count) (next : i.val + 1 = j.val) :
    code.face i = code.face j ∨ P.ShareEdge (code.face i) (code.face j) := code.property.2 i j next

private theorem placement_exists :
    ∃ place : Fin code.count → Space →ᵃ[ℝ] Plane,
      (∀ i, ∀ x ∈ (code.face i).val, ∀ y ∈ (code.face i).val, dist (place i x) (place i y) = dist x y) ∧
      (∀ i j, i.val + 1 = j.val → EqOn (place i) (place j) ((code.face i).val ∩ (code.face j).val)) ∧
      (∀ i j, i.val + 1 = j.val → OutwardFacePlacement (code.face i) (code.face j) (place i) (place j)) :=
  exists_ordered_face_development code.positive code.face code.adjacent

/-- One fixed coherent development for this face sequence. -/
noncomputable def place : Fin code.count → Space →ᵃ[ℝ] Plane := code.placement_exists.choose

theorem rigid (i : Fin code.count) :
    ∀ x ∈ (code.face i).val, ∀ y ∈ (code.face i).val, dist (code.place i x) (code.place i y) = dist x y :=
  code.placement_exists.choose_spec.1 i

theorem joined (i j : Fin code.count) (next : i.val + 1 = j.val) :
    EqOn (code.place i) (code.place j) ((code.face i).val ∩ (code.face j).val) :=
  code.placement_exists.choose_spec.2.1 i j next

theorem outward (i j : Fin code.count) (next : i.val + 1 = j.val) :
    OutwardFacePlacement (code.face i) (code.face j) (code.place i) (code.place j) :=
  code.placement_exists.choose_spec.2.2 i j next

def first : Fin code.count := ⟨0, code.positive⟩

def last : Fin code.count := ⟨code.count - 1, by have := code.positive; omega⟩

/-- The planar endpoint-distance formula attached to this fixed sequence. -/
noncomputable def distanceValue (a b : Space) : ℝ := dist (code.place code.first a) (code.place code.last b)

end FaceSequence

/-- A finite collection of planar distance values, without a claim that all are admissible routes. -/
def developedDistanceValues (P : ConvexPolyhedron) (a b : Space) : Set ℝ :=
  range (fun code : P.FaceSequence => code.distanceValue a b)

theorem developedDistanceValues_finite (P : ConvexPolyhedron) (a b : Space) :
    (P.developedDistanceValues a b).Finite := Set.finite_range _

end SixVertexUnfolding.ConvexPolyhedron
