import SixVertexUnfolding.Geometry.TrianglePetal
import SixVertexUnfolding.Geometry.VoronoiSeparation

/-!
An outward petal is one original face attached to a fixed base placement.
Two such petals are separated by the bisector between their apex copies.
-/

namespace SixVertexUnfolding

/-- The geometric facts needed for one outward face in a flower-shaped development. -/
structure PetalPlacement {P : ConvexPolyhedron} (base side : P.Face)
    (apex : P.Vertex) (left : Space →ᵃ[ℝ] Plane) where
  place : Space →ᵃ[ℝ] Plane
  rigid : ∀ x ∈ side.val, ∀ y ∈ side.val, dist (place x) (place y) = dist x y
  apex_in : (apex : Space) ∈ side.val
  other_vertices_in_base : ∀ x : P.Vertex, (x : Space) ∈ side.val → x ≠ apex → (x : Space) ∈ base.val
  joined : ∀ x : P.Vertex, (x : Space) ∈ side.val → (x : Space) ∈ base.val → place x = left x
  base_safe : Disjoint (interior (left '' base.val)) (interior (place '' side.val))
  farther : ∀ x : P.Vertex, (x : Space) ∈ base.val → (x : Space) ∉ side.val →
    dist (x : Space) apex < dist (left x) (place apex)

namespace PetalPlacement

variable {P : ConvexPolyhedron} {base F G : P.Face} {apex : P.Vertex} {left : Space →ᵃ[ℝ] Plane}

/-- Different original petals in the same flower have disjoint planar interiors. -/
theorem disjoint (first : PetalPlacement base F apex left) (second : PetalPlacement base G apex left)
    (different : F ≠ G) :
    Disjoint (interior (first.place '' F.val)) (interior (second.place '' G.val)) := by
  have missing : ∃ x : P.Vertex, (x : Space) ∈ F.val ∧ (x : Space) ∉ G.val := by
    by_contra none
    push Not at none
    apply different
    apply F.eq_of_subset G
    rw [F.eq_convexHull_vertices]
    apply convexHull_min _ G.convex
    rintro x ⟨xF, vertex⟩
    exact none ⟨x, vertex⟩ xF
  obtain ⟨v, vF, vG⟩ := missing
  have v_base := first.other_vertices_in_base v vF (fun same => vG (same ▸ second.apex_in))
  have sites_distinct : first.place apex ≠ second.place apex := by
    intro same
    have distance := first.rigid v vF apex first.apex_in
    rw [first.joined v vF v_base, same] at distance
    exact (second.farther v v_base vG).ne distance.symm
  have nearer {I J : P.Face} (own : PetalPlacement base I apex left) (other : PetalPlacement base J apex left)
      (x : Space) (hx : x ∈ I.val ∩ (P.vertices : Set Space)) :
      dist (own.place x) (own.place apex) ≤ dist (own.place x) (other.place apex) := by
    let v : P.Vertex := ⟨x, hx.2⟩
    by_cases at_apex : v = apex
    · have equal : x = (apex : Space) := congrArg Subtype.val at_apex
      simp [equal]
    have v_base := own.other_vertices_in_base v hx.1 at_apex
    rw [own.rigid x hx.1 apex own.apex_in]
    change dist (v : Space) apex ≤ dist (own.place v) (other.place apex)
    rw [own.joined v hx.1 v_base]
    by_cases vJ : (v : Space) ∈ J.val
    · have distance := other.rigid v vJ apex other.apex_in
      rw [other.joined v vJ v_base] at distance
      exact distance.ge
    · exact (other.farther v v_base vJ).le
  exact F.disjoint_of_nearer_sites G first.place second.place (first.place apex) (second.place apex)
    sites_distinct (nearer first second) (nearer second first)

end PetalPlacement

namespace ConvexPolyhedron.Face

/-- Construct a certified outward petal whenever its two nonapex vertices lie on the base. -/
theorem exists_petal_placement {P : ConvexPolyhedron} (base side : P.Face)
    (a b apex : P.Vertex) (ab : a ≠ b)
    (aB : (a : Space) ∈ base.val) (bB : (b : Space) ∈ base.val)
    (vertices : side.val ∩ (P.vertices : Set Space) = {(a : Space), (b : Space), (apex : Space)})
    (apex_outside : (apex : Space) ∉ base.val)
    (left : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ base.val, ∀ y ∈ base.val, dist (left x) (left y) = dist x y) :
    Nonempty (PetalPlacement base side apex left) := by
  obtain ⟨right, rigid, joined, safe, farther⟩ :=
    base.exists_triangle_petal side a b apex ab aB bB vertices apex_outside left left_rigid
  refine ⟨{
    place := right
    rigid := rigid
    apex_in := ?_
    other_vertices_in_base := ?_
    joined := joined
    base_safe := safe
    farther := farther
  }⟩
  · have member : (apex : Space) ∈ side.val ∩ (P.vertices : Set Space) := by rw [vertices]; simp
    exact member.1
  · intro x xS different
    have member : (x : Space) ∈ ({(a : Space), (b : Space), (apex : Space)} : Set Space) :=
      vertices ▸ ⟨xS, x.property⟩
    rcases member with equal | equal | equal
    · exact equal ▸ aB
    · exact equal ▸ bB
    · exact False.elim (different (Subtype.ext equal))

end ConvexPolyhedron.Face
end SixVertexUnfolding
