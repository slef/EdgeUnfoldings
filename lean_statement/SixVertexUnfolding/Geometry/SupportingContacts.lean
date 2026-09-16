import SixVertexUnfolding.Geometry.Boundary
import SixVertexUnfolding.Geometry.SupportTilt

/-! Supporting contact sets before they have been enlarged to full facets. -/

namespace SixVertexUnfolding.ConvexPolyhedron

def SupportsAt (P : ConvexPolyhedron) (n x : Space) : Prop :=
  ∀ y ∈ P.body, inner ℝ n y ≤ inner ℝ n x

def contactSet (P : ConvexPolyhedron) (n x : Space) : Set Space :=
  {y ∈ P.body | inner ℝ n y = inner ℝ n x}

noncomputable def contactVertices (P : ConvexPolyhedron) (n x : Space) : Finset Space := by
  classical
  exact P.vertices.filter (fun y => inner ℝ n y = inner ℝ n x)

variable (P : ConvexPolyhedron) (n x : Space)

theorem coe_contactVertices :
    (P.contactVertices n x : Set Space) = P.contactSet n x ∩ (P.vertices : Set Space) := by
  ext y
  simp only [contactVertices, Finset.mem_coe, Finset.mem_filter, contactSet,
    Set.mem_inter_iff, Set.mem_setOf_eq]
  exact ⟨fun h => ⟨⟨P.vertices_subset_body h.1, h.2⟩, h.1⟩,
    fun h => ⟨h.2, h.1.2⟩⟩

theorem contactVertices_subset : P.contactVertices n x ⊆ P.vertices :=
  Finset.filter_subset _ _

theorem contactSet_isExposed (support : P.SupportsAt n x) (point : x ∈ P.body) :
    IsExposed ℝ P.body (P.contactSet n x) := by
  intro _
  refine ⟨innerSL ℝ n, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, equal_height⟩
    exact ⟨hy, fun z hz => by simpa [equal_height] using support z hz⟩
  · rintro ⟨hy, maximal⟩
    exact ⟨hy, le_antisymm (support y hy) (maximal x point)⟩

theorem contactSet_convex : Convex ℝ (P.contactSet n x) :=
  P.body_convex.inter (convex_hyperplane
    ⟨fun a b => inner_add_right n a b, fun a b => inner_smul_right n b a⟩ (inner ℝ n x))

/-- All contact points, including the chosen boundary point, come from the active original vertices. -/
theorem contactSet_eq_convexHull (support : P.SupportsAt n x) (point : x ∈ P.body) :
    P.contactSet n x = convexHull ℝ (P.contactVertices n x : Set Space) := by
  have exposed := P.contactSet_isExposed n x support point
  have extreme_eq := exposed.isExtreme.extremePoints_eq
  rw [P.body_extreme_points, ← P.coe_contactVertices] at extreme_eq
  have finite_extreme : ((P.contactSet n x).extremePoints ℝ).Finite := by
    rw [extreme_eq]
    exact (P.contactVertices n x).finite_toSet
  have hull_eq := closure_convexHull_extremePoints (exposed.isCompact P.body_compact)
    (P.contactSet_convex n x)
  rw [(finite_extreme.isClosed_convexHull ℝ).closure_eq, extreme_eq] at hull_eq
  exact hull_eq.symm

theorem point_mem_contact_hull (support : P.SupportsAt n x) (point : x ∈ P.body) :
    x ∈ convexHull ℝ (P.contactVertices n x : Set Space) := by
  rw [← P.contactSet_eq_convexHull n x support point]
  exact ⟨point, rfl⟩

/-- A nonzero height functional cannot be constant on every original vertex. -/
theorem exists_vertex_height_ne (nonzero : n ≠ 0) :
    ∃ v ∈ P.vertices, inner ℝ n v ≠ inner ℝ n x := by
  by_contra all_equal
  push Not at all_equal
  have agree : Set.EqOn (innerSL ℝ n).toLinearMap.toAffineMap
      (AffineMap.const ℝ Space (inner ℝ n x)) (P.vertices : Set Space) := all_equal
  have everywhere := AffineMap.eqOn_affineSpan agree
  rw [P.vertices_span_space] at everywhere
  have at_zero := everywhere (AffineSubspace.mem_top ℝ Space (0 : Space))
  have at_normal := everywhere (AffineSubspace.mem_top ℝ Space n)
  change inner ℝ n 0 = inner ℝ n x at at_zero
  change inner ℝ n n = inner ℝ n x at at_normal
  have norm_zero : inner ℝ n n = 0 := by simpa using at_normal.trans at_zero.symm
  exact nonzero (inner_self_eq_zero.mp norm_zero)

theorem supportsAt_of_vertex_bounds
    (bound : ∀ v ∈ P.vertices, inner ℝ n v ≤ inner ℝ n x) : P.SupportsAt n x := by
  exact convexHull_min bound (convex_halfSpace_le
    ⟨fun a b => inner_add_right n a b, fun a b => inner_smul_right n b a⟩ (inner ℝ n x))

theorem contact_normal_orthogonal :
    n ∈ (vectorSpan ℝ (P.contactVertices n x : Set Space))ᗮ := by
  have agree : Set.EqOn (innerSL ℝ n).toLinearMap.toAffineMap
      (AffineMap.const ℝ Space (inner ℝ n x)) (P.contactVertices n x : Set Space) := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro v hv
  simpa using AffineMap.linear_eqOn_vectorSpan agree hv

/-- A nonzero supporting normal leaves at most two dimensions of contact. -/
theorem contact_dimension_le_two (normal_nonzero : n ≠ 0) :
    affineDimension (P.contactVertices n x : Set Space) ≤ 2 := by
  let D := vectorSpan ℝ (P.contactVertices n x : Set Space)
  have normal_span : Submodule.span ℝ {n} ≤ Dᗮ := by
    apply Submodule.span_le.mpr
    intro v hv
    rw [Set.mem_singleton_iff.mp hv]
    exact P.contact_normal_orthogonal n x
  have lower := Submodule.finrank_mono normal_span
  rw [finrank_span_singleton normal_nonzero] at lower
  have dimensions := D.finrank_add_finrank_orthogonal
  have ambient : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [ambient] at dimensions
  rw [affineDimension, direction_affineSpan]
  change Module.finrank ℝ D ≤ 2
  omega

/-- A direction orthogonal to the contact span fixes the height of every contact vertex. -/
theorem tilt_fixes_contacts (support : P.SupportsAt n x) (point : x ∈ P.body)
    {q : Space} (orthogonal : q ∈ (vectorSpan ℝ (P.contactVertices n x : Set Space))ᗮ)
    {v : Space} (contact : v ∈ P.contactVertices n x) :
    inner ℝ q v = inner ℝ q x := by
  have point_span := convexHull_subset_affineSpan (𝕜 := ℝ) _
    (P.point_mem_contact_hull n x support point)
  have vertex_span := subset_affineSpan ℝ _ contact
  have difference := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
    vertex_span point_span
  have zero := (Submodule.mem_orthogonal' _ _).mp orthogonal _ difference
  simpa only [vsub_eq_sub, inner_sub_right, sub_eq_zero] using zero

end SixVertexUnfolding.ConvexPolyhedron
