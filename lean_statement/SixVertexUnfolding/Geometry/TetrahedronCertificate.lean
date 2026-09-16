import SixVertexUnfolding.Geometry.TetrahedronHinges
import SixVertexUnfolding.Geometry.VertexCertificate
import SixVertexUnfolding.Geometry.VoronoiSeparation

/-!
The tetrahedron flower has one base and three outward petals. Each petal's
source copy is farther from its missing base vertex than the original source.
Those three inequalities give all petal-pair separators.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- The three missing-vertex inequalities certify every pair of tetrahedron petals. -/
theorem tetrahedron_unfolding_of_copies (P : ConvexPolyhedron) (size : P.vertices.card = 4)
    (source : P.Vertex) (copy : P.Vertex → Space →ᵃ[ℝ] Plane)
    (rigid : ∀ v, ∀ x ∈ (P.oppositeFace size v).val, ∀ y ∈ (P.oppositeFace size v).val,
      dist (copy v x) (copy v y) = dist x y)
    (joined : ∀ v x : P.Vertex, x ≠ source → x ≠ v → copy v x = copy source x)
    (base_safe : ∀ v, v ≠ source →
      Disjoint (interior (copy source '' (P.oppositeFace size source).val))
        (interior (copy v '' (P.oppositeFace size v).val)))
    (farther : ∀ v, v ≠ source → dist (v : Space) source < dist (copy source v) (copy v source)) :
    P.HasEdgeUnfolding := by
  let index : P.Vertex ≃ P.Face := Equiv.ofBijective (P.oppositeFace size)
    (P.oppositeFace_bijective size)
  let place (F : P.Face) := copy (index.symm F)
  have place_opposite (v : P.Vertex) : place (P.oppositeFace size v) = copy v := by
    change copy (index.symm (index v)) = copy v
    rw [index.symm_apply_apply]
  obtain ⟨hinges, tree, original, star⟩ := P.exists_tetrahedron_face_star size
    (P.oppositeFace size source)
  refine ⟨{
    place := fun F => place F
    hinges := hinges
    tree := tree
    original_edges := fun _ _ h => original h
    rigid := ?_
    joined := ?_
    nonoverlap := ?_
  }⟩
  · intro F
    obtain ⟨v, rfl⟩ := (P.oppositeFace_bijective size).surjective F
    simpa only [place_opposite] using rigid v
  · intro F G edge
    apply F.joined_of_vertex_agreement G (place F) (place G)
    rintro x ⟨⟨xF, xG⟩, vertex⟩
    let w : P.Vertex := ⟨x, vertex⟩
    obtain ⟨v, rfl⟩ := (P.oppositeFace_bijective size).surjective F
    obtain ⟨u, rfl⟩ := (P.oppositeFace_bijective size).surjective G
    have wv : w ≠ v := (P.vertex_mem_oppositeFace size v w).mp xF
    have wu : w ≠ u := (P.vertex_mem_oppositeFace size u w).mp xG
    rw [place_opposite, place_opposite]
    rcases star _ _ edge with left | right
    · have vs := (P.oppositeFace_bijective size).injective left
      subst v
      exact (joined u w wv wu).symm
    · have us := (P.oppositeFace_bijective size).injective right
      subst u
      exact joined v w wu wv
  · intro F G different
    obtain ⟨v, rfl⟩ := (P.oppositeFace_bijective size).surjective F
    obtain ⟨w, rfl⟩ := (P.oppositeFace_bijective size).surjective G
    have vw : v ≠ w := fun same => different (congrArg (P.oppositeFace size) same)
    rw [place_opposite, place_opposite]
    by_cases vs : v = source
    · subst v
      exact base_safe w vw.symm
    by_cases ws : w = source
    · subst w
      exact (base_safe v vs).symm
    have source_v := (P.vertex_mem_oppositeFace size v source).mpr (Ne.symm vs)
    have source_w := (P.vertex_mem_oppositeFace size w source).mpr (Ne.symm ws)
    have sites_distinct : copy v source ≠ copy w source := by
      intro same
      have v_in_w := (P.vertex_mem_oppositeFace size w v).mpr vw
      have distance := rigid w v v_in_w source source_w
      rw [joined w v vs vw, ← same] at distance
      exact (farther v vs).ne distance.symm
    have nearer (i j : P.Vertex) (is : i ≠ source) (js : j ≠ source)
        (x : Space) (hx : x ∈ (P.oppositeFace size i).val ∩ (P.vertices : Set Space)) :
        dist (copy i x) (copy i source) ≤ dist (copy i x) (copy j source) := by
      let u : P.Vertex := ⟨x, hx.2⟩
      have ui : u ≠ i := (P.vertex_mem_oppositeFace size i u).mp hx.1
      have source_i := (P.vertex_mem_oppositeFace size i source).mpr is.symm
      by_cases us : u = source
      · have equal : x = (source : Space) := congrArg Subtype.val us
        simp [equal]
      have own := rigid i x hx.1 source source_i
      rw [own]
      change dist (u : Space) source ≤ dist (copy i u) (copy j source)
      rw [joined i u us ui]
      by_cases uj : u = j
      · rw [uj]
        exact (farther j js).le
      · have u_in_j := (P.vertex_mem_oppositeFace size j u).mpr uj
        have source_j := (P.vertex_mem_oppositeFace size j source).mpr js.symm
        have other := rigid j u u_in_j source source_j
        rw [joined j u us uj] at other
        exact other.ge
    exact (P.oppositeFace size v).disjoint_of_nearer_sites (P.oppositeFace size w)
      (copy v) (copy w) (copy v source) (copy w source) sites_distinct
      (nearer v w vs ws) (nearer w v ws vs)

end SixVertexUnfolding.ConvexPolyhedron
