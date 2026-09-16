import SixVertexUnfolding.Geometry.BipyramidMetric

/-! All four source petals lie in their own source-copy Voronoi regions. -/

namespace SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices.Development

variable {P : ConvexPolyhedron} {B : P.BipyramidVertices}
    {triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3}
    {source : Fin 3} (net : B.Development triangles source)

/-- At every petal vertex, its own source copy is at least as near as an opposite-cap copy. -/
theorem petal_nearer_opposite (size : P.vertices.card = 5) (upper : Bool) (i j : Fin 3)
    (first_petal : i ≠ source) (second_petal : j ≠ source)
    (v : P.Vertex) (vF : (v : Space) ∈ (B.face triangles upper i).val) :
    dist ((net.cap upper).place i v) ((net.cap upper).place i (B.equatorVertex source)) ≤
      dist ((net.cap upper).place i v) ((net.cap (!upper)).place j (B.equatorVertex source)) := by
  have source_in := (B.equator_mem_face triangles upper i source).mpr first_petal.symm
  rw [(net.cap upper).rigid i v vF (B.equatorVertex source) source_in]
  rcases B.vertex_cases_from_pole upper v with at_pole | at_opposite | ⟨k, at_equator⟩
  · rw [at_pole, net.petal_pole_agreement]
    have farther := net.opposite_pole_farther size (!upper) j second_petal
    cases upper <;> simpa using farther.le
  · have bad : (B.poleVertex (!upper) : Space) ∈ (B.face triangles upper i).val :=
      at_opposite ▸ vF
    exact False.elim (B.opposite_pole_not_mem_face triangles upper i bad)
  · rw [at_equator]
    by_cases at_source : k = source
    · subst k
      simp
    have k_in := (B.equator_mem_face triangles upper i k).mp (at_equator ▸ vF)
    rw [net.petal_equator_agreement upper i k k_in at_source,
      net.base_equator_agreement upper k at_source]
    by_cases missing : k = j
    · subst k
      exact ((net.cap (!upper)).farther j second_petal (B.equatorVertex j)
        ((B.equator_mem_face triangles (!upper) source j).mpr second_petal)
        (fun member => (B.equator_mem_face triangles (!upper) j j).mp member rfl)).le
    · have rigid := (net.cap (!upper)).rigid j (B.equatorVertex k)
        ((B.equator_mem_face triangles (!upper) j k).mpr missing) (B.equatorVertex source)
        ((B.equator_mem_face triangles (!upper) j source).mpr second_petal.symm)
      rw [net.petal_equator_agreement (!upper) j k missing at_source] at rigid
      exact rigid.ge

/-- Every upper source petal is disjoint from every lower source petal. -/
theorem cross_petals_disjoint (size : P.vertices.card = 5) (i j : Fin 3)
    (upper_petal : i ≠ source) (lower_petal : j ≠ source) :
    Disjoint (interior ((net.cap true).place i '' (B.face triangles true i).val))
      (interior ((net.cap false).place j '' (B.face triangles false j).val)) := by
  have different : (net.cap true).place i (B.equatorVertex source) ≠
      (net.cap false).place j (B.equatorVertex source) := by
    intro same
    have rigid := (net.cap true).rigid i B.top (B.pole_mem_face triangles true i)
      (B.equatorVertex source) ((B.equator_mem_face triangles true i source).mpr upper_petal.symm)
    have pole_agree : (net.cap true).place i B.top = (net.cap true).place source B.top :=
      net.petal_pole_agreement true i
    rw [pole_agree, same] at rigid
    exact (net.opposite_pole_farther size false j lower_petal).ne rigid.symm
  apply (B.face triangles true i).disjoint_of_nearer_sites (B.face triangles false j)
    ((net.cap true).place i) ((net.cap false).place j)
    ((net.cap true).place i (B.equatorVertex source))
    ((net.cap false).place j (B.equatorVertex source)) different
  · rintro x ⟨xF, vertex⟩
    exact net.petal_nearer_opposite size true i j upper_petal lower_petal ⟨x, vertex⟩ xF
  · rintro x ⟨xF, vertex⟩
    exact net.petal_nearer_opposite size false j i lower_petal upper_petal ⟨x, vertex⟩ xF

end SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices.Development
