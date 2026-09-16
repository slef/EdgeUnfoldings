import SixVertexUnfolding.CanonicalSixFaces

/-! Recover the actual facets from original edge incidence and the convex-facet intersection rule. -/

namespace SixVertexUnfolding.SmallGraphs.SixGraphKind

set_option maxHeartbeats 3000000

/-- Count incidences in any finite subfamily of the candidate facets. -/
theorem candidate_incidence_count (kind : SixGraphKind)
    (actual : Finset (Finset (Fin 6))) (subset : actual ⊆ kind.candidates)
    (condition : Finset (Fin 6) → Prop) [DecidablePred condition] :
    (actual.filter condition).card =
      ∑ face ∈ kind.candidates, if condition face then (if face ∈ actual then 1 else 0) else 0 := by
  have recover : actual = kind.candidates.filter (fun face => face ∈ actual) := by
    ext face
    simp only [Finset.mem_filter]
    exact ⟨fun member => ⟨subset member, member⟩, And.right⟩
  conv_lhs => rw [recover]
  rw [Finset.filter_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro face member
  by_cases first : face ∈ actual <;> by_cases second : condition face <;> simp [first, second]

/-- Edge incidence determines the original facets of the `octahedron` graph. -/
theorem octahedron_facets_determined (actual : Finset (Finset (Fin 6)))
    (subset : actual ⊆ octahedron.candidates)
    (edges : ∀ i j, octahedron.adjacent i j → (actual.filter (fun face => i ∈ face ∧ j ∈ face)).card = 2)
    (nonedges : ∀ i j, i ≠ j → ¬ octahedron.adjacent i j →
      (actual.filter (fun face => i ∈ face ∧ j ∈ face)).card ≤ 1) :
    actual = octahedron.facets := by
  let weight (face : Finset (Fin 6)) : ℕ := if face ∈ actual then 1 else 0
  have count (i j : Fin 6) := candidate_incidence_count octahedron actual subset (fun face => i ∈ face ∧ j ∈ face)
  have e02 : weight {0, 2, 4} + weight {0, 2, 5} + weight {0, 1, 2, 3} = 2 := by
    have equation := (count 0 2).symm.trans (edges 0 2 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e03 : weight {0, 3, 4} + weight {0, 3, 5} + weight {0, 1, 2, 3} = 2 := by
    have equation := (count 0 3).symm.trans (edges 0 3 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e04 : weight {0, 2, 4} + weight {0, 3, 4} + weight {0, 1, 4, 5} = 2 := by
    have equation := (count 0 4).symm.trans (edges 0 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e05 : weight {0, 2, 5} + weight {0, 3, 5} + weight {0, 1, 4, 5} = 2 := by
    have equation := (count 0 5).symm.trans (edges 0 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e12 : weight {1, 2, 4} + weight {1, 2, 5} + weight {0, 1, 2, 3} = 2 := by
    have equation := (count 1 2).symm.trans (edges 1 2 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e13 : weight {1, 3, 4} + weight {1, 3, 5} + weight {0, 1, 2, 3} = 2 := by
    have equation := (count 1 3).symm.trans (edges 1 3 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e14 : weight {1, 2, 4} + weight {1, 3, 4} + weight {0, 1, 4, 5} = 2 := by
    have equation := (count 1 4).symm.trans (edges 1 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e15 : weight {1, 2, 5} + weight {1, 3, 5} + weight {0, 1, 4, 5} = 2 := by
    have equation := (count 1 5).symm.trans (edges 1 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e24 : weight {0, 2, 4} + weight {1, 2, 4} + weight {2, 3, 4, 5} = 2 := by
    have equation := (count 2 4).symm.trans (edges 2 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e25 : weight {0, 2, 5} + weight {1, 2, 5} + weight {2, 3, 4, 5} = 2 := by
    have equation := (count 2 5).symm.trans (edges 2 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e34 : weight {0, 3, 4} + weight {1, 3, 4} + weight {2, 3, 4, 5} = 2 := by
    have equation := (count 3 4).symm.trans (edges 3 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e35 : weight {0, 3, 5} + weight {1, 3, 5} + weight {2, 3, 4, 5} = 2 := by
    have equation := (count 3 5).symm.trans (edges 3 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have n01 : weight {0, 1, 2, 3} + weight {0, 1, 4, 5} ≤ 1 := by
    have inequality := nonedges 0 1 (by decide) (by decide)
    rw [count] at inequality
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using inequality
  have n23 : weight {0, 1, 2, 3} + weight {2, 3, 4, 5} ≤ 1 := by
    have inequality := nonedges 2 3 (by decide) (by decide)
    rw [count] at inequality
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using inequality
  have n45 : weight {0, 1, 4, 5} + weight {2, 3, 4, 5} ≤ 1 := by
    have inequality := nonedges 4 5 (by decide) (by decide)
    rw [count] at inequality
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using inequality
  have bounded (face : Finset (Fin 6)) : weight face ≤ 1 := by
    dsimp [weight]
    split_ifs <;> omega
  have b0 := bounded {0, 2, 4}
  have b1 := bounded {0, 2, 5}
  have b2 := bounded {0, 3, 4}
  have b3 := bounded {0, 3, 5}
  have b4 := bounded {1, 2, 4}
  have b5 := bounded {1, 2, 5}
  have b6 := bounded {1, 3, 4}
  have b7 := bounded {1, 3, 5}
  have b8 := bounded {0, 1, 2, 3}
  have b9 := bounded {0, 1, 4, 5}
  have b10 := bounded {2, 3, 4, 5}
  have values : weight {0, 2, 4} = 1 ∧
      weight {0, 2, 5} = 1 ∧
      weight {0, 3, 4} = 1 ∧
      weight {0, 3, 5} = 1 ∧
      weight {1, 2, 4} = 1 ∧
      weight {1, 2, 5} = 1 ∧
      weight {1, 3, 4} = 1 ∧
      weight {1, 3, 5} = 1 ∧
      weight {0, 1, 2, 3} = 0 ∧
      weight {0, 1, 4, 5} = 0 ∧
      weight {2, 3, 4, 5} = 0 := by omega
  have recover : actual = octahedron.candidates.filter (fun face => weight face = 1) := by
    ext face
    have present : weight face = 1 ↔ face ∈ actual := by simp [weight]
    simp only [Finset.mem_filter, present]
    exact ⟨fun member => ⟨subset member, member⟩, And.right⟩
  rcases values with ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩
  rw [recover]
  simp (disch := decide) [candidates, facets, Finset.filter_insert, Finset.filter_singleton, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]

/-- Edge incidence determines the original facets of the `minusEdge` graph. -/
theorem minusEdge_facets_determined (actual : Finset (Finset (Fin 6)))
    (subset : actual ⊆ minusEdge.candidates)
    (edges : ∀ i j, minusEdge.adjacent i j → (actual.filter (fun face => i ∈ face ∧ j ∈ face)).card = 2) :
    actual = minusEdge.facets := by
  let weight (face : Finset (Fin 6)) : ℕ := if face ∈ actual then 1 else 0
  have count (i j : Fin 6) := candidate_incidence_count minusEdge actual subset (fun face => i ∈ face ∧ j ∈ face)
  have e02 : weight {0, 2, 4} + weight {0, 2, 5} = 2 := by
    have equation := (count 0 2).symm.trans (edges 0 2 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e03 : weight {0, 3, 4} + weight {0, 3, 5} = 2 := by
    have equation := (count 0 3).symm.trans (edges 0 3 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e04 : weight {0, 2, 4} + weight {0, 3, 4} + weight {0, 1, 4, 5} = 2 := by
    have equation := (count 0 4).symm.trans (edges 0 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e05 : weight {0, 2, 5} + weight {0, 3, 5} + weight {0, 1, 4, 5} = 2 := by
    have equation := (count 0 5).symm.trans (edges 0 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e13 : weight {1, 3, 4} + weight {1, 3, 5} = 2 := by
    have equation := (count 1 3).symm.trans (edges 1 3 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e14 : weight {1, 3, 4} + weight {0, 1, 4, 5} + weight {1, 2, 4, 5} = 2 := by
    have equation := (count 1 4).symm.trans (edges 1 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e15 : weight {1, 3, 5} + weight {0, 1, 4, 5} + weight {1, 2, 4, 5} = 2 := by
    have equation := (count 1 5).symm.trans (edges 1 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e24 : weight {0, 2, 4} + weight {1, 2, 4, 5} + weight {2, 3, 4, 5} = 2 := by
    have equation := (count 2 4).symm.trans (edges 2 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e25 : weight {0, 2, 5} + weight {1, 2, 4, 5} + weight {2, 3, 4, 5} = 2 := by
    have equation := (count 2 5).symm.trans (edges 2 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e34 : weight {0, 3, 4} + weight {1, 3, 4} + weight {2, 3, 4, 5} = 2 := by
    have equation := (count 3 4).symm.trans (edges 3 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e35 : weight {0, 3, 5} + weight {1, 3, 5} + weight {2, 3, 4, 5} = 2 := by
    have equation := (count 3 5).symm.trans (edges 3 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have bounded (face : Finset (Fin 6)) : weight face ≤ 1 := by
    dsimp [weight]
    split_ifs <;> omega
  have b0 := bounded {0, 2, 4}
  have b1 := bounded {0, 2, 5}
  have b2 := bounded {0, 3, 4}
  have b3 := bounded {0, 3, 5}
  have b4 := bounded {1, 3, 4}
  have b5 := bounded {1, 3, 5}
  have b6 := bounded {0, 1, 4, 5}
  have b7 := bounded {1, 2, 4, 5}
  have b8 := bounded {2, 3, 4, 5}
  have values : weight {0, 2, 4} = 1 ∧
      weight {0, 2, 5} = 1 ∧
      weight {0, 3, 4} = 1 ∧
      weight {0, 3, 5} = 1 ∧
      weight {1, 3, 4} = 1 ∧
      weight {1, 3, 5} = 1 ∧
      weight {0, 1, 4, 5} = 0 ∧
      weight {1, 2, 4, 5} = 1 ∧
      weight {2, 3, 4, 5} = 0 := by omega
  have recover : actual = minusEdge.candidates.filter (fun face => weight face = 1) := by
    ext face
    have present : weight face = 1 ↔ face ∈ actual := by simp [weight]
    simp only [Finset.mem_filter, present]
    exact ⟨fun member => ⟨subset member, member⟩, And.right⟩
  rcases values with ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8⟩
  rw [recover]
  simp (disch := decide) [candidates, facets, Finset.filter_insert, Finset.filter_singleton, v0, v1, v2, v3, v4, v5, v6, v7, v8]

/-- Edge incidence determines the original facets of the `prismDiagonal` graph. -/
theorem prismDiagonal_facets_determined (actual : Finset (Finset (Fin 6)))
    (subset : actual ⊆ prismDiagonal.candidates)
    (edges : ∀ i j, prismDiagonal.adjacent i j → (actual.filter (fun face => i ∈ face ∧ j ∈ face)).card = 2) :
    actual = prismDiagonal.facets := by
  let weight (face : Finset (Fin 6)) : ℕ := if face ∈ actual then 1 else 0
  have count (i j : Fin 6) := candidate_incidence_count prismDiagonal actual subset (fun face => i ∈ face ∧ j ∈ face)
  have e02 : weight {0, 2, 4} + weight {0, 2, 5} = 2 := by
    have equation := (count 0 2).symm.trans (edges 0 2 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e03 : weight {0, 3, 5} + weight {0, 1, 3, 4} = 2 := by
    have equation := (count 0 3).symm.trans (edges 0 3 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e04 : weight {0, 2, 4} + weight {0, 1, 3, 4} + weight {0, 1, 4, 5} = 2 := by
    have equation := (count 0 4).symm.trans (edges 0 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e05 : weight {0, 2, 5} + weight {0, 3, 5} + weight {0, 1, 4, 5} = 2 := by
    have equation := (count 0 5).symm.trans (edges 0 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e13 : weight {1, 3, 5} + weight {0, 1, 3, 4} = 2 := by
    have equation := (count 1 3).symm.trans (edges 1 3 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e14 : weight {0, 1, 3, 4} + weight {0, 1, 4, 5} + weight {1, 2, 4, 5} = 2 := by
    have equation := (count 1 4).symm.trans (edges 1 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e15 : weight {1, 3, 5} + weight {0, 1, 4, 5} + weight {1, 2, 4, 5} = 2 := by
    have equation := (count 1 5).symm.trans (edges 1 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e24 : weight {0, 2, 4} + weight {1, 2, 4, 5} = 2 := by
    have equation := (count 2 4).symm.trans (edges 2 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e25 : weight {0, 2, 5} + weight {1, 2, 4, 5} = 2 := by
    have equation := (count 2 5).symm.trans (edges 2 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e35 : weight {0, 3, 5} + weight {1, 3, 5} = 2 := by
    have equation := (count 3 5).symm.trans (edges 3 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have bounded (face : Finset (Fin 6)) : weight face ≤ 1 := by
    dsimp [weight]
    split_ifs <;> omega
  have b0 := bounded {0, 2, 4}
  have b1 := bounded {0, 2, 5}
  have b2 := bounded {0, 3, 5}
  have b3 := bounded {1, 3, 5}
  have b4 := bounded {0, 1, 3, 4}
  have b5 := bounded {0, 1, 4, 5}
  have b6 := bounded {1, 2, 4, 5}
  have values : weight {0, 2, 4} = 1 ∧
      weight {0, 2, 5} = 1 ∧
      weight {0, 3, 5} = 1 ∧
      weight {1, 3, 5} = 1 ∧
      weight {0, 1, 3, 4} = 1 ∧
      weight {0, 1, 4, 5} = 0 ∧
      weight {1, 2, 4, 5} = 1 := by omega
  have recover : actual = prismDiagonal.candidates.filter (fun face => weight face = 1) := by
    ext face
    have present : weight face = 1 ↔ face ∈ actual := by simp [weight]
    simp only [Finset.mem_filter, present]
    exact ⟨fun member => ⟨subset member, member⟩, And.right⟩
  rcases values with ⟨v0, v1, v2, v3, v4, v5, v6⟩
  rw [recover]
  simp (disch := decide) [candidates, facets, Finset.filter_insert, Finset.filter_singleton, v0, v1, v2, v3, v4, v5, v6]

/-- Edge incidence determines the original facets of the `prism` graph. -/
theorem prism_facets_determined (actual : Finset (Finset (Fin 6)))
    (subset : actual ⊆ prism.candidates)
    (edges : ∀ i j, prism.adjacent i j → (actual.filter (fun face => i ∈ face ∧ j ∈ face)).card = 2) :
    actual = prism.facets := by
  let weight (face : Finset (Fin 6)) : ℕ := if face ∈ actual then 1 else 0
  have count (i j : Fin 6) := candidate_incidence_count prism actual subset (fun face => i ∈ face ∧ j ∈ face)
  have e02 : weight {0, 2, 4} + weight {0, 2, 3, 5} = 2 := by
    have equation := (count 0 2).symm.trans (edges 0 2 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e03 : weight {0, 1, 3, 4} + weight {0, 2, 3, 5} = 2 := by
    have equation := (count 0 3).symm.trans (edges 0 3 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e04 : weight {0, 2, 4} + weight {0, 1, 3, 4} = 2 := by
    have equation := (count 0 4).symm.trans (edges 0 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e13 : weight {1, 3, 5} + weight {0, 1, 3, 4} = 2 := by
    have equation := (count 1 3).symm.trans (edges 1 3 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e14 : weight {0, 1, 3, 4} + weight {1, 2, 4, 5} = 2 := by
    have equation := (count 1 4).symm.trans (edges 1 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e15 : weight {1, 3, 5} + weight {1, 2, 4, 5} = 2 := by
    have equation := (count 1 5).symm.trans (edges 1 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e24 : weight {0, 2, 4} + weight {1, 2, 4, 5} = 2 := by
    have equation := (count 2 4).symm.trans (edges 2 4 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e25 : weight {0, 2, 3, 5} + weight {1, 2, 4, 5} = 2 := by
    have equation := (count 2 5).symm.trans (edges 2 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have e35 : weight {1, 3, 5} + weight {0, 2, 3, 5} = 2 := by
    have equation := (count 3 5).symm.trans (edges 3 5 (by decide))
    simpa (disch := decide) [candidates, weight, add_assoc, add_comm, add_left_comm] using equation
  have bounded (face : Finset (Fin 6)) : weight face ≤ 1 := by
    dsimp [weight]
    split_ifs <;> omega
  have b0 := bounded {0, 2, 4}
  have b1 := bounded {1, 3, 5}
  have b2 := bounded {0, 1, 3, 4}
  have b3 := bounded {0, 2, 3, 5}
  have b4 := bounded {1, 2, 4, 5}
  have values : weight {0, 2, 4} = 1 ∧
      weight {1, 3, 5} = 1 ∧
      weight {0, 1, 3, 4} = 1 ∧
      weight {0, 2, 3, 5} = 1 ∧
      weight {1, 2, 4, 5} = 1 := by omega
  have recover : actual = prism.candidates.filter (fun face => weight face = 1) := by
    ext face
    have present : weight face = 1 ↔ face ∈ actual := by simp [weight]
    simp only [Finset.mem_filter, present]
    exact ⟨fun member => ⟨subset member, member⟩, And.right⟩
  rcases values with ⟨v0, v1, v2, v3, v4⟩
  rw [recover]
  simp (disch := decide) [candidates, facets, Finset.filter_insert, Finset.filter_singleton, v0, v1, v2, v3, v4]

/-- The same short incidence criterion works uniformly for all four canonical graphs. -/
theorem facets_determined (kind : SixGraphKind) (actual : Finset (Finset (Fin 6)))
    (subset : actual ⊆ kind.candidates)
    (edges : ∀ i j, kind.adjacent i j → (actual.filter (fun face => i ∈ face ∧ j ∈ face)).card = 2)
    (nonedges : ∀ i j, i ≠ j → ¬ kind.adjacent i j →
      (actual.filter (fun face => i ∈ face ∧ j ∈ face)).card ≤ 1) : actual = kind.facets := by
  cases kind
  exacts [octahedron_facets_determined actual subset edges nonedges,
    minusEdge_facets_determined actual subset edges,
    prismDiagonal_facets_determined actual subset edges,
    prism_facets_determined actual subset edges]

end SixVertexUnfolding.SmallGraphs.SixGraphKind
