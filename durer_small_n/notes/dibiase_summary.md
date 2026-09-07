# DiBiase, *Polytope Unfolding*, Smith College honors thesis, 15 April 1990 (adviser J. O'Rourke)

Read in full on 2026-09-08 (115 pages, scanned, no text layer). Only Chapter 3 (pp. 38–84) concerns the
n ≤ 7 problem. Chapter 2 is statistics on Hamiltonian unfoldings, Chapter 4 on star unfoldings
(conjectured non-overlapping; AAOS90 cited as working on the proof).

## Scope: simplicial polytopes only
"Fact 3: every face in the polytope and unfolded polygon is a triangle (by assumption)." Types are the
Bowen–Fisk triangulations of the sphere: 1 (n=4), 1 (n=5), 2 (n=6), 5 (n=7), 14, 50, 233, 1249, 7595 (n=12).
So the thesis proves nothing about the non-simplicial 6-vertex types (prism, pentagonal pyramid,
octahedron-minus-an-edge, prism-with-one-diagonal, ...). Our handoff's belief that DiBiase did a direct
chart for a non-simplicial type is wrong: the reductions in HANDOFF.md ("Reduction of n=6") are needed.
The two simplicial 6-types are G_a(6) (degrees 5,5,4,4,3,3) and G_b(6) (octahedron, all degree 4).

## Definitions and facts used
* Overlap = two faces intersect other than at edges/vertices (touching allowed) — same as ours.
* Fact 1: angle deficit 0 < κ < 2π at every vertex. Fact 2: a cut edge has two images of equal length.
* Nearness ν of a face = distance in the dual tree from the root face Δ (the "bottom" face, drawn as the
  outer face of the planar map, left interior in the unfolding and therefore never involved in overlap
  except together with another face). "Nearness principle": unfold so that ν is as small as possible
  (minimum-radius dual tree; "open like the petals of a flower"). All her trees are rooted at Δ.
* Notation ⁺BE / ⁻BE: B moves counter-clockwise / clockwise toward E.
* "Worst-case" maps: faces elongated ("pulled") until an angle deficit hits 0; her proofs argue that
  overlap needs a deficit ≤ 0 or a face that is no longer a triangle.

## The lemmas (numbering as in the thesis)
1. (3.1) Two edges incident to the same vertex of the net that are images of the same polytope edge cannot
   overlap; more generally faces sharing a net vertex do not overlap (the gap between them is the deficit).
   = our shared-vertex lemma. Rigorous.
2. (3.2) A face R of ν=1 and a face T of ν=2, separated by one or more faces (of ν=1 or 2), cannot overlap.
   Proof uses Fact 2: the two images x, y of the cut vertex z give a line L1 = xy; T is confined to one side
   of a line L2 (it must stay a triangle); "as Ω → π, L1 → L2; Ω < π so L1 never reaches L2". A sketch;
   the geometric claim is essentially our "cut-edge line" confinement plus a one-parameter picture.
3. (3.3) Two faces R, T of ν=2 separated by a face S of ν=2 cannot overlap, under the extra conditions that
   S and T share a vertex with Δ and R, T are separated by at least one face. Proof by edge–edge cases
   (e1..e4) using half-planes l_R, l_T, l_S beyond which a face would stop being a triangle. Rigorous in
   spirit; case 4 relies on "x is below l_S" from a figure. She notes it "is impossible to generalize".
4. (3.4) Two faces T, U of ν=2 separated by no face of ν=2 (the ⁻TU case in U_a(6): D and E around the apex
   of Δ) cannot overlap. "Perhaps the most complicated proof in the thesis": the cut vertex y has images
   y1, y2 (apexes of T and U); if both y1, y2 were inside their lines L1, L2 the exterior angles β1, β2 at
   y would sum to > 2π (Fact 1); otherwise an angle comparison θ2 < θ* < θ1 with θ* "clearly from Figure
   3.23f". This is the ancestor of our v-fan argument (angle sum at the cut vertex), but the second half is
   a figure-based sketch, not a proof.
5. (3.5) "Safe spot": if two faces of ν=2 separated by 0 faces (⁺BE in U_a(6)) would overlap, one of them
   can be re-attached elsewhere (E moved to G) where overlap is impossible. Proof is one sentence
   ("BE overlap cannot occur if the longest edge of E matches C; if not, moving E to G makes overlap
   impossible"). Not a proof.
6. (3.6) For G_b(6) (octahedron): if the ν=3 face G intersects a ν=2 face as in Fig. 3.28, G can be moved
   to a safe place. Proof by the angles α4, α5, α6 of the face at the three vertices 4,5,6 (needs α4 > π/2
   for the intersection, then re-attaching to E needs α5 > π/2, "but this is not the case"). Specific to
   the figure; "since G_b(6) is totally symmetric without face G, this lemma could be generalized".
7. (3.7) Hexstar polytopes (an infinite class extending U_a(7)) never overlap — stated, proof "realized by
   breaking the unfolding into regions and using the convex curve theorem"; Conjecture 3 says the formal
   proof is in progress.

## Charts
For each type: the planar map G(n), the unfolding map U(n) (dual tree rooted at Δ), and a face-pair chart
listing every pair of the 7 non-root faces (21 entries for n=6) with the lemma that excludes overlap.
* U_a(6): Δ with A (ν=1, bottom), B, C (ν=1); D on B, E on C (ν=2); F, G on A (ν=2). Chart (Fig. 3.25):
  Lemma 1 ×11, Lemma 2 ×6, Lemma 3 ×2 (DG, EF), Lemma 4 ×1 (DE), Lemma 2,5 ×2 (BE, CD).
* U_b(6) (octahedron): Δ (outer triangle 1-2-3 of the map), A, B, C on the three edges of Δ (ν=1),
  D on A, E on B, F on C (ν=2), G (the inner triangle 4-5-6, opposite to Δ) on D (ν=3). Dual tree: a
  spider centred at Δ with legs Δ-A-D-G, Δ-B-E, Δ-C-F (degrees 3,2,2,2,2,1,1,1). Chart (Fig. 3.29):
  Lemma 1 ×11, Lemma 2 ×4 (AE, BF, CD, DF), Lemma 2,5 ×2 (DE, EF), Lemma 6 ×4 (BG, CG, EG, FG).
  So all four far pairs involving G rest on the "safe spot" Lemma 6, and two more on Lemma 5.
Her Theorem 3.5.1 (∀ G_a(6), G_b(6) ∃ non-overlapping unfolding) is therefore an existence statement with
a shape-dependent choice of tree — consistent with our finding that no fixed labelled tree works for the
octahedron. It is not a rigorous proof by today's standards (Lemmas 4, 5, 6).

## n = 7
Five simplicial types with degree ids 6554433, 6644433, 6555333, 5554444, 5554443 (Fig. 3.30), unfolding
maps drawn by the nearness principle (Fig. 3.31): (a) all faces ν ≤ 2; (b), (c) one face of ν=3; (d), (e)
two faces of ν=3. No proofs ("far beyond the time scope"). Our handoff counts 34 types for n=7 including
non-simplicial ones.

## Relation to our work (2026-09-08)
* Our Lemma A (vertex adjacent to all others) has no counterpart; she uses Δ-rooted spider trees instead.
  For G_a(6) her tree is essentially the star of a degree-5 vertex? No: Δ is a face, not a vertex; the
  tree cuts are not a vertex star. The two approaches are different.
* Her Lemma 3 half-plane confinement = our D-lemma (cut-edge lines); her Lemma 4 angle-sum at the cut
  vertex = our v-fan / c*-rotation argument, made exact.
* Her Lemmas 5–6 (move a face when it overlaps) = our choice of apex v and slit k by curvature.
* Adopt her chart format for the write-up: per type, the planar map, the unfolding map with the rooted
  tree, and the 21-entry pair chart citing lemmas; add the hypothesis (which tree is used when).
