# Dürer's problem for n ≤ 7 vertices — proof state and work plan

## Current update: complete selected octahedron proof, 11 September 2026

[The equal-length proof](n6/LEMMA_F_CHORD.md) completes the low-curvature
branch. Together with the high-curvature pole-angle argument and the recorded
dependency audit, this gives a complete written proof for the H/R selected
tree on every convex octahedron. All 28 pairs and all five patch regimes are
covered, including equality and ties. Independent mathematical review is
still needed. The every-slit Lemma F and the two nonsimplicial six-vertex types
remain open; the full n=6 theorem is not claimed.

See [n6/CONTINUATION.md](n6/CONTINUATION.md) for the current proof and
next research. All earlier counts below are historical. In particular the
old 2-excluded/47-open report is unchanged as a record; the new theorem
excludes all 49 simultaneous-failure classes at once. The false older
unrestricted fan-to-petal reduction remains false and is not used.


## Previous proof state: 11 September 2026 JST, codex/minus-edge-patterns

**The full n=6 case remains unproved. Read [n6/REVIEW.md](n6/REVIEW.md)
before relying on the historical proof status below.**

- **Latest result, 11 September:** [Lemma L is proved](n6/LEMMA_L_PROOF.md): all three local pairs, in every curvature branch, under the stated selections. The proof combines a cut-edge separator with spherical-link and pole-triangle bounds. The current count is 3/3 local obligations and 22/28 selected-net pairs. Lemma F, the complete octahedron, and n=6 remain open. The old four-opening 2/47 class record is unrecounted and separate; do not reuse the slit ranking after changing openings.
- **Previous result:** [Lemma L's curvature gate](n6/LEMMA_L_CURVATURE_GATE.md) separates the two local angular-overlap routes at sigma=kappa_slit+kappa_w=pi. All three local pairs are proved safe at equality and in explicit corner subfamilies. Below pi, a remaining overlap must involve the unique petal inward at the slit; only two local pairs then need work. A separate exact 18-coordinate radial family has a 6/5 clearance ratio and all-pairs certificates. General L remains open (0/3 universal obligations); patch-regime and fixed-source counts are unchanged.
- **Previous result:** [the middle-patch switch](n6/OCTA_THREE_CHAIN.md) proves explicit common-direction three-patch subfamilies under H using four prescribed trees. A simple excess threshold and a stronger two-view condition have written proofs, point certificates, and an 18-coordinate region. Two branches outside the stronger hypotheses remain open; one has an exact example. Four of five entire patch regimes and the 2-excluded/47-open fixed-source count are unchanged.
- **Previous result:** [the shared patch-angle budget](n6/OCTA_PATCH_BUDGET.md) proves all cases with at most two bad patches, plus three with mixed directions, when a pole is globally sharpest. The four-cut source may change. **Only three bad patches with a common cyclic direction remain open in this patch approach.** The 49-class fixed-source count stays 2 excluded and 47 open. The overview now shows 4 of 5 coarse existence regimes proved, with the fifth partly settled; this is not a coverage percentage.
- **Previous proof:** [one nonconvex patch under H](n6/OCTA_ONE_PATCH.md) now has a complete existence proof using two prescribed trees, one at each pole. If both cone tests failed, an equator vertex would be sharper than both poles. The fixed sharpest-source rule remains open. [The half-fan proof](n6/OCTA_HALF_FAN.md) additionally handles all three adjacent-two-patch directions when either pole has curvature at least 180 degrees. Neither changes the 2-excluded/47-open fixed-source count.
- **Earlier correction:** [the hinge audit](n6/HINGE_AUDIT.md) refutes the old
  conditional far-fan reduction with an exact convex counterexample. Its
  source is not sharpest. Restore **49 original classes, 2 excluded and 47
  open**; the 24-class reduction and the one-nonconvex-patch whole-net proof
  are withdrawn pending an H-specific repair. All-convex patches and the
  two switching implications remain proved.
- New independent complete families: the [curvature-pair theorem](n6/OCTA_TWO_SHARP_POLES.md)
  proves a net when sharper pole curvature K and opposite curvature J satisfy
  K+2J>=2*pi; **every centrally symmetric octahedron follows**. The
  [local radial-cover theorem](n6/OCTA_RADIAL_COVER.md) extends the short-edge
  test with a face-angle test and certifies further asymmetric families.
  None of these independent results uses the refuted reduction.
- Latest proof step: [n6/MINUS_NEIGHBORHOOD.md](n6/MINUS_NEIGHBORHOOD.md)
  applies Pinciu’s Theorem 1, excluding seven of the original 28 minus-edge
  failure classes globally. Twenty-one classes remain open.
- Earlier minus-edge pattern work: [n6/MINUS_PAIR.md](n6/MINUS_PAIR.md) gives a
  two-tree conjecture and a two-fan proof target. A new exact cover uses one
  of those trees on the entire existing ±0.05 box, with 16 cells instead of
  409. This initially left all 28 simultaneous-failure classes open.
- The unqualified double-outward D-lemma is false. An integer-coordinate
  counterexample is verified by rational intervals. The working notes now
  restrict it to an angle range automatic in Case A. The new base-cone proof
  handles the complementary large-angle partition: under (H), only Sigma_W<pi
  remains. See [n6/CASE_PARTITION.md](n6/CASE_PARTITION.md).
- Interior-hinge noncrossing uses local nonoverlap. The further far-fan
  reduction is false as stated, even with those local pairs clear.
  Nonsimplicial limit reductions additionally need successful trees that never
  cut the introduced diagonals. These conditions were missing from earlier summaries.
- Corrected the far-vertex angle index in `adv_angle.py` and rejected Qhull's
  triangulated flat quadrilaterals in `octa_structure`. Historical mode-i angle
  searches are not evidence for the intended angle and have not all been rerun.
- Integrated both attached Codex archives once in `n6/`. Their 24-tree family
  duplicates the existing Z_k family; their exact formulation and sector probe
  are complementary tools, not completed proofs.
- A new replayable certificate proves nonoverlap throughout one explicit
  18-coordinate octahedron box of half-width 1/1000. It does not cover all octahedra.
- The reduced 24-tree SMT query has 120 shared paths and returns unknown/timeout.
  Neither random searches nor solver timeouts certify the universal theorem.
- The direct thesis review now has an exact counterexample to the fixed DF chart
  entry; see [n6/THESIS_AUDIT.md](n6/THESIS_AUDIT.md). The useful leaf-reattachment
  strategy is represented by 48 distinct three-arm trees.
- New original-facet certificates cover nine-parameter prism and ten-parameter
  octahedron-minus-edge regions. Lemma L and universal region coverage remain
  open. [n6/LEMMA_L.md](n6/LEMMA_L.md) records an exact bisector-shortcut failure
  and the nonoverlapping resolution of a thin numerical candidate.
- Morning verification: the larger prism box has a complete independently
  replayed cover of 443 leaves using three trees. Wider prism and minus-edge
  searches ended with 94 and 11 unresolved leaves, respectively. All 53 tests
  pass; no universal solver query succeeded. See [n6/REGION_COVER.md](n6/REGION_COVER.md).

Reproduction and exact scopes: [n6/README.md](n6/README.md).
The account below preserves Claude's prior work and chronology; where it says
“proved” without these qualifications, this audit and the corrected notes take precedence.

---

Owner: Stefan Langerman. Goal: a human-readable proof that every convex polytope with ≤ 6 vertices
(then 7) has a non-overlapping edge unfolding, reconstructed along the lines of J. DiBiase's 1990
Smith College thesis (fixed rooted dual tree per combinatorial type + face-pair lemmas + shape case split).

## Conventions
Octahedron type: antipodal pair (v, w), equator u1..u4 (neighbours of w, cyclic). W_i = w u_i u_{i+1},
V_i = v u_i u_{i+1}, Q_i = W_i ∪ V_i developed along u_i u_{i+1}. Z_k = net of the cut tree
star(v) ∪ {w u_k}: the fan W_k, W_{k+1}, W_{k+2}, W_{k-1}' around w opened along w u_k, with petals V_i
on the outer edges. κ = curvature. ω_i = angle of W_i at w, ν_i = angle of V_i at v.
e_i = angle of Q_i at u_i, f_{i+1} = angle of Q_i at u_{i+1}. Leans F_i (forward, reflex at u_{i+1}),
B_i (backward, reflex at u_i). "Touching" counts as non-overlapping.

## Proved
* Lemma A. A vertex adjacent to all others: cutting exactly its edges gives a net. (Aronov–O'Rourke star
  unfolding with source at the vertex; nonoverlap is closed, so the limit source→vertex is fine.)
  Settles n=4, n=5, and 6-vertex types: pentagonal pyramid, (5,4,4,3,3,3), simplicial (3,3,4,4,5,5).
  Prism is known separately.
* Reduction of n=6: octahedron-minus-an-edge ⟸ B(octahedron) by a limit argument (perturb the quad into
  a roof along its diagonal, an equator edge, never cut by the family). Prism-with-one-diagonal ⟸ the
  same statement for type (3,3,4,4,5,5) at a degree-4 vertex (perturb with ridges B'C and CA'), OR a
  direct chart for that type (NOT in DiBiase: her thesis treats simplicial polytopes only, see notes/dibiase_summary.md).
* Shared-vertex lemma: faces sharing a net vertex lie in disjoint wedges (angle sum < 2π): never overlap.
  Only 9 face pairs per Z_k need work: local (V_k–V_{k-1}', V_k–W_{k-1}', V_{k-1}'–W_k), opposite petals
  (V_k–V_{k+2}, V_{k+1}–V_{k-1}'), petal vs far fan face (4 pairs).
* AO reduction: if the shortest v–w path crosses u_j u_{j+1}, then Z_j is simple iff triangle w u_j v
  (in place) avoids V_{j+2} and V_{j-1}'; similarly Z_{j+1}. (Only useful for those two slits.)
* Wedge–lean framework. Lemma 1: Q_i lies in a wedge at w of opening < π (own arc + one lean).
  Lemma 2: at each ray w u_i at most one quad leans over it, by less than π − κ_{u_i}.
  Lemma 3: consecutive quads never overlap. Proposition: Z_k is simple if
  B_k+F_{k-1}<κ_w; F_k+B_{k-1}<ω_{k+1}+ω_{k+2}; F_k+B_{k+2}<ω_{k+1}; B_k+F_{k+2}<ω_{k-1}+κ_w;
  F_{k+1}+B_{k-1}<ω_{k+2}; B_{k+1}+F_{k-1}<κ_w+ω_k. Holds for some k in 98.3% of (P,v) cases; not enough alone.
* Topological step for Lemma F: a petal cannot cross a hinge segment w u_j (it would enter a fan face
  sharing a vertex with it), so petal-vs-far-fan-face overlap implies opposite-petal overlap or local overlap.
* Vertical-wedge step: opposite petals V_i, V_{i+2} meeting on the W_{i+1} side meet inside the vertical
  wedge at the apex of V_{i+1}; this forces κ_{u_{i+1}} < ν_{i+1} and κ_{u_{i+2}} < ν_{i+1}. If ν_{i+1} ≤ π/2,
  that wedge is at distance ≥ |v u_{i+1}| from u_{i+1}, so V_i can reach it only if |u_i u_{i+1}| > |v u_{i+1}|
  (petal base longer than its v-edge, i.e. ν_i > angle of V_i at u_i); same for V_{i+2}.

## Conjectured (numerically solid) — these two finish the octahedron
* Lemma F (far). If κ_v ≥ κ_u for all four neighbours u of w, then in every Z_k no far pair overlaps.
  Evidence: 0 far overlaps in 22,732 nets; every observed far overlap has two equator spikes sharper than v.
  Missing step: show κ_v ≥ max κ_u is incompatible with the vertical-wedge conditions above (and their
  mirror on the gap side). Expect Σκ = 4π to do it.
* Lemma L (local). With v the sharpest vertex and the slit at the sharpest neighbour u of w
  (also works: u farthest from v, or longest edge wu), the three local pairs never overlap.
  Evidence: 0 failures in 11,000 random octahedra + adversarial hill-climb. Known partial: the local pair is
  wedge-safe when κ_u + κ_w ≥ π (98.9% of cases); the rest are barely-reflex quads leaning < 0.18 over a
  tiny gap — a bounded-geometry inequality in (r_u, ℓ_u, e_u, f_u, κ_w) is needed.
* Conjecture C (general form, tested n ≤ 8): every vertex star extends to a net. Implies Dürer.


## Status of the work plan (updated 2026-09-08)
1. Lemma F: Case A proved; Case B reduced (2026-09-08) to two apex statements under the slit rule (details
   below and in notes/lemmaF.pdf). 2. Lemma L: not started. 3. Charts for non-simplicial 6-types: not started.
4. Write-up: notes/lemmaF.tex started (LaTeX + TikZ, figures generated from real nets by tikz_net.py).
   The FULL DiBiase thesis ("DiBiase - Polytope Unfolding - Smith 1990.pdf", top folder, 115 pages, no text
   layer) was read on 2026-09-08; summary in notes/dibiase_summary.md. Key facts: she treats SIMPLICIAL
   polytopes only (so nothing about the non-simplicial 6-types — the reductions above are needed); her
   octahedron unfolding is a spider tree rooted at a face Δ (legs Δ-A-D-G, Δ-B-E, Δ-C-F), with the four
   far pairs involving the opposite face G handled by a "safe spot" lemma (move G if it overlaps) whose
   proof is a sketch; Lemmas 4–6 are not rigorous. Chart format to adopt: planar map + unfolding map +
   21-entry face-pair chart citing lemmas. Her Lemma 3 (half-plane confinement) and Lemma 4 (angle sum at
   the cut vertex) are the informal ancestors of our D-lemma and c*-argument.
5. n = 7: not started.

## Lemma F progress (session 2026-09-08) — full account
Hypothesis: (H) v is the sharpest of ALL six vertices (κ_v ≥ κ_x for every x, including w). This is what the
final choice "v = sharpest vertex" gives anyway. The handoff's weaker hypothesis κ_v ≥ max κ_{u_i} (call it H2)
and the local one κ_v ≥ κ_{u_j}, κ_{u_{j+1}} (H1) are numerically also overlap-free, but the argument below
genuinely needs κ_w ≤ κ_v (adv_mu.py: margin 0.5 rad under (H), only 0.06 under H2, fails under H1).
Elementary consequences of (H): κ_v ≥ 2π/3; Σν = 2π − κ_v ≤ 4π/3; cone inequality (each face angle at a
convex vertex ≤ sum of the other three; checked on 240k angles) gives ν_j ≤ π − κ_v/2 ≤ 2π/3.

### Proved (in notes/lemmaF.tex; all checked numerically on the 44 observed overlaps and 72k nets)
* Petals never cross an interior hinge segment w u_j (they would enter both adjacent fan faces, and every petal
  shares a net vertex with one of them). Hence petal-vs-far-fan overlap ⟹ petal-vs-petal overlap (entering
  through the outer edge u_j u_{j+1}). So Lemma F ⟸ TRIPLE LEMMA: for consecutive fan faces W_i W_j W_{j+1}
  (any net where they are contiguous) the petals V_i and V_{j+1} are disjoint. In Z_k the relevant triples are
  (V_k,V_{k+1},V_{k+2}) and (V_{k+1},V_{k+2},V_{k-1}'). There is NO separate gap-side case: the argument
  below covers every common point of the two petals whatever side it is on.
* D-lemma (no hypothesis): V_i lies on the far side of the line through its cut edge u_j v_i, V_{j+1} on the
  far side of the line through u_{j+1} v_{j+1}; so any common point lies in D = the wedge at the crossing p*
  of these two lines opposite to the base u_j u_{j+1}. D is on v's side of the base ("above") iff
  κ_{u_j} + κ_{u_{j+1}} < ν_j, on w's side ("below") iff >, empty iff =. The 44 observed overlaps split 26/18
  exactly along this rule. Above-base meetings are in the vertical wedge of V_j at v_j (this recovers the
  handoff's vertical-wedge step, with the combined condition κ_{u_j}+κ_{u_{j+1}} < ν_j).
* The two cut edges u_j v_i and u_{j+1} v_{j+1} never cross (their crossing would be in the vertical wedge,
  so v_j inside triangle u_j u_{j+1} p, so |u_j p|+|u_{j+1} p| > s_j + s_{j+1}: triangle inequality).
  Consequence: an above-base meeting needs a petal whose base is longer than its v-edge (l_i > s_j or
  l_{j+1} > s_{j+1}) — the handoff's condition, now without the ν ≤ π/2 assumption.
* Rotation picture. Glue V_i, V_j, V_{j+1} flat around v (the "v-fan"; disjoint wedges since Σν < 2π).
  The net is the v-fan with V_i rotated about u_j by κ_{u_j} and V_{j+1} about u_{j+1} by κ_{u_{j+1}}, both in
  the same rotational sense. Composition = rotation R by κ := κ_{u_j}+κ_{u_{j+1}} about c*, the point on w's
  side of the base with base angles κ_{u_j}/2 at u_j and κ_{u_{j+1}}/2 at u_{j+1}.
  Meeting in the net ⟺ R(V_i^fan) ∩ V_{j+1}^fan ≠ ∅ (cstar.py check C3: exact agreement on 3267 triples).
  Let M = line(c*, v). R moves points from u_{j+1}'s side of M to u_j's side. Angular criterion (proved): if
  κ < ν_j and the above-base parts of V_i^fan, V_{j+1}^fan cross M (towards the other petal) by angular
  excursions ε_i, ε_{j+1} seen from c* with ε_i + ε_{j+1} < κ, there is no meeting. In particular no meeting if
  neither crosses M. (Uses: the rotation about u_j maps below-base points of V_i^fan to below-base points,
  because V_i's wedge at u_j in the net ends at the W_i edge, i.e. before the base direction.)
* Both petals crossing M through their wedges at v is impossible under (H) (would need ν_i+ν_j+ν_{j+1} > 2π).
* Above-base case under (H) forces κ_v > 6π/7 (Σκ = 4π ≤ 4κ_v + κ and κ < ν_j ≤ π − κ_v/2), hence
  Σν < 8π/7 and every ν < 4π/7.

### Numerically established (random 72k nets + adversarial hill-climbs with guards edges ≥ 0.05·diam, κ ≥ 0.05)
* Under (H): neither petal EVER crosses M above the base (224 triples incl. degenerate; adv_eps.py and
  adv_cstar.py cannot make an excursion positive; adv_mu.py: max of ν_i + ∠(u_j v c*) − π is −0.50).
  Every one of the 26 observed above-base overlaps (no hypothesis) has a petal crossing M (20 via V_i, 6 via
  V_{j+1}). Under H1 crossings occur with ε up to 1.96 ≫ κ, so H1 is not enough for THIS argument.
* Closest approach of opposite petals under (H): 0.4% of the diameter (adv_opp.py with guards); the extremal
  configurations sit at the guard boundary (a gap κ → 0, or V_j a needle), never overlap. Unguarded searches
  converge to degenerate touching (collapsed edge or flat vertex), which is why guards are needed.
* Both-reach condition: each petal alone can reach the vertical wedge of V_j under (H) (obtuse ν_j or a long
  petal), but never both (adv_cond.py Ri2: margin −0.0015 at the guard boundary). The angular "reach"
  condition for one petal: exists τ ∈ [0, ∠V_i(u_j)] with sin ν_i sin(ν_j − κ_{u_j} − τ) ≥ sin ν_j sin(ν_i + τ).
* The six wedge–lean inequalities of the Proposition hold for all k in only 99.5% of nets under (H)
  (failures: needle w with κ_w ≈ 6, tiny ω) — so they cannot replace the rotation argument.
* Below-base meetings (18 observed) always have: the outer-edge lines of W_i and W_{j+1} converging on w's
  side (ΣW := ∠_{u_j}W_i + ∠_{u_j}W_j + ∠_{u_{j+1}}W_j + ∠_{u_{j+1}}W_{j+1} < π), exactly one of the two fan
  faces reaching past the crossing X (14 times W_i, 4 times W_{j+1}; both is impossible since fan faces are
  disjoint), the opposite petal passing over the far vertex of that fan face, two equator vertices with
  κ ≈ 6 and v nearly flat (κ_v ≤ 1.2).
* Opposite-petal overlaps come in pairs: the same two petals overlap in Z_k and Z_{k-1} (the triple is
  contiguous in both), so 44 observations = 22 geometric events.

### Open
* Above-base case: prove that under (H) and κ < ν_j no petal crosses M above the base. Crossing mechanisms:
  (a) wedge of V_i at v passes the ray of M beyond v: ν_i > π − ∠(u_j v c*) (needs ν_i + ν_j > π, hence
  κ_v < π; combined with κ_v > 6π/7 this is a narrow regime; adversarial margin 0.5 rad, and κ_w ≤ κ_v is
  what provides it); (b) far vertex u_i above the base on u_{j+1}'s side of M; (c) an edge of V_i crossing the
  base line outside the segment u_j u_{j+1} on u_{j+1}'s side of M (via v u_i needs ν_i + ν_j > π + ψ).
  Fallback if only "ε_i + ε_{j+1} < κ" can be shown: still sufficient by the angular criterion.
* Below-base case (κ ≥ ν_j): turn the necessary conditions above into a contradiction with (H). Note
  κ_{u_j}, κ_{u_{j+1}} ≤ κ_v and ν_j < κ ≤ 2κ_v; observed cases have v flat, so (H) should kill them easily,
  but no argument is written.
* Then Lemma L (local pairs), untouched.

### Do not retry (this session)
* Separating the two petals inside D by a fixed line (bisector of D at p*, lines through v_j): fails in about
  a third of the non-degenerate cases even under (H). The separation is a rotation phenomenon.
* Star-unfolding (Aronov–O'Rourke) shortcut: for the two slits adjacent to the geodesic quad it only removes
  the three pairs not involving that quad; useless for the other slits.

### Code added (all use .venv/bin/python; scripts take `seed N` or `HYP seed restarts steps`)
octa.py — module: Octa(P, v) computes r,s,l (|wu|,|vu|,|u u'|), ω, ν, angles aV/aVp/bW/bWp, e, f, κ, leans
  F,B; Z(k) nets with w at origin and slit ray = +x (CCW fan); PAIRS/LOCAL/OPP/FARFAN by name; overlaps(k),
  intersection(k, name), arc_of; random_octahedra, all_apexes, sharpest_apex, hill_climb. Cross-checked
  against unfold.py on 7200 nets.
vwedge.py (baseline vertical-wedge check), oppcases.py (collects/classifies/draws all opposite-petal overlaps;
  cases_opp/cases.pkl = the 44 cases with P and apex), oppwedge.py (six inequalities under hypotheses),
adv_opp.py (adversarial petal separation; hypotheses H1/H2/H3 = (H); results adv_opp_*_d.pkl),
inspect_adv.py (print + draw best adversarial configs), adv_cond.py (adversarial on the reach/angle/ΣW
  conditions), adv_sep.py (candidate separating lines; do not retry), cstar.py (all checks of the rotation
  picture; analyse(o,i) returns the flags and excursions), adv_cstar.py / adv_eps.py / adv_mu.py (adversarial
  tests of the side conditions, of ε_i+ε_{j+1}−κ, and of ν_i+∠(u_j v c*)−π), draw.py (PNG nets, zoom),
tikz_net.py (TikZ for a net Z_k and for the three-petal picture with D, c*, M), notes/lemmaF.tex (+figs/).
Convention trap: several helpers use a "signed side" test; cstar.signed_side is the standard left-of-line
  test (fixed 2026-09-08 after a sign bug made the side checks vacuous — always re-verify a new check on the
  44 stored overlaps, which must all be flagged).

## Case A of the Triple Lemma is PROVED (2026-09-08, later session) — see notes/lemmaF.tex §"Case A is closed"
* No-wrap lemma: under (H), ν_i + ν_j ≤ π + κ_u + κ_{u'} for every triple. Proof: Σκ = 4π and (H) give
  κ_u + κ_{u'} ≥ 4π − 4κ_v = 4Σν − 4π; if Σν ≥ π then π + κ ≥ 4Σν − 3π ≥ Σν ≥ ν_i + ν_j, else ν_i + ν_j < π.
* Apex-cone lemma: each petal lies in the cone at its apex spanned by its two cut edges. If κ < ν_j and
  ν_i, ν_{j+1} ≤ π − ν_j + κ, the two apex cones have disjoint interiors: the cones meet iff the direction
  v_i → v_{j+1} lies in the sector between the direction v_i → u and the direction u' → v_{j+1} (width
  π − ν_j + κ < π), and a coordinate computation shows this happens iff both cut edges reach their crossing
  point p*, i.e. iff they cross — excluded by the cut-edges lemma. So Case A needs NO side condition; the
  c*-rotation argument (Open problem 1) is superseded and kept only as a second view.
* Numerics: cones' intersection has empty interior in every Case-A triple under (H) (adversarial depth −0.0007
  at the guard; without (H) the adversary reaches +0.006); no-wrap margin 1.3 rad (adv_wrap.py, adv_cones.py).
* Case B (κ ≥ ν_j) remains open; exact structure established 2026-09-08 (notes/lemmaF.pdf §"The below-base
  case"). Let A = line(u, u_i), C = line(u', u_k) (outer fan edges; u_k = far vertex of W_{j+1} = slit copy),
  Σ_W = the four fan angles at u, u'. Proved: V_i lies beyond A and V_{j+1} beyond C, so a meeting lies in the
  wedge Ω beyond both lines; Σ_W ≥ π ⟹ Ω is above the base, disjoint from D ⟹ no meeting; Σ_W < π ⟹ Ω is the
  wedge at X = A∩C opposite the triangle u u' X (w inside it). V_i reaches Ω only via its far vertex u_i past X
  (f) or its apex v_i ∈ Ω (a); not both far vertices past X. Direction identity: ∠_{u_k}V_{j+1} − Σ_W =
  ν_i + ν_m + ∠_uV_i − κ_back, κ_back = κ_{u_i} + κ_{u_k} + κ_w (and the mirror one); an apex in Ω needs the
  left side > 0. Sub-case (a,a) [both apexes in Ω]: a meeting point p closes the hexagon u_i p u_k w u_k' v_m
  around V_m, and the angle sum gives ν_m = κ_back + γ_p + (two non-negative angles) (uses Lemma L for the slit
  pairs); so ν_m ≤ κ_back excludes (a,a), and for ν_m > κ_back the outer cut-edge lines converge on V_m's side
  and the apex-cone lemma applies with base u_i u_k (gap: no-cross of the outer cut edges across the slit).
  BUG FIXED: the old test "X on w's side" (caseB_sub.py) compared the sign of a point ON the line and was
  vacuous; the "15% both reach" figure is withdrawn. Correct numbers under (H): 23,578 Case-B triples, 19,858
  with Σ_W ≥ π, 27 both-reach ((a,a) 22, (fa,a) 4, (a,fa) 1); adversarial closest approach in Ω: (a,a) 3.5%,
  (fa,a) 3.2%, (a,fa) 1.9%. Tight (a,a) configs: w, u_i, u_k flat, u, u' needles, u_k at X, the thin V_m
  between the petals. Outer cut edges never cross when ν_m > κ_back (adv_crossA.py, best −0.003), and the apex
  cones are disjoint in every (a,a) triple with ν_m > κ_back.
* SLIT RULE (recommended route, 2026-09-08). With the slit at the sharpest neighbour u_k of w (the rule Lemma L
  needs anyway: without it local pairs overlap under (H) in 134+61+73 of 8000 nets), Case B is numerically dead:
  in 641 Case-B triples with Σ_W < π, V_i never reaches Ω and V_{j+1} only via its far vertex; adversarially
  (adv_reach.py, adv_angle.py, hyp H3R = (H)+rule, R = rule alone): v_i beyond C −0.35 diam (Σ_W ≤ π−0.3),
  v_{j+1} beyond A −0.12, u_i past X −0.026, ∠_{u_k}V_{j+1} − Σ_W ≤ −0.35 under R alone. Since a meeting needs
  an apex in Ω, it suffices to prove under (H)+rule: (P1) v_{j+1} ∉ Ω, (P2) v_i ∉ Ω. lp_angles.py: linear angle
  facts alone (face sums, cone inequalities, rule, (H)) allow ∠_{u_k}V_{j+1} − Σ_W up to π/2, so edge lengths
  must enter. Pure curvature counting also fails: both-reach configurations exist with
  κ_u + κ_u' + 2max + κ_{u_i} + κ_w − 4π = −1.9 (adv_rule.py), i.e. the rule acts through the geometry.
  Under (H) alone (no rule) the route is: (a,a) via hexagon identity + cones (+ no-cross across the slit),
  then the four far-vertex sub-cases — heavier.

## Known false (do not retry)
* "Star unfolding along a non-shortest geodesic is simple": fails ~4e-5.
* "One of the two slits at the shortest-geodesic edge always works": fails ~0.7%.
* "Some antipodal pair has all four quads convex": false in 72% of octahedra.
* Any fixed labelled tree for the octahedron: every orbit class fails on some realization.

## Work plan
1. Lemma F, Case B: prove (P1) v_{j+1} ∉ Ω and (P2) v_i ∉ Ω under (H) + slit rule (metric argument; tight
   configurations are needles, see notes/lemmaF.pdf figure in §Case B). Then Lemma F holds under the rule
   modulo Lemma L. Test every intermediate inequality with adv_*.py-style scripts before writing it.
2. Lemma L: derive the exact overlap condition for the flank pair at the slit (two triangles with apexes
   u, u' at distance 2 r_u sin(κ_w/2), direction gaps κ_u + κ_w outer and e_u + f_u − ... inner),
   then show the sharpest-neighbour choice violates it. Use local.py cases as the test bed.
3. Charts for the two non-simplicial 6-vertex types (or confirm the limit argument suffices).
4. Write-up in DiBiase's vocabulary: per type a rooted tree, a 21-entry chart, lemma citations.
5. Then n=7: enumerate the 34 types (plantri), tag by max degree / dome / prism, apply Lemma A, F+L.

## Code map (all Python, numpy/scipy)
unfold.py (simplicial nets, all trees, overlap test), unfold2.py (polygonal faces), gen.py (random
polytopes incl. flat/needle), geostar.py (quad convexity, geodesic star unfolding), pairpos*.py and
farcond.py (which pairs overlap, conditioned on curvature ranks), lemmaF.py (full leans), local.py
(local pair when κ_u+κ_w<π), bstar.py/rules3.py (rule B* tests + adversarial), wedge.py (six inequalities),
allconvex.py, bothstats.py, angles.py, conjC.py, nonsimp6.py, types6.py.
