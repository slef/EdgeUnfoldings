# Dürer's problem for n ≤ 7 vertices — proof state and work plan

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
  direct chart for that type (probably what DiBiase did).
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
1. Lemma F: proof architecture found and numerically validated, two gaps left (details below and in
   notes/lemmaF.pdf). 2. Lemma L: not started. 3. Charts for non-simplicial 6-types: not started.
4. Write-up: notes/lemmaF.tex started (LaTeX + TikZ, figures generated from real nets by tikz_net.py).
   The FULL DiBiase thesis is now in the top folder ("DiBiase - Polytope Unfolding - Smith 1990.pdf",
   115 pages, added 2026-09-08 08:10; the old 3-page excerpt is JulieDiBiase_p71-3.pdf). Nobody has read it
   yet in this project; read it before writing more (it may contain the chart format and the face-pair lemmas).
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

## Known false (do not retry)
* "Star unfolding along a non-shortest geodesic is simple": fails ~4e-5.
* "One of the two slits at the shortest-geodesic edge always works": fails ~0.7%.
* "Some antipodal pair has all four quads convex": false in 72% of octahedra.
* Any fixed labelled tree for the octahedron: every orbit class fails on some realization.

## Work plan
1. Lemma F: prove the mirror (gap-side) version of the vertical-wedge step; combine with Σκ = 4π and
   κ_v ≥ max κ_u. Test every intermediate inequality with lemmaF.py-style scripts before writing it.
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
