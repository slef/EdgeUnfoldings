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
