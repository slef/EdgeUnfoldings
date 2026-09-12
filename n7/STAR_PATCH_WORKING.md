**Historical working checkpoint, superseded by the completed written
proofs in BIPYRAMID_STAR_PATCH.md and BIPYRAMID_RECEIVERS.md.** Preserved
to record the discovery and audit sequence; its future-tense notes are old.

# Shortest-patch comparison — working proof, 13 September overnight

This is a separate research route being audited, not yet a completed page.
Current time around 18:15 UTC; overnight work continues to 22:04 UTC.
Do not lose the existing Case A work or conflate the following conditional
results with a universal bipyramid proof.

## Published dependency actually inspected

Kiazyk–Lubiw, SoCG 2015, Definition 1 (vertex sources and shortest-path
ties are allowed), Theorem 4 (star net nonoverlap), and Lemma 6 (empty
region at a vertex image):
https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SOCG.2015.390
PDF downloaded to /private/tmp/pdfs/kiazyk-lubiw-star.pdf; Figure 4,
page 396 (PDF page7), rendered and visually inspected. The PDF skill was
read. No PDF authoring was done.

At a star-net vertex p adjacent to source copies q0,q1 at distance D,
the outside gap has angular width kappa_p. The empty region W is bounded
by segments p q0,p q1 and perpendicular rays from q0,q1 directed into the
gap. For gap<pi the rays meet; for gap>=pi the region is unbounded.
The circular gap sector of radius D is empty too. A triangle inside the
gap sector and the two halfplanes x dot(qj-p)<=D^2 lies inside W.
This elementary inclusion is the precise part needed below; audit it.

## 1. Shortest p–q path lives in a strictly convex two-face patch

For a convex bipyramid with any m>=3, every surface path from pole p to q
crosses the equator cycle. At a crossing x on ui ui+1, its length is at
least |px|+|qx|. Conversely those two straight segments lie in the two
original facets Wi,Vi, so that sum is achieved by a surface path.
Thus shortest length = min over equator x of |px|+|qx|.

A minimizer cannot be an equator vertex. The two adjacent flattened
patch corners there sum to 2*pi-kappa_ui<2*pi, so at least one is <pi;
cutting the broken p–ui–q corner inside that patch gives a strict shortcut.
Consequently the path crosses the interior of an equator edge and is a
straight diagonal p q_i in its flattened patch. Such a diagonal crosses
the hinge internally only when that patch is strictly convex at both
ring corners. Thus select a shortest diagonal among all convex patches.
All ties may be resolved arbitrarily.

Cut this p–q geodesic and every q–ui edge. Each q–ui is a shortest path
because it has Euclidean length. Cuts have disjoint interiors and form
a shortest-path star. The chosen convex patch Qk is split by its diagonal
into two planar triangles p q0 uk and p q1 uk+1, lying at the two ends of
the same safe fan core. They are geometric triangles across the old hinge;
the diagonal is allowed only in this comparison unfolding.

Replacing the geodesic cut with p uk keeps one half and rotates the other
half rigidly around p by the curvature gap, aligning q0 with q1. This
reconstitutes the whole original two-face patch. The actual final cuts
are precisely star(q) plus original edge p uk. All other m-1 patches
keep their star placements. Hence they form a known safe core.

At n7, that gives 28 core face pairs +1 within-Qk pair +4 fan/fan pairs
involving Wk +3 further pairs against the uncut adjacent patch =36/45.
The nine remaining obligations all involve Qk. Other convex patches are
also automatically separated from Qk by their fan wedges.

## 2. Right/obtuse ring corner gives an entire safe edge net

Suppose the chosen shortest patch has a ring corner gamma>=pi/2 at ui.
Choose either fan pole p; move the half-triangle with that ui corner.
Write old p=0, q0=(D,0), ui=r(cos alpha,-sin alpha). The triangle has
angles alpha at p, beta at q0, gamma at ui. Gamma>=pi/2 gives r<D and
r<=D cos alpha. Thus its radial boundary R(theta), theta in[-alpha,0],
is nondecreasing toward theta=0 (derive this from the line q0–ui, or
its outward normal). Rotate by kappa into the star's empty gap.
For angles still below zero, R_new(theta)=R_old(theta-kappa)<=R_old(theta),
so that part lies in the removed old half. The newly occupied part is
inside the empty circular gap sector, since all its radii are <=D.
If kappa>=alpha the entire moved half lies in that empty sector.
All stationary pieces therefore remain disjoint from the moved half.
Boundary equality is harmless. Rejoin the original patch: the cuts are
all original edges. This works for every m, no curvature ranking needed.

## 3. A pole with curvature >=pi suffices for EVERY bipyramid

This is the most promising new theorem; audit fully and check exact
three/four-inward examples before claiming it publicly.

Choose the high-curvature pole p as FAN, and the other pole q as source.
Select a shortest convex patch as above. Split its source angle nu<pi
by the shortest diagonal. Choose the half whose source angle beta<pi/2
(e.g. the smaller half); move that half, slit at its ring vertex ui.
Let alpha be this half's angle at p and r=|pui|.

The strict link-side bound at p gives
 alpha < omega_k < Gamma_p/2 = pi-kappa_p/2 <= kappa_p/2.
With old q0=(D,0), old ui=r(cos alpha,-sin alpha), the new endpoint is
 ui'=r(cos(kappa_p-alpha),sin(kappa_p-alpha)), and q1 has angle kappa_p.
The whole moved triangle lies inside the gap, since alpha<kappa_p.

Beta<pi/2 is exactly r*cos(alpha)<D, so ui' satisfies the tangent bound
at q1. Also
 cos(kappa_p-alpha)-cos(alpha)
   = -2 sin(kappa_p/2) sin(kappa_p/2-alpha) <0,
so ui' satisfies the tangent bound at q0 too. Vertices p,q1 also satisfy
both halfplanes. The moved triangle is therefore inside the empty W;
its interior is in the interior of W. All stationary star pieces are safe.
This proves the original-edge net. Equality kappa_p=pi works strictly
because alpha<Gamma_p/2=pi/2. There is no restriction on bad-patch count
or m. This would settle the high-pole-curvature branch for ALL 15 n7
symbolic patterns, including three/four bad patches.

More generally sufficient for a particular half: beta<=pi/2,
kappa_p>=alpha, and r*cos(kappa_p-alpha)<=D. The same triangle-in-W
argument applies. A simpler sufficient gate is kappa_p>=2*alpha and
beta<=pi/2. Keep exact boundary cases separate from strict sample checks.

## 4. A missed easy auxiliary branch is also solved

For the receiver chain's three patches Q0,Q1,Q2, the six-vertex hull
on p,q,u0,u1,u2,u3 retains those six original triangles. Its remaining
cap on boundary p,u3,q,u0 is either two triangles with diagonal u0u3
(octahedron), two with diagonal pq (both poles universal), or a flat quad.

For the pq-edge case, cutting the universal source q's star is a known
safe shortest-path star. It preserves all three patches and their fan
joins, so the desired pair is safe at EITHER choice of fan pole. The new
pq edge is used only in the comparison, never as a cut in the n7 net.
For a flat cap use the straight diagonal pq inside that facet as a
shortest-path comparison cut; same conclusion. Thus the 'other reduced
graph' branch left in BIPYRAMID_RECEIVERS.md is actually solved by this
published-star comparison. Only the actual octahedron branch needs
its auxiliary curvature orders or the newer local Case A separator.
The existing exact 'other-reduced-graph-Case-A' example should also get
an exact 28-pair auxiliary star check to validate this application.

## Floating discovery just completed / limits

/private/tmp/n7_star_patch_search.py and .json, seed913620:
551 attempts,233 valid; no failure of the proposed proved gates was found.
But THREE shapes allegedly fail ALL FOUR shortest-patch endpoint trees
outside those gates. These need exact conversion and overlap witnesses.
Do not claim four-candidate failure from floating scores alone.
The first two normalized penetration scores are about8e-5 and1.36e-4;
third3e-7 might be a numerical issue. These are all local-to-Qk tests.

Counts include three/four-bad examples passing the proposed gates. Use
them for exact certificates. Test longer after disabling the stop on
three four-candidate failures; prioritize high-curvature pole choices
and record successful three/four-bad cases.

Other pending work from this pass:
- n7/BIPYRAMID_CHAIN_PAIR.md + angle_intervals.py + receiver_identity.py
  + receiver_pairs.py were installed and built, not committed yet.
  All38 Python tests and both Node UI tests passed.
- Four exact pair examples: three Case A (including H<0) and one base-cone.
- /private/tmp/n7_chain_gate_cover.json gives five examples where the ONLY
  eligible chain pole has H<0. This defeats a simplistic 'swap to H>=0'
  shortcut. Exact-convert one if useful; all still pass wider separators.
- /private/tmp/n7_chain_cobyla.py/.json optimized the wide-apex failure;
  none found, objectives still negative. Do not treat as proof.
- /private/tmp/n7_pair_class_search.py/.json:350k attempts,124043 valid,
  4916 relevant both-low chain shapes.6771 both-short choices,2443 Case A
  wide choices,1 base-cone; no uncovered local separator was found.
  These are discovery counts, not universal proof or coverage percentages.

Need update the main overnight handoff and archive useful scripts/results
before ending this research pass. Last committed HEAD is5a36963.
