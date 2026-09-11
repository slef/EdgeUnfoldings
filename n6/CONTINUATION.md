## Closing audit of the requested four-hour session

Window: 11 September 2026 17:05:34–21:05:34 UTC (12 September
02:05:34–06:05:34 JST). Both remaining original-edge type arguments were
completed as written research proofs. Independent mathematical review is
still pending; the geometric dependency chain is not formally verified.

The last audit checked the same-net pair obligations, copied edges,
closed curvature thresholds, flat auxiliary hinges, and positive-slack
identities. The overview introduction now agrees with the 7/7 written-proof
ledger; its earlier 5/7 introduction remains in collapsed history.
All 271 distinct scientific tests passed (269 in the full run and two
subsequent switching tests), as did the final navigation and progress
checks. All 220 rendered evidence links resolve in the packaged site.
These are implementation and algebra checks, not a substitute for review
of the universal geometric proofs. Work is saved locally, without a push.
The next substantive task is the independent audit in N6_PROOF_MAP.md.
Earlier session instructions and counts below are historical.

## Verification of the completed written argument

The full Python suite passed **269 tests** in 274.058 seconds. The two
subsequently added exact switching-family tests passed separately (17.007 s),
for **271 distinct tests**. Navigation, progress accounting, retained history,
original prism model ordering, and the separate minus-edge conjecture checks
passed. The new face-tree SVG was rendered and visually checked; the full
browser page was not inspected through a blocked browser surface.

The three prism angle identities vanish as exact rational polynomials in
14 independent angle variables. The reflection preserves the original facet
sets, fixes the seventh tree, and permutes the six near-stars. The existing
finite graph enumeration again returns exactly seven six-vertex types.
These algebraic/combinatorial audits do not formally verify the geometric
lemmas. New sharp-fan and obtuse/acute fallback examples each include a
whole nine-parameter family with independently checked original face pairs.

Reproduce the final saved examples with:

    python3 -m n6.prism_edge_examples
    python3 -m n6.prism_switch_examples
    python3 -m n6.prism_angle_identities

All new universal claims are written research proofs pending independent
mathematical review. The whole n=6 argument is now written; the stronger
original every-slit and fixed-two-tree questions remain open.

## Current completion checkpoint: 12 September 2026

All seven six-vertex type arguments are now written, pending independent
mathematical review. The complete review map is [N6_PROOF_MAP.md](N6_PROOF_MAP.md).
The new prism proof is [PRISM_EDGE_PROOF.md](PRISM_EDGE_PROOF.md):
its six near-stars plus the triangular-chain fallback cover every curvature
case. PRISM_ONE_PAIR.md proves fourteen fallback pairs universally;
PRISM_SHARP_FAN_SWITCH.md gives three exact positive angle identities;
PRISM_GATE_SWITCH.md handles the other source by an obtuse/acute switch.
Direct-cut failures force the latter gate. All equality cases and original
quadrilaterals are retained. The stronger every-slit Lemma F and fixed two-tree
minus-edge conjecture remain open. No finite numerical experiment is a
universal-proof premise. The current web overview marks 7/7 **written proofs**,
with independent review explicitly pending. Earlier checkpoints below keep
their original counts and limitations.

## Latest prism branch (12 September, after the complete minus-edge proof)

PRISM_COMPLEMENTARY_ROUTES.md proves both fans <=pi with sum >=pi.
Both routes at a source cannot be Case A when both curvature gates hold;
if neither source gets both gates, their failures force an original source
above pi, with an allowed weighted cut. All equalities included.
Exact point, nine-parameter family, and reflected example are saved under
results/prism-complementary-*. Outside the all-low and two-high-end families,
only one-high/one-low fan or two-low-fan sum<pi remains. These regimes have
proved subfamilies; the whole prism type remains open. Positional counts
remain 0/6,11/15,20/20; geometric branch count is now 3/5.

## Latest: complete original-edge minus-edge proof (12 September 2026)

MINUS_EDGE_PROOF.md closes the entire type. When sharp P has no allowed
fifth endpoint passing 2*kappa_c+kappa_D>=pi, its three strict failures
force kappa_C+kappa_A>pi and kappa_C+kappa_B>pi, with A,B<pi/2.
The generalized complementary-source theorem then supplies one safe net.
Reflect for Q. Every branch and equality is included. The total is now
6/7 written whole-type proofs, pending independent review; prism remains open.
The old T_P/T_Q conjecture retains its separate 7/28 class count.
Exact fallback point, full 10-parameter family, and reflection are saved
under results/minus-complementary-fallback*. The universal argument is
geometric, not an inference from these examples. Earlier entries below
retain their original progress counts.

# Active four-hour continuation: two sharp prism ends

User request: keep trying the last proofs for four hours, starting
11 September 2026 17:05:34 UTC, through 21:05:34 UTC (12 September
02:05–06:05 JST). This checkpoint is early in that window, not the end.
The heartbeat continue-lemma-f-proof-research is active every 15 minutes
through the deadline; pause it at the deadline and report the full result.
No subagents or push in this turn. Preserve unrelated lean_statement/ and PDFs.

## Third checkpoint: wider Case A and exact length separators

CASE_A_WIDE_CONES.md proves that s<=L and lambda<=(pi+theta)/2,
or the reflected condition, suffice for opposite-petal nonoverlap.
The geometric distance-sum inequality s+s'<L+R and the source identity
lambda+rho<pi+theta are the only extra ingredients. Equalities included.
This proves both-short cases, two nonobtuse outer apex angles, and a
nonobtuse middle apex (which forces both-short). A possible remaining
failure needs two adjacent obtuse face angles at the source. Hence
sources with at most one obtuse incident angle have all Case A triples safe.
This does not alone supply local or Case B premises for the whole net.

cofacial_case_a_examples.py gives exact minus and prism examples and
six-parameter symmetric affine boxes that fail every older original-star
criterion, Case B and the older one-sided test, but pass the wider theorem.
Independent original-face certificates check all21/all15 pairs. These affine
boxes are not full shape charts. Whole-type count and sharp-position ledger
are unchanged.

The wider bound is NOT automatic with fan<=pi: a targeted optimization
found case-A-low-fan-wide-failure.certificate.json. It has a sharp actual
slit, low fan, Case A, one long side and an obtuse short-side apex above
the wider bound. Every actual face pair is nevertheless nonoverlapping.
The new CASE_A_LENGTH_SEPARATORS.md retains the actual shortfall A and
overshoot B on a common positive scale. A>B; in the difficult positive
case the left line works iff A*sin(lambda)>=B*sin(lambda-theta).
The full four-branch table gives exact boundary tests for the two full
apex cones, assuming the automatic source angle identity. The exact
low-fan wider-test failure passes this metric test. The high-fan real
overlap case-A-high-fan-failure fails both, and its same-solid repair
is independently certified safe. Failure of a cone test is not by itself
finite-face overlap. No universal low-fan Case A theorem has been proved.

The new checker functions are length_planar_tests and verify_lengths in
case_a_one_sided.py; cofacial verify_case_A now uses the actual-length
separator to certify its whole original net. The overview has #case_A_wide
and #case_A_lengths with the exact meaning and limits; successive notes
remain in history. A 150000-shape exploratory sample missed the wider-test
failure, illustrating why no sampled success fraction is treated as proof.
The symbolic low-fan wider-failure query was interrupted once the exact
counterexample was verified; its result is UNKNOWN, not UNSAT.

A literature dependency audit found that an older infinite empty-wedge
claim in a star-unfolding proof was false (Kiazyk--Lubiw 2015 section3.2,
Figure8 explicitly corrects it). Our star comparison uses only their
Theorem4 nonoverlap, not that false wedge assertion. The dependency
boundary is documented in COFACIAL_STAR_REDUCTION.md.

## Fifth result: the complementary-source angle proof closes C/D sharp

MINUS_COMPLEMENTARY_SOURCES.md is the main new breakthrough at 19:46 UTC.
If minus-edge C is sharp and A/B low, compare star(A)+BC and star(B)+AC.
The cofacial/sharp-slit reduction leaves Qquad/APQ versus Qquad/BPQ;
middles ADQ/BDQ share K=kappa_D+kappa_Q. If either K>=nu_A/B, Case B
finishes it. Otherwise both are Case A. Define theta_X=pi-nu_X+K,
q_X the quadrilateral angles, mu_A=PAQ, mu_B=PBQ,
tau=APQ+BPQ at P. Exact angle sums give
K+q_D=nu_A+nu_B+mu_A+mu_B+tau. For all four combinations of an outer
angle at A and one at B, their sum is strictly below theta_A+theta_B.
The four positive gaps are recorded in the proof. Thus one source has
BOTH outer angles strictly below its OLD theta no-wrap bound. This
uses CASE_A_CONES.md directly, not the newer wider or length refinements.
If A/B sharp, the older high-source rule works; C=pi is included. Reflect
C/D and P/Q for D sharp. One tree has all its own obligations proved safe.

Consequently minus singleton positions A,B,C,D and ALL15 two-sharp pairs
are proved. All20 triples remain proved. Only P-alone and Q-alone remain
open (two positions related by symmetry). Prism remains singleton0/6,
pairs11/15, triples20/20. Whole-type count remains5/7.

minus_complementary_sources.py selects a uniformly verified fixed tree
on an exact domain. minus_complementary_examples.py saves a new C/P-sharp
point and full10parameter local chart outside all earlier curvature
criteria, the D/Q-reflected point, and an exact C=pi example. All21 pairs
are independently checked for each. The initial runtime call without
setting interval precision was unresolved; at prescribed240bits it passes.
Do not mistake that initial interval failure for a geometric counterexample.

CASE_A_SUPPORT_TRIANGLE.md is a separate new planar refinement: for a
left-short/right-long pair, convexity of
(ell-R)|uX|+L|u'X| on the containing triangle gives
(L-s)/(s'-R)>L/(ell-R). This yields the still wider angular allowance
2*lambda<=pi+theta+alpha, or its reflection. Exact angle equality and
actual-length tangency controls pass. These refinements are not needed
for the complementary-source proof.

## First new geometric theorem

PRISM_TWO_SHARP_ENDS.md proves the fixed original two-pair tree whenever
kappa_2>=pi AND kappa_5>=pi, equality included. Face labels A..F are
021,0352,013,1254,143,345. Cuts 02,12,25,35,45; hinges C-A,C-B,C-E,E-D,E-F.
Thirteen pairs are shared-vertex pairs; only A/F and B/D remain.

At each sharp end, every original face angle is strictly below pi/2 by
the spherical-link triangle inequality. For A/F, view around B or D;
the middle quadrilateral base-angle sum exceeds pi in both views.
Their intervening central-angle sums are pi-angle(C,1)+angle(E,3)
and pi-angle(E,3)+angle(C,1), totaling 2*pi. At least one base-cone
separator applies. For B/D, use middle cap A or F. Their intervening
sums are pi-angle(C,3)+angle(E,1) and its complement. Choose one >=pi.
Its Case B has a base-cone separator; its Case A has both no-wrap bounds
because the three incident angles at its sharp apex total <=pi.
The equal-cut-length cone proof applies to convex polygonal petals too.

This is a written research proof awaiting independent review, not formal
verification. prism_two_sharp_ends.py checks its hypotheses on a point,
a full nine-parameter box, and exact one-/two-end equality points. All
15 original pairs replay independently (13 vertex fans + 2 edge separators).
The strict example is outside every previous original-star sufficient rule.
Five focused tests check this branch and its limits. The overview has #prism_two_sharp with the full
explanation, true-scale net and exact 3D model; the prism now has an explicit
three-part curvature partition, two branches proved and one open. This is
not a fraction of shape space. Whole types remain 5/7.

## Second checkpoint: a star comparison and sharp-position ledger

COFACIAL_STAR_REDUCTION.md proves that each of the four cofacial routes
in either remaining type inherits all faces except its movable original
quadrilateral from a shortest-path star. The diagonal across that Q is
only a comparison cut; final trees use original edges. The theorem uses
Kiazyk--Lubiw 2015 Definition 1/Theorem 4, which explicitly allows a vertex
source. Adding shared-vertex paths leaves exactly two original pair checks:
19/21 proved for minus, 13/15 for prism, with no curvature ranking.

For a cofacial route with fan w<=pi and route endpoint c>=pi, the existing
sharp-slit reduction supplies every local/finite-cut/small-fan premise.
One opposite-petal pair lies outside Q and is inherited; only the other
opposite pair remains. If its middle base xy has kappa_x+kappa_y>=nu_middle,
Case B applies and the whole net is proved. A sharp x or y suffices.
Remaining middle bases: minus A/C or B/C -> DQ; A/D or B/D -> CP;
prism 1/2 -> 34, 1/4 -> 02, 3/0 -> 45, 3/5 -> 01.

SHARP_VERTEX_PATTERNS.md now covers all 20 three-sharp-vertex position
patterns in both types. Sharp means >=pi. At most three sharp vertices
are possible by positive curvature and total 4pi. Outside all<=pi:
minus singleton 2/6, pairs 13/15; prism singleton 0/6, pairs 11/15.
Open minus positions: C,D,P,Q and pairs CP,DQ. Open prism: all six
singletons and pairs 01,02,34,45. Counts are positions, not shape volume.
The full types remain open. In particular minus C,D both sharp is a
new whole branch: choose the lesser A/B as low fan, slit C, then D makes
Case B. Prism new pairs 24,05 use the same theorem; 04 also follows from
the earlier curvature budgets. The earlier prism two-sharp-end theorem
covers 25, including both exact equality boundaries.

cofacial_case_b_examples.py saves minus C,D-sharp and prism 2,4-sharp
points and full ten-/nine-parameter boxes. All old original-star criteria
reject these examples; the new condition plus independent all-pair replay
passes. An exact minus point has both C,D curvature exactly pi. Six
focused tests check these domains, every cofacial route, and the ledger.
An initial prism 0,4 example was correctly found to meet earlier budgets
and was replaced with the genuinely new 2,4 example.

All four minus cofacial routes CAN fail on one exact solid: retained
minus-cofacial-{0,1,2,3}-failure.certificate.json and shared verification.
Each overlap involves Q; P and Q are both sharp. Same-solid star(P)+DQ
repair passes old high-source rule and all21 original pairs. Do not claim
the four cofacial choices universal. Numerical lead only: 150313 samples
with min(kappa_P,kappa_Q)<pi gave no simultaneous failure of all four.

The lifted low-fan Case A nonlinear query also returned UNKNOWN after
its 30-minute timeout, not UNSAT; both query encodings/reports are saved.
No running solver remains. The useful next target is the one residual
quadrilateral/triangle Case A pair at a sharp cofacial route, or a switching
argument for the remaining one-/two-sharp-position patterns.

The overview now has #sharp_positions, #cofacial_star (three-panel
true-scale comparison figure), #case_A_one_side, and exact 3D models.
Progress dashboard reads and checks the saved positional ledger. Existing
history is preserved. Navigation/progress/minus VM tests pass; the new SVG
was rendered and visually inspected. Local-file browser denial remains
respected. Continue through 21:05:34 UTC; this is not the final checkpoint.

## Current research target and exploratory work

The main remaining strategy is sharp slit c>=pi with low fan w<=pi:
only the opposite-petal Case A tests remain, by ORIGINAL_EDGE_RULE.md.
A provisional stronger conjecture is that Case A alone is always safe
when w<=pi. It is unproved. If the sharp-slit theorem were completed,
it would close the minus type; together with the new double-sharp prism
branch it would close the prism type. Recheck the combinatorial selection
argument before asserting that implication as a theorem.

CASE_A_ONE_SIDED.md gives a new written planar separator: the angle bound
is needed only on one short cut edge, rather than both apex angles. It is
not automatic even at sharp slits: later low-fan random examples have
both conditions fail, but their actual faces are still numerically safe.
The exact checker and an example failing the older two-angle criterion are now saved in case_a_one_sided.py and results/case-A-one-sided.*. Three focused tests pass.

Numerical work only (not proof): 30,000 original samples per type gave no
sharp-slit/low-fan failures. Detouring around a forbidden diagonal via its
two boundary neighbors CAN fail in both directions; these differ from
the older cofacial two-route prism conjecture, which remains unrefuted.
The new probe files retain exact rational input proposals, not verified
failures. A 20,000 strict-octahedron low-fan search had 10,953 Case A pairs,
20 failing the old no-wrap bounds, and no actual numerical pair failure.
Several also fail the new one-sided test. Bounded optimization of all 20
found no positive overlap; it often approached degeneracy/contact.
The direct exact algebraic query caseA_low_fan returned UNKNOWN due to
memory exhaustion after 33 seconds at 2 GB, not UNSAT or a proof.

Temporary scripts/results in /private/tmp: case_a_low_fan.py and
case-a-low-fan-octa.json; optimize_case_a_lowfan.py and
case-a-lowfan-optimized.json; check_prism_double_high.py (1623 double-high
samples, no failure); prism_caps_probe.py (250356 cap-pair samples, no
failure); check_prism_one_high.py found a numerical failure of the stronger
one-sharp-end version. It is now exactly verified in prism-one-sharp-
failure.certificate.json: end 5 is sharp, end 2 is not, and B/D overlap.
The same solid has a separately certified star(3)+25 repair, accepted by
the older high-source theorem. This refutes only the one-end extension. The last two positive searches do not prove universality.

Continue useful theoretical work and exact verification until the deadline.
The local-file browser denial remains respected; UI VM tests pass, and the
new SVG was rendered and visually inspected. No browser access is claimed.

---

# Current continuation: the last two original-face types

12 September 2026. The user asked to apply the octahedron rule to the last
two types, classify its failures, and attack those cases. Work stayed on
codex/lemma-f-continuation. Full types remain 5/7; neither remaining type
is claimed complete. New written proofs await independent mathematical review.

## New proved sufficient rule

Read ORIGINAL_EDGE_RULE.md. For an original degree-four source v, its
opposite w, and an original fifth edge wc, use the equator (c,a,d,b).
The new sufficient predicates are:

- kappa_w<=pi;
- 2*kappa_c+kappa_w>=pi;
- kappa_a+kappa_c+2*kappa_w>=pi and its b version;
- kappa_v+kappa_a+kappa_d>=pi and kappa_v+kappa_d+kappa_b>=pi;
- kappa_c+kappa_w>=pi-kappa_v/2.

Their proof directly audits L, the equal-length finite-cut exclusion,
Case A's no-wrap bounds, the small-fan angle contradiction, and the
surviving boundary-entry reduction. No source or slit ranking is required.
All displayed equalities are included. Flat original-face diagonals remain
uncut, using the previous audit.

If c>=pi and w<=pi, all except the two no-wrap sums are automatic. Even
when those sums fail, only the two opposite-petal Case A branches can
remain. Actual weaker apex-angle inequalities can replace the sums;
Case B is already safe. This is the next focused geometric target.
Configurations with no such original sharp-slit/low-fan candidate remain
separate, e.g. the prism with both possible fan vertices 2 and 5 sharp.
Do not call a failed sufficient inequality a positive-area overlap.

## Exact new positive and negative results

original_edge_rule.py verifies the sufficient predicates with rational
intervals, including careful unwrapped sum/half-angle comparisons.
original_edge_examples.py builds four positive certificates (points plus
independent ten-/nine-parameter boxes). Every original degree-four source
is below pi and some degree-three vertex is above pi throughout each,
so all old source conditions fail. All original face pairs replay separately.

There are also exact counterexamples to the deterministic adaptation:
choose the sharpest original degree-four source, then the sharpest allowed
fifth-cut endpoint. Both strict rankings and real overlap are verified.
Same-coordinate repairs have separate all-pairs certificates. Minus chooses
source 5/fan 2/slit 1; prism chooses source 1/fan 5/slit 2. These do not
refute the union of the 14 minus-edge or 6 prism star candidates, much
less unfoldability. Saved files begin results/original-rule-.

The numerical probe preserves original faces using integer affine and
positive projective maps of fixed seeds. It is biased and not exhaustive.
At 5,000 samples each (seed6091201), old/extra/newly-unresolved counts are
3925/396/679 minus and 2610/930/1460 prism. Every unresolved sample had a
numerically successful original star candidate. Greedy failures within
the unresolved sets: 67 and 223. All 1987/2219 additional predicate-passing
trees checked numerically were safe. Counts are NOT coverage/proof premises.
Exact witness generation does not trust the floating geometry/rankings.

## Page and reproduction

The overview has a new #original_rule page with the proof, explicit remaining
obligations, two true-scale nets and corresponding integer-coordinate 3D
models. Both type pages and the progress panel link to it. Previous progress
entries and the separate 7/28 minus two-choice-class count are retained.
No current full-type or snapshot count was incremented.

Run python3 -m n6.original_edge_examples and
python3 -m unittest n6.tests.test_original_edge_rule.
Validation: all 236 n6 tests pass (77.981 seconds); navigation, progress,
minus-edge UI, and all 172 rendered deployment evidence links pass. The
changes are saved locally; no push or live deployment was requested this turn.
SVG source: original_edge_figure.py; plot rendering is illustration only.
The local-file browser denial remains respected: no live-browser access
or browser visual verification is claimed. The SVG was visually inspected.

An untracked lean_statement/ directory appeared during this work, along
with the two previously untracked PDFs. It was not created by this task;
do not stage, edit, or remove it as part of this continuation.

---

# Current continuation: flat auxiliary hinges and the weighted slit threshold

11 September 2026, end of the authorized two-hour continuation. Branch
codex/lemma-f-continuation; local commits only, no Git push this turn.
Earlier checkpoints: 7da9b0d complete selected octahedron proof; 5a2d107
strict-low nonsimplicial families; 6461160 conditional low far theorem plus
exact H-local failure. The new material below follows those checkpoints.
All universal results are written research proofs with dependency audits,
awaiting independent mathematical review; none is machine-checked in full.

[OCTA_SLIT_THRESHOLD.md](OCTA_SLIT_THRESHOLD.md) replaces R by
2*kappa_c+kappa_w>=pi. It gives a safe whole octahedral net if source>=pi
or all six curvatures<=pi; therefore under H it always applies whenever
that threshold holds. Equality is included. The L cut-edge separator needs
only this weighted bound. In the high branch the hexagon contradiction uses
kappa_c+kappa_w-nu_m >= (kappa_v+kappa_w-pi)/2 > 0.
The low branch uses LOW_CURVATURE_FAR_REDUCTION.md after L is supplied.
A maximum equator choice always passes strictly by Gauss--Bonnet, but other
slits can pass too. Four non-R point/18-coordinate-domain examples have
independent all-28 checks. A synthetic exact phase test exercises threshold
equality without pretending the prescribed phases are a realized solid.
The low-local-failure solid has three threshold-passing safe slits and one
threshold-failing slit with exactly two local overlaps and six safe far pairs.

[OCTA_FLAT_HINGES.md](OCTA_FLAT_HINGES.md) audits the same proof for a convex
surface triangulated with the octahedron graph, allowing flat auxiliary
edges but requiring six genuine vertices and nondegenerate triangles.
The only stronger 3D premise needing attention was the opposite direction's
strict interiority in a spherical link. The closed-link lemma proves the
same strict bounds: perimeter Gamma>2*distance(a,q), and after removing
an incident side of length omega, Gamma-omega>distance(a,q). Extend a-q
to boundary c and use the two boundary paths; both cannot be the unique
shortest arc because the link has positive area. For the one-sided bound,
choose c on the retained path; its positive tail to b gives strictness,
or c=b leaves a nongeodesic retained boundary path. Flat side subdivisions
do not change this argument. All other proof steps need positive curvature,
nondegenerate triangles, planar wedge geometry, and the already retained
local premises, not strict folding across every triangulation edge.

Consequences for original polygonal facets:
- Both nonsimplicial types now unfold when every curvature<=pi, INCLUDING
  equality. Use the same four A-source candidates in the minus type and
  six prism candidates. At allowed R ties each tied net works directly.
  The earlier strict perturbation proof remains preserved as history.
- Any original degree-four source with curvature>=pi and an ORIGINAL
  fifth edge wc satisfying 2*kappa_c+kappa_w>=pi gives a safe fixed net.
  This includes equality in both tests, without a limiting perturbation.
- The whole-type count remains 5/7. The two unresolved types now require
  maximum curvature STRICTLY above pi and failure of the new sufficient
  original-tree criteria. Failure of a sufficient criterion is not overlap.

Exact checker flat_octahedron.py keeps polycert's original strict-polygon
hull checks; it does NOT weaken the geometry verifier to accept non-strict
triangular hulls. It checks octahedral completion, original candidates,
polygonal curvature, and the written theorem's conditions. The pi recognizer
uses exact rational squared cosines for a finite set of known angles; three
60-degree incident angles give exactly pi. Unresolved signs remain rejected.
There are 14 original degree-four star candidates in the minus-edge type
when all four degree-four sources are allowed, versus four at the fixed
A source used by the all-low existence rule; prism has six total.

Exact boundary examples:
- Minus points A=(10,10,0), B=(10,0,10), C=(0,0,0), D=(20,10,10),
  P=(0,10,10), Q=(10,15,15), original MINUS_FACES reversed: kappa_C=pi.
- Prism points (0,0,0),(5,5,0),(5,0,5),(0,5,5),(6,10,6),(6,5,11),
  original PRISM_FACES reversed: kappa_0=pi.
All other curvatures are below pi. Independent full-original-face checks
pass on both. Higher-curvature examples apply positive-definite affine
stretches I+3*a*a^T to the earlier low examples: a=(1,1,-1) for minus,
a=(0,1,-1) for prism. The full ten-/nine-parameter neighborhoods of
half-width 1/1000 pass using exact affine interval arithmetic.

The overview has F_slit_threshold and nonsimp_flat pages, a true-scale
local-overlap figure, failed/repaired 3D cut choices, both pi-boundary
polygonal models, and updated proved/open tables. Two stale figure captions
were corrected; the dated investigation bodies and history remain retained.

Validation at this checkpoint: all 232 mathematical-code tests pass. The
three overview tests pass, and all 164 rendered evidence links resolve in
the staged deployment package. The new overlap SVG was rendered and
visually checked; no actual browser inspection is claimed.

Next work:
1. Independent line-by-line review of the complete selected proof and the
   closed-link/flat-hinge extension. Do not treat successful exact examples
   as proof of those universal geometric steps.
2. Original every-slit F: only 2*kappa_c+kappa_w<pi can remain under H;
   in the all-low branch a local pair must also overlap. Such local failures
   exist (see low_local_failure.py), but its far pairs are all safe.
3. Higher-curvature original-edge types outside the new fixed-tree tests:
   especially a sharp original degree-three vertex, or an eligible high
   source whose only threshold-passing fifth edge is artificial. Do not
   silently cut an added diagonal. The older P/Q two-choice conjecture
   remains separate, with 7/28 whole classes excluded, not a full proof.

# Previous continuation: low-curvature every-slit reduction and a real local failure

11 September 2026. New written conditional theorem:
[LOW_CURVATURE_FAR_REDUCTION.md](LOW_CURVATURE_FAR_REDUCTION.md).
If all six octahedral curvatures<=pi, any source/slit with all three local
pairs safe has every far pair safe and hence the whole net safe. No H or R.
The original every-slit Lemma F remains open at slits with a local failure;
this condition is not automatically supplied by L at a different slit.

Proof: through-fan L needs only fan curvature<=pi. The local premises
trap the neighboring patch for the equal-cut-length proof, excluding both
finite cut segments. The Case A no-wrap bound follows from all-low total
curvature. The base-cone branch needs no ranking. In the small-fan branch,
the closed-curve hexagon identity would force nu_m>kappa_a+kappa_c+kappa_w,
but the latter sum>=pi>nu_m. Boundary contacts without R require care:
M may touch the opposite slit segment; shrink the auxiliary triangle acM
slightly into itself, apply the angle identity to the simple region, then
pass to the limit. The positive angle at the chosen overlap point remains
strict. This is a planar diagram perturbation, not a realizability claim.

Exact modules low_far.py and low_far_examples.py check just the three
local separators and all-low hypothesis on a point and full 18-coordinate
box +/-1/10000 where both H and R strictly fail. Independent all-28
certificates agree. Missing/duplicate/wrong/reversed witnesses, high or
uncertain curvature bounds, and a genuinely overlapping local pair are
rejected. Equality at pi is accepted when certified.

Crucially, the local-failure branch is nonempty even under H. The exact
integer example in low_local_failure.py has source 5, opposite 3, ring
(0,4,1,2), slit 2. All curvatures<pi; source 5 is sharpest. Exactly two
local pairs overlap, (3,4) and (3,7), and all other 26 pairs are safe,
including all six far pairs. Thus this refutes all-slits WHOLE-NET safety
under H, not the far-only Lemma F. Changing to R gives an independent
all-28 safe net. All claims in this example are checked exactly; the
floating-point affine optimization merely found its coordinates.

The selected octahedral proof remains in 7da9b0d; the two strictly-low
nonsimplicial theorems are in 5a2d107. The whole-type tally stays 5/7.
The web overview now separates the conditional low-curvature far theorem
from the still-open every-slit statement and retains the earlier history.
No Git push has been made this turn. All new universal proofs await
independent mathematical review and are not machine-checked proofs.

Next mathematical lead (not yet promoted): replace R by the weaker
weighted threshold 2*kappa_c+kappa_w>=pi. The L slit-edge separator only
needs that inequality (equality gives a strict angle via rho<pi-kappa_c).
Through-fan L holds when source>=pi or all curvatures<=pi. In the high
source branch the small-fan contradiction follows from
kappa_c+kappa_w-nu_m >= (kappa_v+kappa_w-pi)/2 > 0.
In the all-low branch use the new conditional theorem. This would prove
the whole net at every slit passing the weighted threshold, without R.
Check it in full before claiming it, particularly equality and no-wrap.
It may help the remaining nonsimplicial original-edge high-curvature cases.

# Previous continuation: source freedom and both low-curvature nonsimplicial types

11 September 2026. The selected octahedron proof is saved in commit 7da9b0d
on codex/lemma-f-continuation. A subsequent hypothesis audit gives
[OCTA_SOURCE_CHOICE.md](OCTA_SOURCE_CHOICE.md): keep the maximum-curvature
equator slit R, but allow any source if all six curvatures<=pi. Alternatively,
any source of curvature>=pi works, even if not globally sharpest.
Every former use of H is checked: through-fan L already works when the
source>=pi or fan<=pi; Case A no-wrap is immediate at source>=pi, while
in the all-low branch kappa_u+kappa_u'>=pi-kappa_v by Gauss--Bonnet.
The other dependencies use R or the relevant curvature condition, not H.

This proves [NONSIMPLICIAL_LOW_CURVATURE.md](NONSIMPLICIAL_LOW_CURVATURE.md):
both remaining original-facet types unfold if every vertex curvature is
strictly below pi. The full n=6 problem therefore remains only in those two
types with maximum curvature>=pi, including equality. Whole types stay 5/7;
the original every-slit Lemma F is also still open. All new results are
written research proofs awaiting independent mathematical review.

Minus-edge labels: original quad A-C-B-D, missing diagonal CD. The third
octahedral opposite pair is A,B. Fix source A; every fifth edge from B is
original. In each nearby strict all-low octahedron, R selects one of four
safe trees, all avoiding CD. Take a constant-tree subsequence. This gives
existence among four extensions of star(A), also among limiting R maxima.
Ties in the limiting polygonal solid require retaining all possible maxima;
do not claim every tied tree succeeds. The older P/Q two-tree conjecture
is separate and retains its 7/28 proved class count.

Prism labels follow families.PRISM_FACES. The only octahedral completion
adds 05 and 24. Original degree-four sources 1 and 3 have opposites 5 and 2,
with forbidden fifth-edge endpoints 0 and 4 respectively. Both endpoints
belong to both equators. If source 1 uniquely prefers forbidden 0, then
kappa_0>kappa_4, so source 3 cannot prefer forbidden 4. Ties leave an allowed
choice. Thus one of six original star-plus-edge trees is safe in every
nearby all-low refinement. Neither artificial diagonal is ever cut.

Refinements are explicit: lift C outward from the minus-edge quad; lift
vertex 0 outward from prism quad (0,3,5,2) and vertex 4 outward from
quad (1,2,5,4). Each prism lifted vertex is absent from the other quad,
so the required diagonal signs are independent. All other strict support
inequalities persist. Strict all-low curvature persists by continuity.
A fixed-tree limit merges uncut triangles back into their original quads;
positive-area overlap would persist nearby, contradiction. The equality
boundary max curvature=pi is deliberately NOT included in this extension.

Exact modules: source_choice.py, low_curvature_types.py. The latter checks
polygonal curvature and original candidates, and concludes EXISTENCE among
them; it explicitly does not certify the input tree's nonoverlap. The four
new point/region examples additionally have independent full-net polycert
checks: low-curvature-minus, minus-family (10 parameters, +/-1/1000), prism,
prism-family (9 parameters, +/-1/1000). Two source-choice examples prove
the source is strictly less sharp than its opposite, in the high and low
branches. Explicit strict octahedral refinements at two positive lift sizes
are checked in regression tests. A prism point with three 60-degree angles
at vertex 0 exercises rejection of the pi boundary/uncertainty.

Validation: all 217 mathematical-code tests pass; navigation, progress,
and prism-ordering tests pass. The overview has source-choice and nonsimp_low
pages, both polygonal 3D examples, and a separate 1/2 curvature-branch count
for each remaining type. These are named branches, not shape-space fractions.
The older history remains collapsed. No Git push has been made this turn.

Next options, not yet promoted:
1. Continue the every-slit F question. In the all-low regime, assuming the
   three local pairs safe may suffice without R: use the same cut containment
   and chord proof, and replace R in the hexagon contradiction by
   kappa_a+kappa_c+kappa_w>=pi>nu_m. Check this complete conditional reduction.
   Thus a possible far overlap would require a local failure at that slit.
2. Push the remaining high-curvature nonsimplicial branch. The limit argument
   also works for a fixed eligible source with curvature strictly above pi,
   provided a maximum equator choice avoids artificial cuts throughout nearby
   refinements. For minus-edge, either A or B above pi suffices. For prism,
   both degree-four sources above pi suffice via the cross-ranking argument.
   With only one high source, a strict curvature advantage of an allowed slit
   over its forbidden slit suffices. These additional corollaries are not yet
   written or added to the current page. Equality still requires separate care.

# Previous continuation: complete selected octahedron proof

11 September 2026. [LEMMA_F_CHORD.md](LEMMA_F_CHORD.md) completes the
low-curvature branch of the H/R selected-net rule. Combined with the
high-curvature [pole-angle proof](LEMMA_F_POLE_ANGLE.md), it gives a complete
written proof for every convex octahedron: 28/28 face pairs, all five possible
patch regimes, equality and tied selections included. This is a research
proof with a recorded dependency audit; independent mathematical review and
formal verification have not been performed. Numerical experiments are not
premises. The original every-slit Lemma F and both nonsimplicial remaining
six-vertex types remain open. The whole-type tally is now 5/7.

For the low branch, H and kappa_v<=pi imply all six curvatures<=pi. A supposed
finite-cut crossing traps the neighboring patch Q_m inside triangle(w,a,p).
At a, its apex M and the entering petal's apex P have equal radius s=|av|.
The gap from aM to aP is kappa_a. Put theta=angle_a(Q_m) and
delta=omega_m+kappa_w. Entry before P while M stays on a's side of the cut
line forces 2*theta+2*delta+kappa_a<pi, by the sine-difference formula.
But the neighboring blue-face angle gamma at slit c gives

    2*theta+2*delta+kappa_a
      >= kappa_a+kappa_c+2*kappa_w+2*mu > pi,

where mu=angle_a(V_m)>0. Indeed, its complementary three vertices have
curvature<=3*pi, so kappa_a+kappa_c+kappa_w>=pi. This is the contradiction.
An explicit positive-sum identity and orientation audit are in the proof.
Reflection handles the other finite cut at the same R-selected slit.

The whole-net dependency audit rechecks Case A's apex cones/no-wrap bound,
the exhaustive base-cone partition, and the Case B auxiliary closed curve.
Section 5 added to LEMMA_L_PROOF.md proves strict separation of a closed
flank petal from the opposite closed finite slit edge, even at equality of
its angular extension with the gap. This removes a possible boundary pinch
when taking the six-sided region. Do not use the refuted unrestricted
far-fan implication; only its surviving interior-target version is needed.

Exact replays: `python3 -m n6.selected_octahedron_examples`. Nine coordinate
domains pass independent all-28-pair certificates. New examples include a
point with exactly pi source curvature, an 18-coordinate box crossing that
threshold, and the regular octahedron with H/R ties. The exact equality
shortcut compares signed squared cosines of incident angle multisets only
at rational points; it never treats interval uncertainty as equality.
The checker accepts unresolved source comparison with pi because both
branches and equality have written proofs, after H/R and geometry pass.

Next research: the every-slit Lemma F. R is used through Lemma L's local
exclusions in the containment and the six-sided-region bound. A different
slit need not inherit those premises. Study what a local failure forces
before attempting to transfer the finite-cut proof. Another possible
generalization is that all curvatures<=pi may allow any source with R:
through-fan L works since kappa_w<=pi, and Case A's no-wrap bound follows
from the other three curvatures<=pi. This weakening is not yet promoted.

The overview has a new F_chord page, proof schematic, exact-boundary 3D model,
and explicit current/historical scopes. Earlier enumeration reports retain
their 2/47 count as history; all 49 simultaneous-failure classes are now
excluded by the selected theorem, not a new enumerator. Tests currently:
207 mathematical-code tests pass; nine independent exact replays pass.
The local branch is codex/lemma-f-continuation. No Git push is implied by
continuing the proof. Do not stage the two untracked user thesis PDFs.

# Previous continuation: the high-curvature selected-net theorem

11 September 2026. [LEMMA_F_POLE_ANGLE.md](LEMMA_F_POLE_ANGLE.md) proves the
whole selected net when the globally sharpest source has curvature >=pi.
Keep H and R: four cuts at a sharpest v, fifth at a sharpest equator u_k.
This includes equality and all patch patterns. It is a geometric proof,
not a numerical inference; the full selected rule, every-slit Lemma F,
general octahedron, and n=6 remain open.

For a hypothetical last-cut crossing by V_i, i=k+1, take p just inside
that petal and before the slit endpoint b. At a=u_i, |ap|<s=|av|. Lemma L
and shared-vertex separation trap the entire neighboring Q_m, m=k, inside
T=triangle(w,a,p). Its developed apex M has |aM|=s. If angle(a,M,w)<=pi/2,
projection along aM bounds the whole triangle strictly before M, except
possibly w itself. M is not w. This contradicts containment. No opposite
petal or far-fan nonoverlap is assumed in that trap.

The corner of Q_m at a is <pi because Q_i is reflex there. Its developed
pole distance t=|wM| is at least the original |wv|, by the spherical
triangle inequality at a and cosine law. Thus original angle(w,v,a)<=pi/2
implies the needed flat angle. The link bound 2*angle(w,v,a)<2*pi-kappa_v
makes every applicable angle acute when kappa_v>=pi. Reflection handles
the other target. The existing cut-segment equivalence completes the net.

The low-curvature branch has a second sufficient test. An obtuse original
angle implies r=|aw|>s=|av|. The circle centered at a of radius s lies in
the half-plane facing a from w; backward reach is <pi/2. Therefore
delta=omega_m+kappa_w>=pi/2 excludes that cut direction. For delta<pi/2,
s<=r*sin(delta) is a sharper sufficient test. The checker currently uses
the quarter-turn version, not this sharper sine test.

Next proof target: an uncovered selected shape needs 2*pi/3<=kappa_v<pi,
pi/2<beta=angle(w,v,a)<pi-kappa_v/2<=2*pi/3, the neighboring flat pole
angle still obtuse, delta<pi/2, and s>r*sin(delta). Prove that this joint
configuration is impossible or control finite entry before the endpoint.
For three common-direction bad patches only one remote cut test is active.

Do not silently exchange poles: although one angle in triangle v,w,a is
nonobtuse, the replacement source can fail H. Lemma L's through-fan bound
may still work at both poles below pi, but Case A's no-wrap bound in the
whole-net reduction is not thereby inherited. This was a tempting invalid
shortcut during this investigation.

Exact code: `far_projection.py`, `far_projection_examples.py`. Four domains
pass the hypothesis checker and independent all-28 certificates: a high
three-common-direction point, a low-curvature point, its 18-coordinate box
of half-width 1/10000, and a low-curvature point with both pole angles
obtuse but repaired by the circle argument. Source selection is normalized
from the older local_gate metadata for the first point; its earlier
selection metadata had preceded a change of slit.

Exploratory searches found real obtuse original-angle configurations at the
selected dangerous remote patch. The saved small-integer obtuse example
proves that the original and flat nonobtuse hypotheses are not universal.
The searched obtuse points had wide enough gaps for the circle repair.
Searches directed at simultaneous obtuse beta and acute delta found no
candidate; this does not prove their joint domain empty. The necessary
geometric restrictions, not a measured coverage percentage, guide the
next step. Universal pairs remain 22/28; within kappa_v>=pi they are 28/28.

# Previous continuation: cut-segment equivalence and the only remaining route

11 September 2026 JST. [LEMMA_F_CUT_RAYS.md](LEMMA_F_CUT_RAYS.md) proves
that the selected H/R net is safe iff the two open radial cut segments
miss the interiors of V_(k+2) and V_(k+1), respectively. The earlier
hexagon proof only used its fan-pair assumption to exclude a cut-edge
crossing. This weaker assumption suffices; a boundary-crossing argument
then recovers that fan-pair separation.

The through-fan part of Lemma L works at EVERY slit under the pole
comparison. Reindexing it bounds F_(k+1) strictly below the remaining
forward fan angles. Thus V_(k+1) can reach its target cut ray only backwards
through the slit gap, requiring B_(k+1)>omega_k+kappa_w. Reflection requires
F_(k+2)>omega_(k-1)+kappa_w for the other petal. The opposite weak
inequalities suffice for the whole selected net, with equality allowed.

New subcases: convex or wrong-direction remote patches are safe even in
small-angle Case B with the slit endpoint past X. If all inward patches
lean backward, the first-cut test is automatic and only V_(k+1) against
the last finite cut remains; reflect for all-forward. This is useful in
the remaining three-patch common-direction family, but does not settle it.
The general angular inequalities are a candidate lemma, not yet proved.
If they fail, finite-edge radial separation can still succeed.

`cut_rays.py` rigorously clips three necessary linear inequalities in the
ray parameter using outward rational bounds. It distinguishes finite-edge
safety, infinite-ray safety, and unresolved intervals. Four saved domains
pass both ray checks and agree with independent all-28 certificates.
The apex-entry 11-coordinate box also passes the new general direction
corollary. Regression tests include the historical H-failing cut crossing,
true finite-only separation, touching, and widened interval uncertainty.

Next: attack B_(k+1)<=omega_k+kappa_w under H/R (its reflected inequality
is the other test). If false, certify a rational witness before changing
the claim, and study its intersection parameter relative to the endpoint.
Keep checking the full far-fan angle range, not only small-angle Case B.
Unconditional pair count stays 22/28; the selected-net claim, full Lemma F,
full octahedron, and n=6 remain open. No numerical observation is a premise
of the written proofs.

# Previous continuation: Lemma F reduced to two cut-side fan checks

11 September 2026 JST. [LEMMA_F_CUT_REDUCTION.md](LEMMA_F_CUT_REDUCTION.md)
proves a new reduction under H and R. In Z_k retain V_(k+2)/W_k and
V_(k+1)/W_(k-1). If these two pairs are safe, the whole net is safe.
Opposite petals are now consequences of the retained checks, then the
surviving interior-fan reduction disposes of the two interior targets.

For the last triple, put a=u_i, b=the last slit copy, and p inside a
hypothetical opposite-petal overlap. Gamma=a,p,b,w,a is simple: the retained
cut-side check excludes ap/bw crossing and L excludes bp/wa crossing.
All four vertices are below the middle base, even if a or b passes X.
The inside must face the fourth patch; otherwise the above-base middle
petal would be inside a below-base curve. Shared vertices and L put the
whole fourth patch inside. Remove it to get the historical hexagon.
Its angle sum requires nu_m>kappa_back, contradicting R plus the cone bound.
Reflection supplies the other opposite pair without changing the slit.

The same proof settles the small-angle case when the slit-side far vertex
is at or before X: the other outer edge separates the blue-orange pair.
Unlike the historical two-apex lemma, the nonslit far vertex may pass X.
The slit-side-past-X branch remains open; this position is necessary for
failure of that sufficient test, not sufficient for overlap. The two fan
checks also need study outside the small-angle branch.

Next: prove these two actual blue-orange checks, possibly by controlling
entry across their cut radial edge. Do not return to individual-apex
exclusion (refuted), nor assume an interior-hinge argument applies at a cut.
The universal pair count stays 22/28, the 49-class record stays 2/47, and the
full octahedron and n=6 remain open. Original Lemma F asks for all slits under
H; the new reduction uses the selected slit under H and R.

`n6/far_pairs.py` checks H/R, the hull/cuts, and precisely two exact edge
separators. Four saved examples, including 11- and 18-coordinate boxes,
agree with independent all-28 certificates. The geometric reduction is a
written proof dependency, not a numerical inference or formal verification.

# Previous continuation: Lemma L is proved

11 September 2026 JST. [LEMMA_L_PROOF.md](LEMMA_L_PROOF.md) is a complete
geometric proof of all three local pairs. It needs only kappa_v>=kappa_w
and a maximum-curvature equator slit, so it includes the original hypotheses.
The full octahedron and n=6 remain open; **do not claim a whole net from L**.

First, [LEMMA_L_SMALL_SUM.md](LEMMA_L_SMALL_SUM.md) closed the entire
sigma<=pi branch. If one petal reaches across the slit, extend its cut edge
vu. The slit ranking gives 2*kappa_u+kappa_w>pi; the other u copy and its
whole patch lie strictly on the other side of the line. This handles both
remaining pairs at once, including the older radial obstruction.

The missing through-fan route is now excluded for every slit under the pole
curvature comparison. The spherical link at a pole is a convex polygon with
perimeter equal to its total face angle; the direction of the other pole is
strictly interior. Boundary paths bound the distance from the slit direction
to that interior direction. For the original triangle wuv, if its angle beta
at v is nonobtuse, flattening an inward-away patch increases the pole distance
and decreases its angle at w. The link bounds then separate one or both
extending flanks. If beta is obtuse, the link at v forces kappa_v<pi, hence
kappa_w<pi. The fan spans more than pi while each extending patch subtends
less than pi/2, again giving separation. The proof includes all equalities.

Current status: **3/3 universal local obligations; 22/28 pairs of the selected
net safe**. The remaining two universal objectives are the opposite-petal
small-angle branch and the cut-side far-fan pairs. Once opposite-petal safety
is proved at this same slit, the interior-fan reduction is applicable.
The unrecounted 49-class four-opening enumeration stays a separate conservative
2-excluded/47-open record. Four of five whole patch regimes remain settled.

Next: work on Lemma F at the maximum-curvature slit, where L is now available.
Do not silently carry the slit ranking to an angle-safe opening chosen by the
switching theorem; the openings need not coincide. Do not revive the refuted
unrestricted far-fan reduction. Numerical searches are not proof premises.

Exact hypothesis checks: `python3 -m n6.local_lemma CERTIFICATE`. The saved
large-sum and radial-family reports illustrate the complete theorem. The
small-sum separator is independently checked by `python3 -m n6.local_small_sum
CERTIFICATE --cut-separator`. The webpage includes the full case table and
preserves the earlier radial picture and proof history.

# Previous continuation: direct progress on Lemma L

10 September 2026 JST / 9 September UTC.
[LEMMA_L_CURVATURE_GATE.md](LEMMA_L_CURVATURE_GATE.md) proves a new local
case split without either curvature ranking. Set sigma=kappa_u+kappa_w
at the slit. If sigma<=pi, the first and last patch cones cannot meet
through the intervening fan. If sigma>=pi they cannot meet across the slit.
At equality all three local pairs are safe. The proof adds the two pole
views of each flank patch, using their shared reflex excess; it includes
straight patch corners and the equality boundary.

Further local families follow: no inward slit corner in the small-sum
half; no extension toward the fan interior in the large-sum half; or both
flanks inward away from the slit with sigma<=2*pi. If sigma<pi and a slit
corner is inward, only its petal against the other petal and other fan face
remain. The other mixed pair is proved safe. This narrows the distance
problem to one petal against the opposite patch, but does not solve it.

The old three-chain-uncovered shape has all three local pairs proved at
the maximum-curvature equator slit; this is a different fifth cut from its
previous illustration. The saved point also passes an independent all-pairs
certificate. A second point illustrates the both-away family with pi<sigma<2*pi.

The exact radial example now has an 18-coordinate box: independently vary
every coordinate by ±1/10000. Both maximum-curvature selections and angular
intrusion persist. Radial clipping proves a distance ratio of at least 6/5
against the opposite fan edge on every shared ray, and separate certificates
prove all 28 face pairs safe. This is a certified coordinate family, not a
universal radial inequality. Rebuild with `python3 -m n6.local_gate_examples`.

Next: in sigma<pi, prove simultaneous distance separation of the offending
petal from both faces of the other patch, using H and the slit ranking.
Treat the through-fan route separately for sigma>pi. The gate does not use
those rankings, so they remain extra information for this next step.

The full Lemma L, octahedron, and n=6 remain open. Counts stay 0/3 universal
local obligations, 4/5 complete patch regimes, and 2 excluded / 47 open
fixed-source classes. The proof is geometric; numerical searches and linear
angle relaxations are not used as proofs or as geometric counterexamples.

# Previous continuation: a middle-patch switch proves three-chain subfamilies

10 September 2026 JST / 9 September UTC. [OCTA_THREE_CHAIN.md](OCTA_THREE_CHAIN.md)
proves an original-edge unfolding under H for three bad patches with a
common direction when the middle patch satisfies explicit angle bounds.
For forward Q0,Q1,Q2, try both four-cut poles and fifth endpoints u2,u3.

The simple condition is rho_1<=min(kappa_v,kappa_w). The stronger version
requires the middle extension at each pole to fit that pole's gap, and
rho_1<=kappa_(u1)+min(kappa_v,kappa_w). Start at a pole whose individual
extensions fit its gap. If the two selected openings both fail their
sufficient tests there, the shared-excess identities force the u2 opening
to pass at the other pole. This checks whole patches including slit-side
fan triangles, without the refuted far-fan lemma.

The `three-chain-switch` example strictly fails the simple threshold but
passes the stronger theorem. `three-chain-family` varies all 18 coordinates
independently by ±1/100 and certifies one fixed net throughout. Both point
examples and the box fail the old weighted-curvature test for all three
opposite pairs. The old illustrated `patch-budget-three-same` example is
now covered even by the simple threshold.

The rest splits into two disjoint branches: a middle extension exceeds a
pole gap, or both fit but the combined excess bound fails. The former is
nonempty: the exact `three-chain-uncovered` example (reusing the old sector
radial-failure coordinates) has that behavior and a separately certified
successful net. No actual octahedron in the second branch was established.

Next: exploit radial separation when the middle cone crosses its gap, or
prove an alternative opposite pair enters a covered regime. The temporary
linear relaxations permit the obstruction but do not impose full metric
realization. Numerical optimizations of the second branch approached its
boundary without furnishing a geometric example; this is not an exclusion
proof. Another exploratory search found three common directions with both
poles below pi without H; retaining H did not find such a shape. Neither
search establishes a universal curvature threshold.

The full octahedron remains open. Counts stay 4 of 5 complete patch regimes
(the fifth is partly proved), and 2 excluded / 47 open fixed-source classes.
Use `python3 -m n6.three_chain_examples` to rebuild the exact evidence and
`python3 -m n6.three_chain ... --analyze` for a condition audit. The main
proof is written mathematics, not a numerical or solver conclusion.

The earlier entries below preserve the successive proof states.

# Previous continuation: a shared lean budget closes the two-patch cases

10 September 2026 JST / 9 September UTC. [OCTA_PATCH_BUDGET.md](OCTA_PATCH_BUDGET.md)
proves existence under H for both two-patch arrangements and three bad
patches with mixed directions. Together with the earlier cases, four of
five coarse patch regimes are proved, with the fifth partly settled.
**The remaining pattern is three consecutive bad patches all leaning in
the same direction.** The original fixed-source count is unchanged:
2 excluded, 47 open; the new proofs can exchange the four-cut pole.

For each bad patch, the extensions seen from the two poles add to its
reflex excess. When all curvatures are below pi, the total extensions at
both poles are smaller than the combined fan gaps, so one pole supplies
an adequate total gap. A pole of curvature at least pi supplies the
complementary case. Identities across intervening convex patches finish
the opposite-patch and mixed-three-patch cases. All proofs use direct
whole-patch cone separation, not the refuted far-fan lemma.

The new `n6.patch_budget` checker computes all six sufficient angular tests
for the eight two-pole trees and distinguishes prescribed theorem choices.
Exact examples cover the new direction cases, and an 18-coordinate region
has both poles below pi with one fixed net certified throughout. The
common-direction three-patch example is explicitly classified as an open
regime despite its independently certified individual net.

Next target: the all-forward (or reflected all-backward) three-patch chain.
The total budget alone does not stop an extension entering a later patch
inside the fan. The identity rho_i - (omega_(i+1)+nu_(i+1)) =
f_(i+1)-pi-kappa_(u_(i+1)) now carries another reflex excess when the next
patch is bad. Coordinate the resulting chain across both pole views; a
new geometric step is needed. A [20,000-shape exploratory survey](results/patch-budget-survey.json)
classified every sample and checked angular choices for the 4,351 samples
with opposite bad patches or three bad patches. All of those had a successful
choice, including 28 common-direction three-patch shapes; this is numerical
evidence only and proves no further case. The written proofs above do not
depend on that survey. Reproduce it with:

```sh
durer_small_n/.venv/bin/python -m n6.patch_budget_probe --samples 20000 --seed 6091002 --output /tmp/patch-budget-survey.json
```

The earlier entries below preserve the successive proof states.

# Continuation: the one-patch family has a two-pole proof

9 September 2026 UTC / 10 September JST. [OCTA_ONE_PATCH.md](OCTA_ONE_PATCH.md)
proves existence for the entire one-nonconvex-patch family when either pole
is globally sharpest. Choose the equator vertex opposite the bad patch's
convex corner; use it for the fifth edge in two trees, with the four cuts
at either pole. If both whole-patch cone tests failed, both poles would
have curvature below pi, while the equator vertex opposite the reflex
corner would have curvature above pi. This contradicts sharpness.

The old fixed sharpest-source rule remains open. This proof can change
which pole carries the four cuts, so the original failure-class count
stays **2 excluded, 47 open**. The proof bypasses the refuted far-fan lemma.

[OCTA_HALF_FAN.md](OCTA_HALF_FAN.md) also gives a direct rule for two adjacent
bad patches when either pole has curvature at least pi. All three possible
lean patterns are proved. Exact examples and an 18-coordinate neighborhood
have separate hypothesis and all-28-pair net certificates. These families
may overlap the previous curvature and sector criteria; no global coverage
fraction is asserted.

The next three full regimes are two adjacent bad patches (especially both
poles below pi), two opposite bad patches, and three bad patches. The new
one-patch argument suggests looking for a similar contradiction coordinating
more than one pole choice. Preserve the distinction between this existence
strategy and the stronger fixed-source four-choice conjecture.

The overview has new proof pages, paired nets and 3D cut models, and a
retained progress entry. The following audit remains valid; its older
one-patch wording refers to the withdrawn fixed-source proof.

# Current timed-session audit, 9 September 2026

**Read [HINGE_AUDIT.md](HINGE_AUDIT.md) before the earlier entries below.**
An exact convex octahedron has one far-fan overlap and all other 27 pairs
safe. The source is not sharpest, so H-specific claims remain open; the
old unrestricted conditional reduction is refuted. Restore **49 original
classes, 2 excluded and 47 open**. Reopen the one-nonconvex-patch whole-net
claim. Its local and opposite-petal repair steps survive, as do all-convex
patches and the two independent switching implications.

The restricted interior-fan lemma is now also proved in the audit note: once local and opposite-petal pairs are safe, only the two slit-side far-fan pairs remain. This leaves the conservative original 49-class count unchanged.

The strongest new positive result is unchanged: **every centrally symmetric
octahedron unfolds**, by the opposite-pair curvature theorem. The new
[local radial-cover theorem](OCTA_RADIAL_COVER.md) combines exact chord and
face-angle bounds. It certifies a fifteen-parameter asymmetric family that
failed the earlier criteria. A second integer example exactly fails the
stronger criterion while its chosen net succeeds.

A further elementary reduction in [OCTA_REMAINING_FAMILIES.md](OCTA_REMAINING_FAMILIES.md) proves that, outside the curvature-pair family, all vertices of curvature at least 120 degrees lie on one triangular face. That face carries more than 360 degrees of total curvature. The three possible threshold patterns (one vertex, one edge, the whole face) are all open in full. This is a proved necessary condition, not another unfolding theorem.

Earlier entries retain their then-current conclusions and counts; the audit
above supersedes the former 24-class and one-patch claims.

# Latest octahedron step: assume overlap and switch

## Further timed-session proofs: curvature pair and short edges

[OCTA_TWO_SHARP_POLES.md](OCTA_TWO_SHARP_POLES.md) proves the opposite-pair condition K+2J>=2*pi, where K>=J, and consequently **every centrally symmetric octahedron**. The proof forces a short endpoint of the shortest two-face path by omega+2*nu<=2*pi. The sector angle is automatic since K>=2*pi/3. Source cuts are at the other pole. The more general sufficient hypotheses K>=2*pi/3 and K+2J>=2*pi are supported by the exact checker.

[OCTA_SHORT_EDGES.md](OCTA_SHORT_EDGES.md) separately proves families whose strictly convex patches each have an endpoint within the pole chord radius of a >=120-degree sector vertex. Five exact examples include all patch regimes. Neither result closes the whole octahedron or another fixed-source class. The central nine-parameter certificate is only an illustration of the unbounded central-symmetry theorem.


## Timed session: convex-patch proofs (9 September 2026)

[OCTA_CONVEX_PATCHES.md](OCTA_CONVEX_PATCHES.md) proves every four-slit net works when all four flattened patches are convex, and at least one of two specified slits works when exactly one is nonconvex and H holds. Four nonconvex patches are impossible: reflex corners force strict increases of |wu|+|vu|. This also excludes original class 20. With class 49, **2 of 24 sufficient classes are excluded, 22 remain** (8 mixed, 14 local-only). Two adjacent, two opposite, and three nonconvex patches remain open. Five integer examples have exact patch and all-pairs net checks; the 5,000-shape survey is numerical only. The full octahedron theorem, L, and F remain open.

Earlier entries below retain their then-current counts.

9 September 2026. The [case analysis](OCTA_CASE_ANALYSIS.md) implements the
user's suggested contradiction/repair approach and explains its relation to
L and F. Two universal implications are proved:

- Moving the opening repairs all three old local pairs, by the shared-vertex
  fan lemma. It can introduce different overlaps elsewhere.
- Under H, the same opposite petals cannot overlap along both fan routes.
  The necessary overlap conditions S_j<pi and S_{j+2}<pi contradict the exact
  identity S_j+S_{j+2}=2*pi+curvature(w). This invokes the existing Case A and
  base-cone exclusions and includes equality boundaries.

Using the conditional hinge lemma inside the no-local-overlap branch reduces
the sufficient failure list from 49 to 24 classes. The new angle identity
excludes original class 49, leaving **23 classes** (8 mixed, 15 local-only).
The 49-to-24 change is removal of redundant obligations, not 25 exclusions.
The 24-to-23 change is a geometric exclusion. The full rule remains open.

The identity guarantees some opening with both opposite-petal pairs safe.
Local pairs need not be safe there: a numerical follow-up found 11 apparent
failures of that stronger restricted selector on the same 3,000 shapes.
Those candidates are not exactly audited, so the notes identify them only as
numerical failures. Continue studying mixed/local failure cycles, retaining
all four choices. The report checks 36 local repairs and the symbolic angle
identities and preserves original class IDs.

# Earlier priority change: the octahedron four-slit rule

9 September 2026. At the user's request, prioritize the octahedron. The new
[four-choice proposal](OCTA_FOUR_SLITS.md) retains the sharpest apex and tries
all four openings at its opposite vertex. It is a weaker target than the
existing H/R single-choice rule, using the same near-star constructions.

- Exact combinatorial reduction: 36 residual checks become 24 distinct
  relative placements, with 315 minimal simultaneous-failure covers and 49
  symmetry classes. **No new geometric class is excluded yet.**
- First target: classes 37, 40, 44, 49, each with only two bad placements.
  Class 49 is the same opposite-petal pair overlapping along both fan routes.
- Numerical pilot: 3,000 shapes, all 24 near-stars tested; every sharpest-apex
  four-tree family has a numerically clear choice. This is not a proof.
- Secondary route: the archived geodesic-sector sufficient theorem, with
  an open existence step. Retain its exact sharpest-sector radial obstruction.
- Reused the minus-edge batch development and archive two-face path routines;
  compared all 384 octahedral trees on two fixtures with independent geometry.
- The overview now puts this priority first, links the full proposal and
  saved enumeration, and preserves earlier notes and proof counts.

The old single-choice proof still has Lemma L and the small-angle
opposite-petal gap. The full octahedron and n=6 theorem remain open.

# Earlier continuation: a universal seven-class exclusion

9 September 2026. [MINUS_NEIGHBORHOOD.md](MINUS_NEIGHBORHOOD.md) applies
Pinciu's face-neighborhood theorem to one previously residual pair in each
minus-edge tree. It excludes original classes 7, 13, 18, 19, 20, 21, 22
for every convex realization. The remaining 21 classes, two-tree conjecture,
and full n=6 case remain open. The checker now validates this theorem
application, with an explicit literature dependency. Earlier notes follow.

---

# Latest continuation: minus-edge patterns

9 September 2026. [MINUS_PAIR.md](MINUS_PAIR.md) records a new two-tree
conjecture, a two-fan interpretation, exact switching examples, and a complete
16-cell certificate using one fixed tree on the same ±0.05 box. The earlier
certificate used nine trees and 409 cells. The domain is unchanged. The
universal two-tree statement remains open; 33,000 samples and 150 directed
starts are numerical evidence only. Its simultaneous-failure cases reduce
combinatorially to 28 symmetry classes, none yet excluded as a whole.

The earlier sessions are retained below.

---

# Second continuation on 9 September 2026

The overview was updated first, and the additional research hour began at
approximately 02:05 UTC. The full n=6 theorem remains open. The main new exact
result rules out a stronger intermediate claim without refuting the proposed
unfolding itself. Earlier progress is retained below.

## New exact results

- **Individual-apex exclusion is false for actual convex octahedra.** Six
  small integer-coordinate vertices satisfy H and R, strict Case B, and
  `Sigma_W+a<pi`; one outer apex and its far vertex pass into the relevant
  half-plane. The other petal remains outside, and all 28 pairs of the selected
  net are certified simple. An eleven-parameter closed box of radius `1/1000`
  has the same verified behavior. [CASE_PARTITION.md](CASE_PARTITION.md)
  gives the coordinates, orientation, figure, and exact replay commands.
  This does not settle the distinct remote-apex orientation.
- **Global metric closure is an additional necessary condition.** An exact
  intrinsic metric passes shared triangle lengths, positive curvatures, all
  six strict convex-vertex cone conditions, and H/R. Nevertheless, a complete
  five-interval certificate proves that it cannot be the original edges of
  a strictly convex octahedron. [AXIS_CLOSURE.md](AXIS_CLOSURE.md) derives the
  necessary equations and documents the verifier. No sufficiency claim is made.
- **Distance resolves the known local angular obstruction at that example.**
  On every shared ray, its petal starts at least `1217/1000` as far from w as
  the opposite fan's outer edge. Three exact inequalities establish this bound.
  [LEMMA_L.md](LEMMA_L.md) explains the clipped-triangle argument. L universally
  remains open. The closest candidate from the new coordinate search is also
  exactly certified nonoverlapping after rational reconstruction at 320 bits.
- **Prism path rules need a genuine choice.** Both quadrilateral routes at a
  fixed degree-four apex can fail. In a smaller example, the shorter route
  at the strictly sharper degree-four apex fails while the longer route gives
  a certified simple net. See [PRISM_DIAGONAL.md](PRISM_DIAGONAL.md). Neither
  example refutes the conditional reduction or the existence of an unfolding.

## Numerical exploration and unresolved queries

A reproducible coordinate optimizer retains the actual octahedron geometry,
H/R comparisons, and explicit support and azimuth guards. Ten-minute runs
made 2,112 local-search attempts and 971 joint-petal reach attempts in the
remote/slit-3 orientation. A further seven-minute run made 702 joint-reach
attempts in slit 0; neither orientation produced a candidate with positive
joint reach within these guarded searches. The saved
reports state their coordinate bounds and guards. The best local near-contact
candidate was rechecked exactly; its selected net is simple. No search absence
is treated as a theorem, and no numerical lower margin is claimed uniform.

The best joint-reach candidates are limited by the imposed support guard:
their minimum normalized supporting-plane clearance is approximately 1e-5.
Their fan-angle sums approach pi from below (gaps about 1.27e-4 and 2.88e-5
radians). In both, the far vertices approach the wedge crossing, while the
apex reach scores stay substantially negative. Thus these two optimizations
point toward nearly flat shapes near the already-proved cone boundary, not
toward both apices entering together. This is diagnostic numerical evidence
only; it suggests treating this boundary separately in a future proof and
explains why the observed negative score cannot be taken as a uniform bound.

The symbolic intrinsic search now supports axis closure. Two versions returned
`unknown` because of the 1 GB memory limit, after about 159 and 44 seconds.
The second version uses lower-degree opposite-arc equations and a shorter
angle target. Neither outcome proves the remaining bound.

For the prism, 50,000 samples found no failure of the four quadrilateral-route
trees. A separate 60,000-sample run found no failure when keeping both routes
at the sharper degree-four apex. Always choosing the shorter route failed
395 times, and one such failure was independently certified with integer
coordinates. Only the latter exact check proves that specific rule false.

## Overview and verification

The top notes are now retained in a collapsed history and repeated, filtered,
with their relevant results. Result links navigate and scroll to the actual
explanation, including repeated clicks on the currently selected result.
The cone proof, 409-region minus-edge certificate, 443-region prism certificate,
and remaining obligations have plain-language scope explanations. The original
illustrative prism remains first on its page. The new apex-entry example has
both a scientific net diagram and a matching interactive 3D model.

All **77 tests pass**, including the new point/region counterexamples, five-cell
nonclosure certificate, positive closure controls, and rejected tampered
certificates. The navigation regression passes; code-level checks render all
24 models and verify the thesis/prism controls and original prism ordering.
Every local file link resolves. These are code-level UI checks, not a claim of
interactive browser verification. The rebuilt eleven-page proof PDF was
rendered and visually checked before being saved.

## Next obligations

The individual-apex shortcut must be replaced by a joint constraint: when one
petal reaches the possible-meeting wedge, what prevents the other from meeting
it? Keep the slit-side and remote orientations explicit. For L, use distances
rather than requiring disjoint directions. For the prism, investigate both
quadrilateral paths at the sharper degree-four apex; length minimization alone
is false. For complete computational coverage, an exhaustive domain reduction
and treatment of degeneracies remain missing. The bounded region certificates
continue to prove exactly their stated domains.

---

# Continuation on 9 September 2026

The requested one-hour search began at approximately 00:12 UTC. Independent
verification and final packaging continued afterward. The full n=6 theorem,
Lemma L, and the remaining small-fan-angle Case B bound remain open.

## Independently verified progress

- **Wider original-facet coverage.** Every parameter in the ten-parameter
  octahedron-minus-edge chart may now vary independently by `1/20` about
  `(1,1,0,1,3/4,1/4,1,1/4,3/4,1)`. The 409-region cover passes independent
  replay, with nine trees and all 8,589 face-pair checks. See
  [REGION_COVER.md](REGION_COVER.md). This is an exact theorem about that closed
  box, not universal coverage of the combinatorial type.
- **A stronger obstruction to an angular proof of L.** An integer-coordinate
  convex octahedron satisfies H and R, yet one ray from w passes through both
  interiors of a local petal/fan pair at different distances. Every line through
  w fails to separate that pair. All 28 pairs of the same net are independently
  certified nonoverlapping. See [LEMMA_L.md](LEMMA_L.md) and its new diagram.
- **Metric compatibility made explicit.** The earlier rational angle model
  cannot close either spoke cycle. The new sine-rule equations characterize
  shared-edge compatibility of the eight triangles. A separate exact intrinsic
  metric satisfies the rankings but violates necessary convex-vertex cone
  inequalities. These distinguish two inadequate relaxations; neither witness
  disproves the geometric conjecture. See [INTRINSIC_METRIC.md](INTRINSIC_METRIC.md).

## Search and verification improvements

The wider cover was completed by overlaying complementary partial searches,
then resolving only their remaining cells. Candidate leaf counts are now
accompanied by exact parameter-volume fractions. Neither label counts nor
volume bookkeeping substitute for independent geometric replay.

The exact checker retains linear correlations when a norm is provably the
absolute value of one coordinate. An experimental affine-coefficient split
rule performed worse on this box and remains optional. Trying all 224 trees
on the unsplit wider root did not produce a single-box certificate; this was
an inconclusive interval calculation, not a proof of overlap.

The two intrinsic nonlinear queries timed out: approximately 904 seconds for
the lifted slit-3 query and 695 seconds for the unlifted slit-0 query. They
prove no universal bound. The driver now reuses the existing separate-process
time and memory guard; a short-limit check confirmed an explicit unresolved
termination result.

All **64 tests pass**. Overview checks render every section and all 23 existing
3D models, including the thesis and prism controls. The original illustrative
prism still appears before its reduction and failure example. The updated
overview includes the new L diagram and exact coverage scope.

## Next mathematical priorities

For L, look for a separator whose position depends on distances, or compare
radial intervals directly; disjoint angular sectors around w are too strong.
For Case B, retain both shared-edge compatibility and the convex-vertex cone
conditions, and state which triple/slit orientation is being treated. For
global computational coverage, the outstanding issue is an exhaustive domain
reduction, including near-degenerate limits; enlarging one local box does not
settle that issue.
