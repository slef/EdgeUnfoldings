# Timed octahedron proof session

User-authorized interval: **9 September 2026, 08:41–11:11 UTC** (2.5 hours).
Prioritize simple universal octahedron exclusions, written proofs, and exact
checks. Keep the web overview and collapsed history current. Do not merge or
push. Work on the existing `codex/minus-edge-patterns` branch.

**Latest authoritative checkpoint: 10:55 UTC.** The older far-fan reduction is now exactly refuted. Use 49 original classes, 2 excluded and 47 open; the one-patch whole-net claim is reopened. The curvature-pair, central-symmetry, short-edge and mixed radial-cover theorems survive independently. See the final checkpoint below before interpreting historical entries.

Starting commit: `6b2b24d`. Starting status: 23 sufficient switching classes
open (8 mixed, 15 local-only). The full octahedron theorem, L, and F are open.
Original class 49 is excluded by the opposite-route angle-sum identity.

A bounded heartbeat named `octahedron-proof-session` is active in this task,
every ten minutes, ending at 11:11 UTC. At the deadline, validate changes,
checkpoint them, give the final report, and stop the timed investigation.

## Initial low-hanging targets

1. Audit the new switching implications and identify elementary necessary
   conditions for local pair overlap that exclude cyclic failure patterns.
2. Study local petal lean directions and the broken boundary lengths
   d_i=|wu_i|+|vu_i|. A reflex two-triangle quadrilateral at u_i puts u_i
   strictly inside the triangle formed by its other three vertices, implying
   d_i<d_{i+1} by convexity of the sum of distances. This promising observation
   needs a complete proof, checks, and correct mapping to each local event.
3. A slit at maximum d_i has no flank leaning into its angular gap. Overlap
   around the other side remains a separate issue; do not confuse gap
   exclusion with a proof of L or whole-net simplicity.
4. Exact-audit the numerical failures of the more restrictive large-fan-sum
   selector if useful. These do not refute the four-choice conjecture.

## Persistence notes

- No subagents are authorized; work locally.
- Use `durer_small_n/.venv/bin/python` for numerical tools.
- `n6/OCTA_CASE_ANALYSIS.md` contains the starting proof and dependency map.
- Edit `durer_small_n/notes/status_template.html`, then regenerate the overview
  with `python3 durer_small_n/build_status.py`.
- User PDFs remain untracked; do not add them.
- Finish any ongoing computation before starting a duplicate after a wakeup.

## Checkpoint around 09:20 UTC

New written results in OCTA_CONVEX_PATCHES.md: reflex corner implies a strict
increase of d_i=|wu_i|+|vu_i|; at least one patch is convex; original class20
excluded; all-convex and exactly-one-nonconvex regimes proved (H for one).
Two adjacent, two opposite, and three nonconvex patches remain open.
Current class count: 2/24 excluded, 22 open (8 mixed,14 local-only).
Exact checker convex_patches.py has five integer examples with net certificates;
5,000-shape survey counts 676/1906/1348/976/94, numerical only.

Active computation: exec session50965, n6.octa_targeted,120sec per each of22
classes,100 starts, output results/octa-targeted-session.json. Started08:59UTC,
should finish about09:43UTC. Do not duplicate; failures to find overlaps exclude
no class. Exact-audit any positive feasible candidate. New files uncommitted;
web and tests are being integrated and need validation/checkpoint.

## Checkpoint around 09:31 UTC

Commit803d1a6 saved the two patch regime proofs and class20 exclusion, with104
tests passing and68 deployed evidence links checked. Further uncommitted work:
- Actual four-patch SVG, successful net SVG, and rotating3D exact model on page.
- Exact three-nonconvex-patch radial failure, source1/sector0, all four spokes
  longer than valid two-face path; original H-star net independently verified.
- OCTA_SHORT_EDGES.md and sector_cover.py prove a separate sufficient metric
  family: sector vertex curvature>=120deg and every strictly convex patch has
  an endpoint with spoke<=Euclidean pole chord. Star cuts are at the opposite
  source vertex. Proof invokes Aronov–O'Rourke exterior-sector Theorem9.1,
  re-read from primary PDF this turn. Five exact instances incl3patches pass;
  six new tests pass (including length equality and nonmax high curvature).
  Not yet on overview/logs or committed; no new whole class/regime closed.
- Strengthened existence lemma: at least one strictly convex patch, since a
  straight corner also forces strict broken-path increase. Boundary included.

Targeted search session50965 still active, about14of22 classes complete;
all best scores negative, mostly rounding-scale. Exclude no classes.
Temporary central-symmetry pilot session69189:10k affine cross polytopes,
classify patches at sharpest apex; no result yet. Need inspect before claiming.
Temporary metric-cover all-high-vertex probe:16of10k fail even the patch-aware
chord criterion numerically; no universal criterion claim. Results in/tmp.

## Checkpoint around 09:50 UTC — strong new theorem

OCTA_TWO_SHARP_POLES.md now proves the stronger curvature-pair criterion:
sector pole K>=120degrees and K+2J>=360degrees implies a successful
star(other pole)+one edge net. In particular if K>=J the weighted bound
implies K>=120 automatically. Proof: both sector spokes>L would force
omega+2nu>2pi by adding two triangle side/angle comparisons. The cone angle
bounds instead give omega+2nu<=3pi-K/2-J<=2pi. Angular sector condition is
automatic. Hence **every centrally symmetric octahedron** is proved: the two
sharpest opposite vertices tie and each has curvature>=120. Original H-source
four-choice rule is proved for that symmetric family. No historical novelty
claim and no extra whole fixed-source failure class excluded.

curvature_pair.py checks actual interval hypotheses; verify_central checks
central symmetry by polynomial identities. Four exact point examples and a
nine-variable central affine box have independent successful-net certificates.
Six new curvature tests pass, including phase wrapping/equalities, rejection
of a low-opposite-curvature case, and central midpoint tampering. Six sector
cover tests also pass. Full suite expected116; run before checkpoint.

Overview now has nodes octa_curvature and octa_short_edges, readable proof,
central corollary, exact links, and retained history. Patch page has actual
SVG+3D examples. All are uncommitted after803d1a6.

Targeted numerical search FINISHED:22 classes,3,109,962 objective evaluations,
7,140 optimizer runs; all best overlap scores negative. Excludes no class.
File n6/results/octa-targeted-session.json and module octa_targeted.py need
checkpoint. All earlier exec sessions are complete.

New combined numerical pilot /private/tmp/octa-combined-probe.json (seed6090948):
20,000 shapes;10,386 pass zero/one patch condition;17,487 pass weighted pair;
19,978 pass some high-vertex short-edge cover;16 pass none of these three
simple criteria. Counts overlap and are NOT global coverage. The first
uncovered example has three high-curvature vertices forming a face, their
opposites low, and two nonconvex patches at the sharpest apex. Next exact-audit
that residual and investigate this pattern. The whole octahedron remains open.

## Checkpoint around 10:00 UTC

Exact uncovered representative now saved, small integer points, in
results/octa-new-criteria-uncovered.certificate.json. proof_family_audit.py
proves every eligible sector vertex fails the weighted pair and chord-cover
criteria, and H-source has two nonconvex patches. Independent net is successful.
OCTA_REMAINING_FAMILIES.md records scope and completed22-class search counts.
Two tests added; full expected118. Overview links the exact remaining example.

Dependency audit underway: reread actual Case-A no-wrap/apex-cone/nocross
proofs in durer_small_n/notes/lemmaF.tex; algebra is consistent. Far-fan hinge
proof wording needs careful review at the exterior radial cut boundary.
Temporary numerical dependency audit session85525 tests10k shapes ×24nets
for far-fan overlap with all local and opposite pairs clear; poll it. No
claim of a flaw yet. This dependency affects the earlier switching reduction
and one-patch proof, not the new independent curvature/sector results.

Other exploratory leads: face-angle criterion omega+2nu<=2pi at all patches
of a >=120-degree sector vertex is sufficient by the new radial lemma, but
not universal (207 numerical failures/20k); angular relaxation SAT is not a
polyhedron. A convex-boundary-net shortcut has no qualifying cut tree on the
exact uncovered example (numerical best largest corner204.57degrees). Do not
promote these exploratory results to proofs or add redundant page criteria.

## Checkpoint around 10:06 UTC

All 118 Python tests pass, along with navigation, progress, minus-edge, and
deployment checks (78 evidence links resolve). New proofs, certificates, and
illustrations are staged for a local checkpoint. No merge or push.

Both temporary hinge audits completed without a counterexample. The 10,000
shape audit found 23 nets with far overlap and local pairs clear; all had an
opposite-petal overlap. The targeted two-orbit search (session74089) made
224 optimizer runs and299,060 objective evaluations over240 seconds; neither
target achieved a positive feasible overlap with local and opposite pairs
clear. Numerical failure is not proof. The wording at a radial cut boundary
is still being examined; no flaw in the implication has been established.
No computations remain running as of this checkpoint.


## Checkpoint around 10:55 UTC — exact correction and stronger local theorem

Commit4210095 saved the curvature/short-edge results. Subsequent work is not
committed yet. No computations are running except validation when explicitly
started. All temporary numerical research runs completed.

**Critical:** n6/HINGE_AUDIT.md and hinge_audit.py certify an exact convex
counterexample to the old unrestricted conditional far-fan reduction. The
source is NOT sharpest. Only V2/W0 overlap; all other27 pairs are exactly
nonoverlapping. Point12/25 along the radial cut lies strictly inside V2.
A second cut tree on the same solid is exactly successful. Thus H-specific
F and the sharpest-source four-choice conjecture are NOT refuted. The old
proof fails at a CUT radial boundary, not at an interior hinge.

Restore original49classes,2excluded(20,49),47open. Withdraw smaller24class
sufficient reduction; retain it explicitly as history. One-nonconvex-patch
argument proves a common locally/opposite-petal-safe choice, but whole-net
safety remains open. All-convex patches and both switching implications
survive. Corrected analysis/current vs historical metadata, future targeted
search, overview, dashboard, PDF/LaTeX and current research notes accordingly.
TreeBatch JSON replay had list/tuple mismatch giving false clear masks;
normalized pairs and added regression using the actual overlapping net.
Exact certificate tools were unaffected.

**New positive:** OCTA_RADIAL_COVER.md proves mixed local sufficient cover:
at every strictly convex two-face patch of a >=120degree sector vertex,
either an endpoint spoke <=3Dpolechord OR omega+2nu<=360degrees. This forces
a spoke <= shortestpath length, and the sector theorem gives an edge net.
A15parameter asymmetric box now qualifies where earlier criteria failed;
independent all28pair net certificate covers the box. A second integer
example exactly fails the mixed criterion at every eligible vertex but has
a successful net. Six new radial tests include both positive and negative
checks. Four hinge tests include exact overlap/safe pairs and JSON replay.

**New structural reduction:** outside the curvature-pair theorem, choose the
larger-curvature endpoint of each opposite pair. These endpoints form a face,
its curvature total exceeds360degrees, and all vertices outside it have
curvature below120degrees. Hence the >=120degree vertices form exactly one
of: one vertex, one edge, or a full face. These are three open branches,
not three solved cases and not additional fixed-source class exclusions.
Proof in OCTA_REMAINING_FAMILIES.md; overview node octa_curvature_remainder.

The full suite passed126 before two added radial tests; the six radial tests
then passed. Expect128 full tests on final validation. Node navigation,
progress, and minus-pair tests passed before the new structural node. Need
rerun current build+tests+deployment after staging all intended changes.
The new hinge figure was rendered and visually checked. Corrected lemmaF.pdf
was compiled twice and changed pages visually checked, then copied to repo.
Do not add the two user PDFs. Do not merge or push. Finish at11:11:09UTC.
