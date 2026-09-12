# Pentagonal bipyramid overnight session — 13 September 2026

Work window: **2026-09-12 16:04–22:04 UTC** (01:04–07:04 Tokyo).
Checkpoint written around 17:25 UTC; approximately 4.5 hours remain.
Continue substantive research until the deadline. The heartbeat automation
`pentagonal-bipyramid-overnight` is active in this task every 5 minutes,
with UNTIL 22:06 UTC so the final deadline run is included. At the deadline,
validate, give the morning report, and pause that automation.

All edits belong in `n7/` in the isolated `codex/n7-unfolding` worktree
`/Users/sl/Dropbox/MyStuff/dev/EdgeUnfoldings-n7`. The main worktree has a
parallel n6/Lean agent: do not change n6, durer_small_n, Lean, or root files.
Use explicit workdir and escalated permission for sibling-worktree writes.
No push or merge this session. Local checkpoints are allowed.

Runtime: the main worktree's `durer_small_n/.venv/bin/python -B`, with
`PYTHONPATH=.`. For Matplotlib set `MPLCONFIGDIR=/private/tmp/edge-n7-mpl`.
Do not retry the previously denied browser opening via another surface or
localhost. Use static SVG rendering and the existing Node UI tests.

Research checkpoint: `40f7bae` (all first-pass proofs and exact checks).
A temporary idle-sleep inhibitor runs until approximately the deadline
(`caffeinate -i -t`, tool session 90334); no persistent power setting changed.
No mathematical search is currently running.

## Starting point

Commit 5f73e93 gave the three equator-deletion cases, convex straight-line
insertion, monotonicity of inserted curvature, and two exact insertion
paths. One shows a target minimum whose initially safe net fails; a second
fixed tree works on its whole path. Three of 15 whole symbolic pattern
classes are covered. The whole graph remains open.

## First pass: completed results

Read the current pages rather than rediscovering these results:

1. `BIPYRAMID_OVERNIGHT.md`: old curvatures decrease under nested insertion;
   only four neighbors change; a target minimum stays minimum throughout.
   The collision page strengthens each neighbor loss to strict decrease.
2. Largest-distance-sum slit with the sharper pole as source: all adjacent
   patch pairs safe for any ring size. At n7 this proves 30/45 pairs and
   leaves five nonadjacent patch groups, 15 pairs. This does not prove the
   full selected net. No valid counterexample to its full net is recorded.
3. At most two inward patches and one pole curvature >= pi: entire net,
   every ring size >=4. All five two-bad patterns are covered inside that
   curvature branch. Four remain partial whole classes; 3/15 unchanged.
4. Distinct convex receivers (BCBCC, BCFCC, BFCCC): stronger sufficient
   gate `2*kappa_p+kappa_q >= 2*pi`. Also sufficient: pole sum >=4*pi/3.
   Exact replay: seven examples, including a pole switch and three with
   both poles below pi. `bipyramid_rule_checks.py`, `bipyramid-two-gap.json`.
5. `BIPYRAMID_COLLISION.md`: the original minimum-insertion fixed tree is
   safe exactly for 0<=t<=tau and overlaps for every tau<t<=1, with
   6260373/10000000 < tau < 6260374/10000000. The two pairs 0/1 and 0/6
   collide simultaneously when a moving copy of u1 crosses the fixed
   root-petal cut edge. A fixed-circle formula and strictly decreasing
   fan curvature give uniqueness. All 15 nonlocal pairs stay separated.
   491 closed exact interval cells, `bipyramid_collision.py`.
6. `BIPYRAMID_RECEIVERS.md`: the residual conflicting pole preferences
   really occur, including BOTH receiver-plus-gap failures. Integer points:
   u0=(-75,4,0), u1=(-60,-7,0), u2=(12,-10,0), u3=(54,-7,0), u4=(81,0,0),
   v=(18,-8,1), w=(-20,-3,-5). Pattern FCCBC, canonical BCFCC.
   Exact checker certifies six safe nets (fan either pole; slits0,2,4).
   Do NOT try to prove all conflicting preferences impossible.
7. Universal two-receiver-chain reduction for FCCBC: choose fan p with
   ell0_p+ell3_p < angle_p(Q1)+angle_p(Q2), which exists by the exact
   chain angle sum. Slit at u0. At most one extension is long. If long0,
   only V0/V2 and V0/W2 remain; if long3, reflected pairs V3/V1,V3/W1.
   43/45 pairs settled. A boundary-neighbor argument shows the fan pair
   follows from the petal pair: ONE independent metric pair remains.
8. An auxiliary-octahedron bridge closes another family: for long0,
   deleteu4, require octahedral reduced hull, source q sharper than fan p
   IN THAT HULL, and a reduced equator maximum at endpointu0 oru3.
   Apply n6 paired-pole theorem to separate the unchanged Q0,Q1,Q2.
   Reflection treats long3/deleteu0. The integer example satisfies this;
   exact checker also validates its 28-pair auxiliary net and all ranks.
   n6 dependency read only; no n6 proof code imported.

Overview and ten reading pages regenerated. Both new scientific figures
rendered and inspected. Last full validation: 33 Python tests, both Node
UI tests, and diff whitespace checks passed. Rebuild after later edits.
Whole counts remain 10/34 graphs and 3/15 symbolic patch classes.

## Discovery record and numerical pitfalls

Archived scripts/results under `experiments/bipyramid/`, with exact limits
and replay instructions. The earlier 120k search found no opposing
preferences, but another search did; the exact integer example supersedes
that conjecture. A wide-search alleged full length-rule failure is a FLOAT
ARTIFACT in already-protected adjacent fan faces5/6 at extreme aspect ratio.
Do not present it as a true counterexample.

The latest targeted chain search finished: 200,000 attempts, 139,137 valid,
15,092 relevant. Eligible choices: 18,099 both-short, 2,671 bridges,
6,600 wrong auxiliary pole, 783 other reduced graph, no residual overlap.
Choices overlap, so counts are NOT shape coverage or proofs. All sessions
for this search have completed. More raw tools are in /private/tmp.

## Next bounded proof investigation

Prioritize the one petal/petal pair from the receiver chain, e.g. V0/V2
with Q1 convex and ell0_p>angle_p(Q1). The auxiliary bridge handles only
one branch. Read n6/TIDY_CORE.md (especially the opposite-petal partition
and wider Case A separator) and n6/PAIRED_POLE_RULE.md as dependencies.
These local arguments may transfer without changing n6 files.

Useful deductions not yet added as new universal page theorems:

- The n6 wider Case A separator is local to three consecutive petals.
  Middle base a=u1,b=u2, middle apex M=q, source angles lambda,nu,rho,
  K=kappa_a+kappa_b, theta=pi-nu+K. In Case A theta<pi, copied cut rays
  meet with lengths L=|ab|*sin(beta)/sin(theta),
  R=|ab|*sin(alpha)/sin(theta), alpha=middle angle at a+kappa_a,
  beta=middle angle at b+kappa_b. At least one copy is short by the
  convex distance-sum argument. A short side with outer apex angle
  <=(pi+theta)/2 gives separation. Both outer angles below this bound
  suffice. The angle-sum premise is automatic from the source link.
  Base-cone branch theta>=pi and sigma+tau>=pi also transfers locally.
  Do not silently assume the small-fan-pocket n6 proof transfers.
- A NEW candidate five-patch correction identity has been algebraically
  derived and numerically checked, but needs a clean written audit:
  Let outside ringvertexu4 have source corner A4 (two source triangles)
  and fan corner B4. Let S be the sum of the strict closed-link slacks
  at u0,u3 for their source face angles in Q4,Q3. Then
    2*pi+K-2*lambda-nu
      = (kappa_q-kappa_p+B4-A4)+S+nu+2*rho,
  and swap lambda,rho for the other bound. Thus H=kappa_q-kappa_p+B4-A4
  >=0 makes BOTH wider Case A bounds automatic. H changes sign when
  poles swap. At a flat insertedu4 on the old closing edge, A4=B4=pi,
  recovering the n6 identity. Need exact symbolic validation and scope.
- A long extension into a convex receiver seems to force containment:
  with inward equator a, old source copy P from the bad patch, receiver
  source copy M and fan p, the entire receiver lies in triangle(a,p,P)
  because shared-vertex separation and the cone bounds block all exits.
  |aM|=|aP| then implies (M-a) dot (p-a)>|aM|^2. The original source
  angle angle(p,q,a) is obtuse; the convex receiver's source apex angle
  is also obtuse because its diagonal pM lies inside the convex patch.
  This needs careful boundary/containment audit; do not yet cite as proved.
- A possible small-fan pocket generalization removes both outside patches
  Q3,Q4 from the hypothetical overlap pocket. Expected angle identity:
    nu3+nu4 > kappa_u0+kappa_u3+kappa_u4+kappa_p.
  If valid, Gauss--Bonnet contradicts it whenever K<=2*pi. This is only
  a DERIVATION TARGET; cyclic boundary angles and simplicity must be proved.

If that pair stalls, analyze BCBCC/BFCCC separately or the adjacent-same
both-small-poles branch. Do not request user input while an independent
proof task is available. Preserve negative results and update this handoff
at each research pass. End with a self-contained morning report at deadline.
