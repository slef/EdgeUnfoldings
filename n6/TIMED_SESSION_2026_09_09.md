# Timed octahedron proof session

User-authorized interval: **9 September 2026, 08:41–11:11 UTC** (2.5 hours).
Prioritize simple universal octahedron exclusions, written proofs, and exact
checks. Keep the web overview and collapsed history current. Do not merge or
push. Work on the existing `codex/minus-edge-patterns` branch.

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
