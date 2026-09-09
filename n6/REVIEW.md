# Repository and proof audit, 9 September 2026

Branch: `codex/n6-unfolding`, based on `65d5988`.

**No complete proof or universal computational certificate of n=6 was obtained.**
There is new rigorous partial coverage of a full coordinate box, an exactly
checked counterexample to a supporting lemma, and a reproducible reduced SMT
attempt that reports a timeout.

**Continuation:** the subsequent direct thesis audit found an exact fixed-tree
DF chart failure. A new base-cone proof closes the missing large-angle partition,
including its equality boundaries; under (H), only `Sigma_W<pi` remains for
opposite petals. The slit rule also excludes the historical `(a,a)` branch
conditional on L. See [THESIS_AUDIT.md](THESIS_AUDIT.md),
[CASE_PARTITION.md](CASE_PARTITION.md), [LEMMA_L.md](LEMMA_L.md), and the expanded
[certificate inventory](README.md). These results supersede the corresponding
initial-audit limitations below; the complete theorem remains open here.

**Morning results:** independent replay verifies a nine-parameter prism box
with 443 leaves and three trees. The larger searches remain incomplete, with
94 prism and 11 minus-edge unresolved leaves. The final focused apex query
timed out; all 53 current tests pass. [REGION_COVER.md](REGION_COVER.md) states
the exact domains and which results have received independent replay.

## What was reviewed and reconciled

The review covers the repository structure, both handoffs, the 73 existing
Python files and their experiment/dependency map, the mathematical notes,
status-page sources and generator, stored-result formats, and the deployment
workflow. All 77 pickle streams were parsed as opcodes without executing their
contents. They remain historical numerical data, not proof certificates. The
long searches and every stored sample were not independently rerun.

The two original handoffs were byte-identical. The nested handoff now points to
the root so later corrections cannot silently diverge. Older exploratory scripts
are retained: many contain import-time experiments, and `patch*.py` are historical
edits to the page template, not build steps. They should not be imported as a
general library. The reusable geometry modules receive focused regression checks.

The thesis excerpt (printed pp. 71–73) and full-thesis octahedron discussion
(printed pp. 72–76, including Lemma 3.6 and Figure 3.28) were visually inspected.
The full thesis was not independently reread page by page during this initial audit.
The pages support the existing observation that the octahedron argument relies
on a figure-specific reassignment of its last face; they do not fill the missing
general proof. The scanned PDFs remain user-supplied, untracked files.

In the continuation, all Chapter 3 pages were rendered and reviewed with OCR
alongside the scans, and the complete octahedron argument and relevant figures
were inspected visually. The exact chart counterexample is described in the
separate thesis audit. No claim is made to have reread every page of the thesis.

Both archives contain exactly the same `unfolding.py` (hashes in
`archive_notes/manifest.json`). It is integrated once as `encoding.py`. Their
24-tree octahedron family is the same family as Claude's `Z_k`; it is not new
coverage. The polynomial counterexample formulation is complementary to the
curvature-based proof search, while the sector condition strengthens an earlier
star-unfolding shortcut. The latter is a sufficient condition, not a proof that
some choice always satisfies it.

The first archive's statement that the thesis had not been obtained is historical:
the repository now contains it. Neither archive's instructions to pursue n=7 nor
its runnable examples were treated as the user's task. Work here is on n=6.

## Corrections affecting the proof

### 1. The unrestricted D-lemma is false

The former `lemmaF.tex` assertion says that the line through `u v_i` has `V_i`
on the side not containing the middle petal `V_j`. That is false once the
curvature rotation can wrap past pi. An explicit strictly convex octahedron is

```
0 = ( 6,-4, 9)   1 = ( 2,-5, 9)   2 = (-9,-7, 0)
3 = (-8, 8,-4)   4 = (-5, 0,-5)   5 = (-3,-8,-1)
```

Choose `v=3`, `w=5`, equator `(u0,u1,u2,u3)=(0,1,2,4)`, slit `k=2`,
and triple starting at `i=3`. Thus `u=u0=0`, `u_i=u3=4`, and the middle
petal is `V0`. In the developed net, the far vertex of `V3` and the apex
copy of `V0` lie on the **same strict side** of the line `0 v_3`.
The checker proves the two oriented determinants are negative, by disjoint
rational sign bounds, and verifies all original hull facets first.

Reproduction: `python3 -m n6.audit_witness`. See the coordinate certificate and
`d-lemma-verification.json`. This is an exact refutation of the unqualified
supporting assertion, not a numerical counterexample to unfoldability.

The continuation's exact angle-product checker now also certifies that vertex 3
has maximum curvature: see `d-lemma-curvature.verification.json` and
`python3 -m n6.curvature n6/results/d-lemma-counterexample.json --sharpest 3`.
Thus the sharpest-apex hypothesis does not repair the unrestricted assertion.

The valid D-lemma range is explicitly restricted to
`0 < phi+kappa_u < pi`, `0 < psi+kappa_u' < pi`. It is automatic in Case A
because the sum is `pi-nu_j+kappa < pi`. The existing no-wrap and apex-cone
argument therefore still proves the Case-A opposite-petal statement: its proof
uses only this restricted geometry. The noncrossing-cut-edges lemma is now stated
only in the Case-A range actually covered by its proof.

The continuation handles the complementary ranges through the base cones,
without an unrestricted D-lemma. Under (H), the entire remaining region is
`Sigma_W<pi`; there the outer-fan half-planes directly define the relevant wedge.
The two individual apex non-entry statements still require proof.

### 2. Updated: the conditional far-fan reduction is refuted

The exact [hinge boundary audit](HINGE_AUDIT.md) supersedes the earlier
assessment below: local nonoverlap does not suffice for the far-fan step.
The first and last fan faces have a cut radial boundary, not two interior
hinges. A certified example has one far-fan overlap and all other 27 pairs
safe. Its source is not sharpest; an H-specific replacement remains open.
The original 49-class target (2 excluded,47 open) is current; the 24-class
reduction and fixed-source one-patch whole-net claim are withdrawn.
A subsequent [two-pole proof](OCTA_ONE_PATCH.md) establishes existence for
the one-patch family under H. It can exchange the four-cut source, so it
does not restore that fixed-source claim or change the 47-class count.
The later [patch-budget theorem](OCTA_PATCH_BUDGET.md) extends existence
to every two-patch configuration and to three with mixed directions under
H. Only the common-direction three-patch pattern remains open in this
patch approach. The fixed-source count remains unchanged.

The following interior-hinge observation remains valid.

At `w u_{k+1}`, the petal `V_{k-1}'` has no uncut vertex copy in common with
either adjacent fan face. The mirror exception is `V_k` at `w u_{k-1}`.
The original proof's blanket common-vertex assertion overlooks the slit copies.
A crossing in either exceptional case would cause a local overlap, so the
argument works **assuming Lemma L**. This dependence is now stated explicitly.
Also, the proof excludes proper crossings, not every possible boundary contact.

The former intended order was L, then opposite petals, then far-fan reduction.
The last step now needs its own proof even after the first two are established.

The direction-condition proof in Case B also assumes its far vertex lies on the
near side of the other outer-edge line. That excludes the corresponding `f`
subcase. The angle identity itself is algebraic and remains unchanged; the
geometric implication is now scoped to the condition actually used in its proof.

### 3. Nonsimplicial perturbations require uncut diagonals

An octahedron-minus-edge limit needs successful cut trees avoiding the added
diagonal. Unrestricted existence of a successful `Z_k` does not imply that:
if the selected apex is an endpoint of the added edge, its full star cuts it.
Nor can a degree-four-star existence claim automatically ensure that both
diagonals added to a prism-with-diagonal remain hinges.

A sound conditional limit lemma is: take a sequence of convex refinements
approaching the prescribed original-facet polytope, each with a successful cut
tree using only original edges. Pass to a constant-tree subsequence (finitely
many trees). Developments converge; positive-area intersection of two
nondegenerate limiting faces would persist nearby, contradicting nonoverlap.
The uncut diagonals merge back into their original planar facets.

The missing tasks are construction of the appropriate refinements **and** proof
that a successful tree can always be chosen to avoid the artificial diagonals.
The integrated polynomial queries instead work directly with the original
polygonal faces and do not rely on these reductions.

## Corrections affecting numerical evidence

- `adv_angle.py`, mode `i`, used `Vi[1]` although `Octa.Z` stores
  `[v_i,u_{i+1},u_i]`. It now measures the angle at `Vi[2]`. Saved old
  `adv_angle_*_i_*.pkl` results do not establish the intended claim; fresh mode-i
  output uses a `_far_vertex_v2` suffix. A 500-octahedron smoke run had 47 eligible
  triples, with maxima about -1.440 (i) and -0.455 (jj) radians. This is numerical
  evidence only, and the full historical adversarial runs have not been repeated.
- `octa_structure` accepted some flat quadrilateral facets triangulated by Qhull
  as octahedra. This was encountered in the first candidate for the D-lemma
  witness, which the exact checker rejected. It now checks strict off-facet
  support numerically and rejects unresolved near-mergers. The imported sector
  setup receives the same safeguard. A regression reproduces the former error.
- Existing `unfold.py`/`unfold2.py` use numerical coincidence to skip some face
  pairs. That is suitable only as a heuristic near degenerate contacts. The new
  exact query and certificate use a common vertex **along every face of the
  hinge path**, which identifies the same uncut copy combinatorially.
- Direct floating evaluation of the archive's high-degree homogeneous overlap
  determinants can produce false positives at contacts through cancellation.
  The cross-check removes the positive homogeneous factors before floating sign
  comparisons. The exact polynomial formula is unaffected by this numerical issue.
- The angle LP uses floating arithmetic and does not export an exactly verified
  dual certificate. Its results remain numerical relaxations. Guarded hill climbs
  and finite clipping windows also leave limiting configurations unexamined.

## Current computational results

The atlas filter again gives `1,2,7,34` graph types for `n=4,5,6,7`.
For n=6:

| Atlas graph6 | Degrees | Original facet sizes | Trees | Remaining route |
|---|---|---|---:|---|
| EtTg | 333333 | 33444 | 75 | Dome result applies to the combinatorial prism type |
| Ehfw | 333335 | 333335 | 121 | Universal-vertex star theorem |
| EzNG | 333344 | 333344 | 130 | Direct polygonal case or diagonal-preserving reduction |
| ER~g | 333445 | 3333334 | 209 | Universal-vertex star theorem |
| Ep~o | 334444 | 3333334 | 224 | Direct polygonal case or diagonal-preserving reduction |
| Ep~w | 334455 | 33333333 | 336 | Universal-vertex star theorem |
| EznW | 444444 | 33333333 | 384 | Octahedron case remains open in this investigation |

`nx.octahedral_graph()` uses graph6 `E}lw`, isomorphic to atlas `EznW`; graph6
strings depend on labeling. Do not treat the two strings as different types.

Common-vertex-fan pruning reduces the archive's near-star query from 168 to 120
shared nontrivial paths, and from 257 to 209 assertions. Each tree has exactly
9 remaining face pairs, matching Claude's pair list. The new query contains
21,489 DAG nodes and 1,195,142 bytes. With Z3 5.1.0, a 10-second solver setting
and 20-second outer deadline, the run returned `unknown` with reason `timeout`
in about 15.3 seconds overall. No certificate was generated for this universal
query. A tetrahedron-star calibration returned UNSAT after its fan pairs were
removed; this does not establish the much harder octahedron case.

The new interval certificate covers the 18-dimensional box described in
README, with fixed cut tree `{5-1,5-2,5-3,5-4,0-2}`. The checker validates the
octahedral surface and cut tree, all 24 strict facet-support signs, positive
face areas and divisors, and every one of the 28 face pairs. Its trusted base is
the small checker, Python integer/Fraction arithmetic, and the elementary
convex-vertex-fan lemma. It does not trust the proposed separators or use an
epsilon acceptance rule. Inconclusive intervals cause rejection, not acceptance.
It is a replayable exact arithmetic certificate, not a formal proof-assistant
development, and covers only the explicit box (plus its similarity images).

Numerical differential validation covers all 1,479 trees on one realization of
each of the seven n=6 types, retaining quadrilateral and pentagonal facets.
It also compares all 24 archive and Claude octahedron nets on the box center.
These comparisons test implementations, not the continuum of convex realizations.

## Sources and next proof obligations

The star-unfolding exterior-sector definition and nonoverlap theorem were checked
in Aronov–O'Rourke, Section 8.1 and Theorem 9.1
([original paper](https://link.springer.com/content/pdf/10.1007/BF02293047.pdf)).
The archive's sector condition remains a plausible useful sufficient condition:
the moved triangle fits the exterior sector when its radial length and angular
extent fit. Source-at-vertex and tied-path limiting details must be kept explicit;
there is no proof here that every octahedron admits the required choice.

The definition of a dome and literature attribution of dome edge unfoldability
were checked in Demaine–Demaine–Uehara, Sections 1–2
([author manuscript](https://erikdemaine.org/papers/ZipperDomes_CCCG2013/paper.pdf)).
A general realization of the triangular-prism graph need not be a metric prism
with parallel bases; its quadrilateral facet adjacent to every other facet is
what makes the dome result applicable. This audit uses that established result
as an external theorem, not a new proof of it.

Next work should address the large-angle cases uncovered by this audit and
Lemma L, or prove universal existence for the full 24-tree or sector family.
For computation, extend exact interval coverage with explicit uncovered regions
and a verified subdivision tree; no finite sample or isolated box proves global
coverage. Boundary strata with merged facets must retain their original edges.
The two residual nonsimplicial cases remain separate obligations until a
diagonal-preserving theorem is available.
