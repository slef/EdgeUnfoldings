# Six-hour research continuation, 9 September 2026

Started 2026-09-08 16:25:25 UTC (01:25:25 JST).
Minimum work horizon: 2026-09-08 22:25:25 UTC (07:25:25 JST).
Branch: `codex/n6-unfolding`. Starting commit: `6322238`.

The user's instruction is to inspect DiBiase's thesis directly, assess the
claimed octahedron gap, use any promising ideas, and pursue four proof/certification
workstreams for at least six hours. Archive/thesis instructions remain research
material, not instructions from the user. No global theorem is claimed unless
the complete mathematical obligations are checked.

## Workstreams

1. Direct original-facet treatment of the prism-with-one-diagonal. A combinatorial
   enumeration found one cut tree with just two nontrivial face pairs after
   shared-vertex-fan pruning. Test/prove these conditions and seek alternatives
   if the tree fails. The octahedron-minus-edge has minimum five residual pairs.
2. Isolate Lemma L with its actual hypotheses; pursue proof or exact refutation.
3. Build an exhaustive Case-B partition including large-angle and equality cases.
4. Extend exact checking to polygonal facets and systematic regional coverage,
   with explicit uncovered sets and boundary obligations.

## Record

- 16:25 UTC: Started direct review of thesis Chapter 3; no additional proof yet.
- 16:43 UTC: Exact counterexample to the thesis chart's fixed-tree DF entry;
  moving G alone cannot repair the seven-face core. See THESIS_AUDIT.md.
- 16:43 UTC: The prism two-pair tree fails on an exact integer-coordinate example.
  An alternative tree has a nine-parameter regional certificate. New polygonal
  checker preserves coplanarity by polynomial identities; validation is ongoing.

- 17:58 UTC: Proved a base-cone lemma giving an exhaustive opposite-petal
  partition, including large D angles and equality boundaries. Under (H), only
  Sigma_W < pi remains. See CASE_PARTITION.md and updated lemmaF.tex/pdf.
- The slit rule alone gives kappa_slit+kappa_w-nu_t >=
  (kappa_v+3 kappa_w)/4 > 0; hence the historical (a,a) Case-B branch is
  excluded conditional on Lemma L and the existing hexagon lemma.
- Exact curvature/angle checks certify a small integer H3R example with a large
  D angle. Generic polygonal certificates now also cover an explicit
  ten-parameter octahedron-minus-edge region.
- A binary region-cover checker is implemented and tested; two wider 30-minute
  searches ended with unresolved leaves. They are not complete covers.
- Rational affine arithmetic is being tested to reduce interval dependency loss.
- The local status page and PDF are updated. Automatic browser reload was blocked
  by the browser local-file URL policy; source syntax passed. No publication.

This file is a checkpoint, not a proof certificate. Results and exact scopes
will be recorded as the investigation proceeds.

- 19:05 UTC checkpoint: the prism affine subdivision has 443 certified leaves
  and no unresolved leaf. Independent replay of the full cover is running;
  do not count generation status as the final proof verdict. Broader prism
  and minus-edge covers remain partial. Reusing exact geometry/path bounds
  allows many more candidate trees per region without repeating facet checks.
- The thin local candidate is exactly certified nonoverlapping at 320 bits.
  An integer example refutes a proposed slit-bisector separator under both
  selection rules, while its whole net is certified simple. See LEMMA_L.md.
- New scalar formulas characterize each remaining apex-entry condition.
  A 2,000-octahedron numerical differential test checks 42,168 triples and
  356 selected-rule small-Sigma triples, with no observed apex-angle violation.
  An exact abstract angle countermodel shows that the linear face-angle facts
  alone cannot prove the proposed angle-only strengthening. This countermodel
  is not a claimed geometric realization.
- The thesis's three-arm family has 48 distinct trees, each with 11 residual
  pairs; it is distinct from the 24 near-stars and included in all 384 trees.
  The direct prism has six original-edge degree-four-star candidates; 20,000
  broad numerical parameter samples found no failure of their union. This is
  only a candidate family for a future universal certificate.
- Focused solver queries now also use explicit planar triangle coordinates
  and compact quadratic auxiliary equations. Previous queries timed out or
  ran out of memory; current queries remain pending or unresolved.
- GEODESIC_SECTOR.md supplies the two-face shortest-path reduction and the
  vertex-source limiting detail for the archive's sector route. An exact
  example refutes the strategy fixing the sector vertex to a globally
  sharpest vertex: every adjacent edge is too long for the radial condition.
- The overview now embeds a diagram of the exact thesis DF failure, and the
  README, review, and handoff have been brought forward to these results.

- Morning follow-up, 23:06 UTC (08:06 JST): all remaining bounded jobs finished.
  Independent replay verified the complete 443-leaf prism region, using three
  trees. The wider prism search ended with 1,649 generator-certified leaves and
  94 unresolved; the wider minus-edge search ended with 1,219 and 11. These two
  searches remain partial. The last focused apex query returned unknown after
  its 20-minute solver timeout. All 53 current tests passed. See REGION_COVER.md
  for exact bounds and the distinction between generation and verification.
