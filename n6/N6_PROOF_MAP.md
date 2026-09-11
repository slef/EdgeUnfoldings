# Six-vertex unfolding: current written proof and review map

12 September 2026. **All seven type arguments are now written. Independent
mathematical review has not been completed.** No numerical experiment is a
universal-proof premise, and no formal proof assistant verification is claimed.

The statement concerns every full-dimensional convex polytope with at most
six genuine vertices, with nonoverlapping face interiors after cutting only
original edges. Net-boundary contact is allowed.

## Seven six-vertex types

| Type | Existence argument |
| --- | --- |
| Pentagonal pyramid | A vertex adjacent to all others: its original edge star is a shortest-path star |
| Simplicial type with two degree-five vertices | The same adjacent-to-all vertex-star lemma |
| Remaining type with a degree-five vertex | The same vertex-star lemma |
| Triangular prism | The existing dome argument, using a quadrilateral as base |
| Octahedron | [Selected H/R proof](LEMMA_F_CHORD.md), including both source-curvature branches and all ties |
| Octahedron minus an edge | [Complete original-edge proof](MINUS_EDGE_PROOF.md): failed direct cuts force complementary-source gates |
| Prism with one diagonal | [Seven-candidate proof](PRISM_EDGE_PROOF.md): six original near-stars and one triangular-chain fallback |

For the dome dependency, see Joseph O'Rourke's [author-hosted treatment of unfolding polyhedra](https://www.science.smith.edu/~jorourke/Papers/PolyUnf0.pdf), section “Domes”. A dome has a base facet sharing an edge with every other facet. Any quadrilateral of the triangular-prism graph has that property, without requiring parallel metric bases.

The first four are the repository's earlier arguments. The status overview
contains their statements, references, and illustrations. This map does not
replace those dependencies or claim a new independent proof of them.

For four vertices, the tetrahedron has an adjacent-to-all vertex. At five
vertices, the square pyramid has its apex and the triangular bipyramid has
any equatorial vertex adjacent to all others. The same shortest-path star
lemma therefore handles those smaller full-dimensional cases.

## New dependencies that deserve focused review

| Step | Exact claim to review | Where |
| --- | --- | --- |
| Flat completion | Selected octahedral inequalities remain valid with flat uncut auxiliary hinges | [Flat-hinge audit](OCTA_FLAT_HINGES.md) |
| Cofacial comparison | Removing the split comparison quadrilateral leaves the same original-face tree | [Star comparison](COFACIAL_STAR_REDUCTION.md) |
| Curvature gate | Fan<=pi and slit+fan>=pi supply every non-Case-A premise | End of [star comparison](COFACIAL_STAR_REDUCTION.md) |
| Wider Case A | A short cut side and apex angle <=(pi+theta)/2 separate the full convex apex cones | [Wider cone lemma](CASE_A_WIDE_CONES.md) |
| Nonobtuse middle | The middle triangle then has both cut sides strictly short; the angle-sum condition supplies a safe side | Same lemma |
| Minus switching | Four positive angle identities prevent both source tests failing | [Complementary sources](MINUS_COMPLEMENTARY_SOURCES.md) |
| Prism chain | A reference star at vertex 2 proves every pair except the two quadrilaterals in the fallback | [One-pair reduction](PRISM_ONE_PAIR.md) |
| Prism sharp fan | Three angle identities force the fallback's wider bounds if the first candidate escapes them | [Sharp-fan switch](PRISM_SHARP_FAN_SWITCH.md) |
| Prism gate | An obtuse middle at one candidate gives a nonobtuse middle at the fallback | [Gate switch](PRISM_GATE_SWITCH.md) |
| Exhaustion | Every failed direct-cut branch forces one of those gates | [Minus proof](MINUS_EDGE_PROOF.md), [prism proof](PRISM_EDGE_PROOF.md) |

The published shortest-path star theorem is used only for nonoverlap of
that reference star. The historically false claim of an entirely empty
infinite exterior wedge is not used; COFACIAL_STAR_REDUCTION.md records
that distinction and the exact published reference.

## Self-audit completed in this continuation

The new proofs were checked for original versus auxiliary cuts, original
quadrilateral apex cones, copied edge lengths, positive curvature and link
slacks, same-net use of every pair premise, and all equality branches.
The [finite graph enumeration](results/six-vertex-type-enumeration.txt) was
replayed and again returns seven types. The [prism reflection](results/prism-reflection.verification.json)
preserves the facets and seven-candidate family. The three sharp-fan angle
identities also vanish coefficient by coefficient
over the exact rational polynomial ring after eliminating one angle per
face. This verifies the algebraic identities for all assignments satisfying
the face-angle sums, not just at sample solids.

Former failed nets, exact curvature-boundary examples, and full nine- and
ten-parameter families have independent all-original-face-pair certificates
for successful choices. The selectors reject unresolved uniform choices on
a box. These checks are evidence about implementation and the explicit
certified domains, and are not substituted for a proof of universal coverage.

## What is not claimed

* Independent review or community acceptance of the new research proofs.
* Formal verification of the geometric dependency chain.
* The stronger original every-slit Lemma F.
* The narrower old two-tree minus-edge conjecture, whose separate ledger
  remains 7 of 28 simultaneous-failure classes excluded.
* A single fixed cut tree that works for every prism or every minus-edge shape.
* A finite numerical experiment proving the universal theorem.

The next mathematical task is an independent audit of the complete chain,
with any discovered gap reflected promptly in the status overview.

## Reproduction of the last proof checks

    python3 -m n6.prism_angle_identities
    python3 -m n6.prism_edge_examples
    python3 -m n6.prism_switch_examples
    durer_small_n/.venv/bin/python -m unittest discover -s n6/tests

The completed suite had 269 passing tests before the final two switching
checks, which passed separately. No proof-assistant verification is implied.
