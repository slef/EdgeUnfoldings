# Direct assessment of DiBiase's octahedron argument

Source: Julie DiBiase, *Polytope Unfolding*, Smith College honors thesis, 1990.
Printed page numbers are used below; PDF page numbers are eight greater.
This is a mathematical assessment of the supplied thesis, not a literature-status
claim based on later citations of its theorem.

## Assessment

The octahedron argument is incomplete as written. There is now an exact
counterexample to the **DF entry of its displayed unfolding chart**, in addition
to the previously identified missing justification for moving the final face.
This does not disprove existence of an edge unfolding for the octahedron.

Chapter 3 explicitly restricts itself to triangulations (p. 39), and Fact 3
states that every face is a triangle by assumption (p. 41). It lists two
six-vertex types. Its charts therefore do not by themselves handle the other
five six-vertex types with polygonal facets.

The relevant argument is Section 3.5.2, pp. 72–77, with its completed chart in
Figure 3.29, p. 78. Lemma 3.6 on p. 75 argues that a depicted intersection
requires an obtuse angle of face G, and that another attachment would require
a different angle of G to be obtuse. On p. 77 the argument is extended by
symmetry to the other potential intersections.

For a complete proof, this needs a precise hypothesis for the obtuse-angle
implication, an exhaustive list of possible obstructions after the move, and
a justification that the preceding moves allowed by Lemma 3.5 have not
invalidated earlier entries of the chart. A pairwise repair is not automatically
a simultaneously nonoverlapping unfolding.

## Exact failure of the chart's DF entry

Use the vertex numbering visible in Figure 3.27. An example is:

| Thesis vertex | Coordinates |
|---|---|
| 1 | `(1,-1,-4)` |
| 2 | `(-3,-4,3)` |
| 3 | `(0,0,0)` |
| 4 | `(-1,-3,0)` |
| 5 | `(1,0,0)` |
| 6 | `(3,0,-6)` |

The facet sets are:

```
root = 123    A = 124    B = 235    C = 136
D    = 245    E = 356    F = 146    G = 456
```

The hinges in Figure 3.17(d)/3.29 are:

```
root-A, root-B, root-C, A-D, B-E, C-F, D-G.
```

Equivalently, the cut edges are `14, 25, 36, 46, 56`. The exact checker verifies
all 24 strict supporting-plane signs of this convex octahedron. It then
develops D and F along the unique hinge path `D-A-root-C-F` and verifies six
strict separating-axis overlap witnesses. Thus the two triangle interiors
overlap. The independent older rigid-motion development and polygon clipping
agree numerically; the conclusion relies on the rational interval signs.

Figure 3.29 labels DF as excluded by Lemma 2. The example refutes that entry
for this fixed displayed tree. It does not purport to refute every possible
precise version of Lemma 3.2, whose geometric hypotheses are stated through
figures and separation language.

Moving only G to D, E, or F does not change the seven-face core or the
`D-A-root-C-F` development, so none of those three choices repairs this overlap.
A strategy also changing D, E, or F may still work and is worth investigating.

Reproduce the exact check with:

```
python3 -m n6.polycert verify-overlap n6/results/thesis-chart-DF.certificate.json
```

The certificate's vertices are zero-based, with thesis labels `[1,2,3,4,6,5]`.
Its faces have indices `root,A,B,C,D,E,F,G = 0,1,2,3,4,5,6,7`.
Both the mapping and the source of the attachment pattern are recorded in it.

## Useful ideas retained

1. **Move a leaf face to another neighboring facet.** This changes a single
   hinge and preserves a cut-tree unfolding. It gives a finite, explicit family
   of candidate trees and a possible repair rule. The correct obligation is that
   at least one complete tree works, or that a sequence of repairs has a proved
   termination measure.
2. **Keep the dual tree shallow.** The thesis's cyclic three-arm trees differ
   from the previously integrated 24 near-star trees. They are additional
   candidates for a region-covering certificate, rather than a duplicate of Z_k.
   `trees.thesis_family` enumerates all 48 such trees: eight root faces, two
   cyclic arm assignments, and three placements of G. Every one has 11 residual
   face pairs after the common-vertex fan check. The seven-face core itself has
   six residual pairs: AE, BF, CD, DE, DF, EF. The full all-tree region search
   already includes this family among its 384 octahedron trees.
3. **Use a complete face-pair chart.** Every tree should have its own chart,
   distinguishing unconditional common-vertex pairs from metric obligations.
   A chart for one tree cannot be reused after a hinge move without checking
   which face developments changed.
4. **Use angle sum contradictions to choose among attachments.** A triangle
   cannot have two obtuse angles. If the geometric implication for *all* possible
   obstructions can be proved, this remains a potentially effective existence
   argument. The 10,000-sample exploratory run found no failure of the three
   placements conditional on a nonoverlapping seven-face core; that observation
   is not a proof and does not repair the core counterexample above.

## Reading scope

All Chapter 3 pages (printed 38–84) were rendered, its text was reviewed using
OCR alongside the scans, and the relevant geometric figures and complete
octahedron pages were inspected visually. OCR is navigation support, not the
authority for formulas or labels. The original scanned PDF is unchanged.
