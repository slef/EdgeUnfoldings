# Edge unfolding with five, six, and seven vertices

Research and computational notes, 7 September 2026.

**Outcome.** Every convex polyhedron with at most six vertices is reported as edge-unfoldable in the literature, with attribution to Julie DiBiase's 1990 undergraduate thesis. Five vertices also have a short proof using the spanning-star lemma. This investigation does **not** establish the seven-vertex case. It gives a complete small-graph census, useful theorem-based reductions, and a polynomial encoding of a counterexample search. Solver timeouts are reported as unresolved.

## 1. Existing results and a direct five-vertex argument

Julie DiBiase, *Polytope Unfolding*, undergraduate thesis, Smith College, 1990, is credited with the result for four, five, and six vertices by:

- Erik D. Demaine, Martin L. Demaine, and Ryuhei Uehara, *Zipper Unfolding of Domes and Prismoids*, CCCG 2013, pp. 43–48, introduction. [Author manuscript](https://dspace.jaist.ac.jp/dspace/bitstream/10119/11621/1/19458.pdf).
- Hugo A. Akitaya, Erik D. Demaine, David Eppstein, Tomohiro Tachi, and Ryuhei Uehara, *Ununfoldable polyhedra with 6 vertices or 6 faces*, Computational Geometry 103 (2022), 101857. [Publisher](https://www.sciencedirect.com/science/article/pii/S0925772121001139), [author bibliography](https://erikdemaine.org/papers/MinimalUnunfoldable_CGTA/).

The original thesis was not obtained, so this is a corroborated literature attribution, not a reconstruction or independent verification of its six-vertex proof. The counterexamples in the 2022 title are nonconvex; they do not contradict Dürer's conjecture.

The spanning-star lemma says that if a vertex is adjacent to every other vertex, cutting all edges incident to it gives a nonoverlapping unfolding. Catherine Schevon records the lemma, with Joseph O'Rourke, in a 1987 discussion [preserved by David Eppstein](https://ics.uci.edu/~eppstein/gina/unfold.html). It also follows from the star-unfolding theorem: each edge from the source is a shortest surface path because its length equals the ambient straight-line distance between its endpoints. See Boris Aronov and Joseph O'Rourke, *Nonoverlap of the star unfolding*, Discrete & Computational Geometry 8 (1992), 219–250, [paper](https://link.springer.com/content/pdf/10.1007/BF02293047.pdf).

There are exactly two five-vertex polyhedral graphs:

1. A quadrilateral pyramid: its apex is universal.
2. A triangular bipyramid: each of the three equatorial vertices is universal.

Apply the lemma. This proves the five-vertex statement for all convex realizations, without quantifier elimination.

## 2. Exhaustive combinatorial census

The script filters NetworkX's complete graph atlas through seven vertices for simple, 3-connected planar graphs. For each graph it extracts the unique spherical embedding up to reflection, enumerates primal spanning trees, checks that complementary dual edges form a spanning tree, and compares the count with an exact integer Laplacian cofactor in both primal and dual.

| Vertices | Graph types | Triangular-faced types | Total cut trees across one labeling per type | Maximum per type | Types with a universal vertex |
|---:|---:|---:|---:|---:|---:|
| 4 | 1 | 1 | 16 | 16 | 1 |
| 5 | 2 | 1 | 120 | 75 | 2 |
| 6 | 7 | 2 | 1,479 | 384 | 3 |
| 7 | 34 | 5 | 25,942 | 1,805 | 9 |

The counts are computed, not counts of all metric realizations or symmetry-inequivalent geometric nets. Every cut tree on the chosen labeled representative is retained.

At seven vertices, nine types are settled by the spanning-star lemma. Two types have a facet adjacent to every other facet, hence are domes in the sense of the 2013 paper. One is already among the nine universal-vertex types. The known dome-unfolding result therefore covers one additional type. **Twenty-four types, containing 17,058 cut trees, remain after these two particular reductions.** This is not a claim that no other known result applies to any of them.

Three of the five triangular-faced types have a universal vertex. The two that remain are:

| Type | Graph6 identifier in supplied census | Cut trees | Distinct dual paths of at least two edges |
|---|---|---:|---:|
| Octahedron with a tetrahedron stacked on a triangular face | `FJn^W` | 1,682 | 1,230 |
| Pentagonal bipyramid, combinatorial type | `Fhf~o` | 1,805 | 1,270 |

Here “pentagonal bipyramid” specifies the graph, not coplanarity or regularity of its five equatorial vertices. General convex realizations of this graph need not have a planar equator.

It is not sufficient to prove just these two cases: the 29 nontriangular-faced types include additional cases. Triangulating a flat face introduces artificial diagonals that must not become permitted cuts.

For larger orders, the established graph generator is Brinkmann and McKay's plantri; see [Fast generation of planar graphs](https://cs.anu.edu.au/~bdm/papers/plantri-full). The supplied atlas-based enumeration deliberately stops at seven vertices.

## 3. Exact existential formulation

Fix a polyhedral graph G, its ordered facets, and its dual D. Work with full-dimensional convex polyhedra, all listed vertices extreme, and precisely the prescribed facets. The convention in the code is that contacts between boundaries are permitted, but intersections of face interiors are forbidden. A strictly simple boundary would require additional boundary-contact predicates; that variant remains semialgebraic.

Let X be the 3D vertex coordinates. Use translation, rotation, reflection, and uniform scale to place the first three vertices of one facet at

    (0,0,0), (1,0,0), (a,b,0), with b > 0.

This leaves 3n−7 coordinate parameters. The remaining vertices are on the negative side of this oriented facet. This uses only similarities; an arbitrary affine normalization would change the unfolding problem.

For each facet f with cyclic vertices, let

    N_f = (x_b − x_a) × (x_c − x_a),
    h_f > 0,  h_f² = N_f · N_f,

using the first three vertices of the facet. Require all vertices of the facet to lie on its plane and every other vertex strictly on its inner side. For a nontriangular face, additionally require every other face vertex strictly on the interior side of each directed boundary edge within its plane. These polynomial constraints enforce the prescribed strictly convex facets and their incidence structure; they do not permit hidden coplanar facet mergers.

Denote their conjunction by R_G(X,H). For an undirected simple dual path π, let B_π(X,H) express that the two endpoint faces overlap in their interiors when developed along π. Then a counterexample exists exactly when

    ∃X,H : R_G(X,H) ∧
            ∧ over S ∈ ST(D) [ ∨ over π ⊆ S, |E(π)| ≥ 2 B_π(X,H) ].

Every symbol after the existential quantifier is expressible using polynomial equalities and inequalities. Adjacent faces joined directly by a hinge cannot overlap, so one-edge paths need no predicate. Boolean names for predicates are merely existential definitional abbreviations and can be eliminated.

UNSAT proves unfoldability for every realization of G. SAT for the **complete** tree family produces an actual counterexample, subject to checking the model and the implementation. SAT for a selected subset of trees says only that those trees fail somewhere. A timeout gives neither conclusion.

Your decidability argument is therefore sound. The complexity qualification is that the explicit formula contains a clause for every spanning tree. The standard PSPACE bound for ETR applies to the length of the formula submitted. If n varies, an exponentially expanded formula does not by itself establish a polynomial-space bound in the original graph size.

## 4. Developing faces without trigonometry or per-tree coordinate variables

There are two convenient equivalent implementations. Both keep one common set of geometric parameters for every tree.

For a triangular face with oriented vertices a,b,c, let s = |x_b−x_a|², d = (x_b−x_a)·(x_c−x_a), and h be twice its area. Given planar positions q_a,q_b, its third vertex is

    q_c = q_a + (d/s)(q_b−q_a) + (h/s) J(q_b−q_a),

where J rotates a vector by +90 degrees. The child face uses its own cyclic orientation, reversing the common directed edge relative to its parent. This selects the correct side of the hinge. Also

    h > 0,  h² = |(x_b−x_a) × (x_c−x_a)|².

All denominators s are positive. Thus a path development has rational coordinate functions in X and the face variables H. No sine, cosine, inverse trigonometry, or fresh square root for each tree is necessary.

The supplied implementation represents each developed facet by homogeneous planar coordinates Q_v/D, with a shared positive denominator D. For an arbitrary polygonal facet and an incoming oriented edge a,b, set

    s = |x_b−x_a|²,
    d_v = (x_b−x_a)·(x_v−x_a),
    k_v = N_f · ((x_b−x_a) × (x_v−x_a)),
    U = Q_b−Q_a.

Then

    Q'_v = h_f s Q_a + h_f d_v U + k_v J(U),
    D'   = D h_f s.

This is polynomial and applies directly to entire original facets. For triangles, k_c=h_f² and a positive common factor cancels, giving

    Q'_c = s Q_a + d_c U + h_f J(U),   D'=Ds.

A root triangle is placed at (0,0), (s,0), (d,h), which is its actual intrinsic shape multiplied uniformly by √s; this irrelevant common scale avoids a root-edge square root. The polygonal root uses the analogous homogeneous coordinates.

For n=7 there are at most 10 facets, so at most 14 coordinate parameters plus 10 positive normal-length parameters suffice: **24 real variables**, independently of how many trees are tested. Polynomial degrees and arithmetic expression sizes still grow with path length. Keeping few variables is not the same as making quantifier elimination cheap. An alternative worth benchmarking is introducing extra arithmetic-circuit variables to keep the constraint degrees low.

## 5. Exact overlap predicate

A developed facet is a convex polygon with a fixed counterclockwise ordering. For two such polygons A,B, their interiors overlap if and only if:

- for every directed edge of A, some vertex of B lies strictly to its left; and
- for every directed edge of B, some vertex of A lies strictly to its left.

This is the separating-axis theorem with boundary contact allowed. It handles containment and coincident polygons, which tests based solely on proper edge crossings miss.

If A uses homogeneous coordinates Q/D_A and B uses R/D_B, the left-side test for the edge u→v of A and vertex w of B has the sign of

    det(Q_v−Q_u, D_A R_w − D_B Q_u).

Both denominators are positive, so this is an exact polynomial sign test. All requirements in B_π are finite conjunctions and disjunctions of these strict inequalities.

## 6. Sharing paths and learning a small family of trees

The position of one face relative to another depends only on the dual-tree path between them. The branches attached elsewhere have no effect. Therefore B_π is shared by every spanning tree containing π.

For the pentagonal bipyramid, checking 1,805 full nets naively requires 1,805 × (45−9) = 64,980 potentially overlapping face-pair checks. There are only **1,270 distinct undirected paths** relevant to those checks. The improvement also shares common development prefixes and writes arithmetic expressions as a DAG.

For a fixed realization, every overlapping path gives a necessary clause for a successful hinge tree:

    at least one edge of π must be excluded from the hinge tree.

One short overlapping path can therefore eliminate many trees at once. This suggests combining a combinatorial tree solver with exact geometric predicates, rather than visiting each full net independently.

The most promising proof search is incremental:

1. Start with a small collection C of cut trees, obtained from standard constructions or difficult sampled realizations.
2. Ask an exact solver for a realization where every tree in C fails.
3. If UNSAT, C certifies universal unfoldability for this graph.
4. If SAT, search for a successful cut tree on that realization. A found tree must be new; add it to C.
5. If every tree fails, validate the resulting exact algebraic counterexample independently.

With complete exact subroutines, this terminates after finitely many additions because the tree family is finite. The practical hope is that the certificate uses a tiny fraction of all trees. Numerical sampling may propose trees; the final UNSAT step is what proves coverage. A solver assertion of UNSAT is still distinct from an independently checked proof certificate.

Other useful optimizations are polynomial-factor simplification using known positive factors, parameter-region subdivision, certified interval bounds for easy regions, and exact treatment of contact/degenerate boundary strata. A fixed positive overlap or separation epsilon cannot silently replace the original statement.

Combinatorial automorphisms help canonicalize graph or coordinate cases. They do not justify testing one cut tree per automorphism orbit on an arbitrary asymmetric realization. Relabeling must act on geometry as well as on the tree.

## 7. What was actually computed

- Complete graph/tree/path census through seven vertices, with primal/dual Matrix–Tree checks.
- Counts for the universal-vertex and dome reductions.
- A runnable polynomial formula generator for all original facet types.
- Independent numerical validation against polygon clipping for all 16 nets of two tetrahedra: zero overlapping nets for the right tetrahedron and two for a skew tetrahedron. This checks both positive and negative overlap outcomes, but is not an exact proof of universal correctness.
- A separate exact fixed-coordinate check of the right tetrahedron's 16 nets and a numerical metric check on developments containing the square face of a square pyramid.
- A small round-trip validation of the SMT2 arithmetic-DAG writer.

The initial QF_NRA tactic-solver runs timed out on a one-tree tetrahedron query (15 seconds) and a one-tree pentagonal-bipyramid query (30 seconds). These are calibration failures, not evidence about the conjecture. A first attempt to assemble the complete bipyramid query was interrupted during expensive eager processing; the generator was then changed to collect assertions first and export shared arithmetic definitions before invoking the solver. The final complete bipyramid query contains 206,743 shared expression nodes and was exported successfully (about 13 MB). Its subsequent solver stage was manually interrupted without a SAT or UNSAT answer; the configured timeout did not bound all processing. The exact status is recorded in `pentagonal-bipyramid-all-trees.result.json`.

No seven-vertex universal theorem or counterexample has been obtained here. The immediate research targets are to recover DiBiase's six-vertex proof, use its geometry to seed small tree families, and apply the incremental exact search to the two residual triangular-faced seven-vertex types before tackling every face-incidence stratum.
