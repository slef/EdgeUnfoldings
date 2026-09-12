# Seven vertices: first case map and transferable arguments

12 September 2026. This is a separate investigation in `n7/`, on branch
`codex/n7-unfolding`. The six-vertex arguments and Lean work are not modified.
The new arguments below are written proofs under self-review; no formal or
independent mathematical verification is claimed.

## What is covered now

We consider full-dimensional convex three-dimensional polytopes with seven
genuine vertices. Cuts must be original edges. Face interiors must be disjoint
in the resulting connected planar net; boundary contact is allowed.
A graph case is solved only if the argument covers **every convex realization
of that graph**, not just a convenient symmetric example.

There are **34 combinatorial types**. They split as follows, with priority
from top to bottom so that no graph is counted twice:

| Group | Graph types | Whole graph status | Reason / next obligation |
| --- | ---: | --- | --- |
| A. A vertex joined to all six others | 9 | Solved by an established theorem | Cut its six edges; this is a shortest-path star |
| B. A dome, after removing group A | 1 | Solved by an established theorem | Keep all other faces hinged to the base |
| C. Degree-five source sharing a face with its sole nonneighbor | 11 | Open, with a reduction | Only one quadrilateral changes position |
| D. Another source sharing a face with every vertex | 9 | Open, with a reduction | One, two, or three incident polygons change position |
| E. No source of either kind | 4 | Open | Two triangular core graphs, plus two graphs with quadrilaterals |

Thus **10/34 whole graph types are covered; 24 remain open**. This is a
combinatorial count, not a percentage of shapes, proof difficulty, or elapsed
research. The 10 covered cases use published results, independently of the
new six-vertex manuscript. The other 20 reductions do not depend on the
six-vertex existence theorem either: their general proof is given below.

The [overview](index.html) draws every graph and lists a specific candidate
cut tree and all remaining face-pair obligations. The [census data](results/catalogue.json)
retain vertex labels, facets, edge lists, and the exact paths used by the
pair reductions. IDs such as N7-A992 use stable Graph Atlas indices;
degree sequences alone are **not** used to identify graphs.

## Why this is the complete graph list

A convex three-polytope has a simple, planar, 3-connected graph, and conversely
Steinitz's theorem realizes every such graph. Its planar embedding is unique
up to reflection, so its facet cycles are determined by its graph.
We filter the complete Graph Atlas through these conditions, rather than
sampling coordinates. The result has edge-count distribution

| Edges | 11 | 12 | 13 | 14 | 15 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Types | 2 | 8 | 11 | 8 | 5 |

The lower edge bound follows from degree at least three; the upper bound is
$3n-6=15$. The [NetworkX atlas documentation](https://networkx.org/documentation/stable/reference/generated/networkx.generators.atlas.graph_atlas_g.html)
records completeness through seven vertices. We also ran the independently
implemented [plantri](https://users.cecs.anu.edu.au/~bdm/plantri/) generator
and matched all 34 outputs to the atlas by graph isomorphism. Its authors'
[manual](https://users.cecs.anu.edu.au/~bdm/plantri/plantri-guide.txt)
separately gives the same count. The saved comparison includes the source
archive hash and the label maps. These are exhaustive finite graph checks,
not geometric experiments or a proof-assistant formalization of enumeration.

## A. A universal vertex works for any number of vertices {#edge-star}

**Theorem.** If a convex polytope has a vertex $v$ joined by an original edge
to every other vertex, cutting precisely those edges gives a nonoverlapping net.

Each segment $vu$ is a shortest surface path: it attains the Euclidean distance
between its endpoints, which is a lower bound for every surface path. The
segments have disjoint interiors and form a spanning tree. Their unfolding
is therefore the shortest-path star at $v$. The established star theorem
allows the source to be a vertex: see Definition 1 and Theorem 4 of
[Kiazyk and Lubiw (2015)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SOCG.2015.390).
Nothing in this application uses $n=6$. It settles the nine indicated types.

## B. The dome theorem also has no vertex-count restriction {#dome}

A dome has a base facet sharing an edge with every other facet. Retain those
hinges and cut all remaining edges. [Pinciu (2007), Theorem 1 and Corollary 2](https://cccg.ca/proceedings/2007/01a4.pdf)
prove nonoverlap for this face-neighborhood unfolding. There are two dome
graphs here; the hexagonal pyramid is already in A. The additional case is
N7-A875, whose base is the pentagon with labels 1, 3, 2, 4, 5 in our atlas
embedding. The catalogue's facet witness, rather than this descriptive
label, is the source of truth.

## C–D. Move a few whole faces; the rest keeps a known safe placement {#cofacial-core}

Call $v$ a **cofacial source** if every vertex shares an original face with
$v$. Adjacent vertices automatically satisfy this condition. We extend the
six-vertex quadrilateral comparison to an arbitrary number of vertices and
to several incident polygons.

**Cofacial-core theorem.** At a cofacial source $v$:

1. Cut every original edge incident to $v$.
2. For each original face incident to $v$, choose exactly one boundary edge
   not incident to $v$ to remain as a hinge; cut the other such boundary edges.

These cuts form an original-edge spanning tree. In the resulting net, every
pair of faces **outside the nontriangular faces incident to $v$** has disjoint
interiors. Any overlap must involve at least one of those movable polygons.
The theorem does not say that any hinge choice makes the movable polygons safe.

### Proof

First make a comparison unfolding, temporarily allowing face diagonals.
In each face containing $v$, draw the diagonals from $v$ to all its other
nonadjacent corners. Together with the original edges at $v$, these are
straight segments to all other vertices. They are shortest surface paths.
Their interiors do not intersect, so cutting them gives a nonoverlapping
shortest-path star.

A nonneighbor can share at most one face with $v$. Otherwise two distinct
facets would intersect in two nonadjacent vertices, which is impossible:
their intersection must be a common vertex or edge. Also an original facet
cannot have a graph edge as a diagonal in its interior. Thus a face with
$m$ corners at $v$ contributes exactly $m-3$ distinct nonneighbors and the
same number of comparison diagonals.

The fan triangulation of each incident face consists of leaf triangles in
the comparison unfolding's uncut dual tree. Each such triangle has two cut
sides at $v$ and one boundary hinge away from $v$. Remove all the triangles
belonging to the nontriangular incident faces. Deleting leaves from a tree
leaves the other faces connected, with their same safe relative placements.

In the proposed original-edge net, each removed polygon is a single leaf,
attached by its one retained boundary hinge. Removing these whole leaves
leaves exactly the same connected core and the same hinges as before.
The core's development is unique up to a planar rigid motion, so all its
pairs stay safe.

For completeness the original cuts really form a spanning tree. For an
incident face $v,a,x_1,\ldots,x_k,b$, the vertices $a,b$ are neighbors of
$v$ and each $x_i$ is a distinct nonneighbor belonging only to this face.
Deleting one edge of the chain $a,x_1,\ldots,x_k,b$ leaves two paths, each
attached at one end to the radial star. Doing this in every incident face
adds each nonneighbor once and creates no cycle. All vertices are connected
and there are $d(v)+\sum k=n-1$ cuts. All are original edges. This also
shows directly why leaving the comparison diagonals cut would be an
invalid substitute for the required original-edge net.

### Exactly what the eleven quadrilateral cases gain

For a degree-five source at seven vertices there is only one nonneighbor.
If it is cofacial with the source, their common facet is a quadrilateral:
a larger facet would contribute more than one nonneighbor. The two possible
retained hinges are precisely the six-vertex comparison's two routes.
All pairs avoiding that quadrilateral are safe, without curvature assumptions.
Additional pairs follow from the two local facts below.

For the other nine cofacial types, the same proof handles the complete set
of incident polygons. In the displayed candidates, one type moves a single
pentagon, six move two quadrilaterals, one moves a quadrilateral and a
pentagon, and N7-A1005 moves three quadrilaterals. The candidate shown in the overview minimizes the
remaining pair count **within this finite family**, not among all possible
proof techniques or all geometric cut rules.

## Two local reductions that remain valid at seven vertices

**Uncut vertex fan.** If all faces on the unique uncut hinge path from face
$A$ to face $B$ contain the same original vertex $x$, they form a consecutive
fan there. Its angle is at most the full angle at $x$, strictly below $2\pi$.
Convexity puts each face inside its corner wedge. These successive wedges
have disjoint interiors, so $A$ and $B$ cannot overlap. Merely sharing a label
is insufficient: every face and hinge along the path must retain that vertex.

**Two hinges through an original face.** If the path is $A-Q-B$, the relative
placement is exactly a subplacement of Pinciu's unfolding of the neighborhood
of the original facet $Q$. Hence $A$ and $B$ are safe. This does not authorize
using an arbitrary auxiliary triangle as $Q$, or a path with extra hinges.

The census checks all **25,942 original cut trees** across the 34 graphs
with these two tests. They alone do not settle an extra graph beyond A–B.
They do give a concrete short residual list for every remaining graph.
For cofacial candidates we add the core theorem before reporting that list.

### A useful first target: N7-A992

Use the catalogue's seven original faces:

| Face | Cycle |
| --- | --- |
| 0 | 0–3–2–4 (quadrilateral) |
| 1 | 0–3–6 |
| 2 | 0–4–6 |
| 3 | 1–3–5 |
| 4 | 1–3–6 |
| 5 | 1–5–2–4–6 (pentagon) |
| 6 | 2–3–5 |

Choose source 3 and cut $03,13,23,35,36,04$. The quadrilateral stays
hinged on 24. Exactly **20 of its 21 face-pair obligations** are settled
by the preceding arguments. The one remaining pair is the quadrilateral
(face 0) against triangle 036 (face 1), along hinge path 0–5–2–1.

**Follow-up:** the [dedicated A992 investigation](A992.html) now gives an
exact counterexample to this fixed rule, and a certified family repaired by
moving triangle 036 to its other base-neighbor attachment. Both source-3
quadrilateral hinge choices can fail on the same shape. A longer-edge
shortcut also fails. The graph remains open; the next two-attachment lemma
has three explicit conditional pair obligations.

The 20 settled pairs remain valid. The count was never a percentage of the
whole graph proof: the last pair requires a different cut rule. The initial
census and exploratory history are retained in the overview and case page.

## E. Two core graphs and two original-edge restrictions {#core-graphs}

The four graphs without any cofacial source are:

| Graph | Structure | Further decomposition |
| --- | --- | --- |
| N7-A1212 | Pentagonal bipyramid | Five two-face patches around its two poles |
| N7-A1205 | Capped-octahedron graph | Octahedron graph with a new vertex over a triangular face |
| N7-A1167 | One quadrilateral, otherwise triangles | Either diagonal completes it to one of the two preceding graphs |
| N7-A1104 | Two quadrilaterals, otherwise triangles | Its four triangulations give the same two core graphs |

These are graph completions, **not unfoldability reductions**. A diagonal
inserted in an original quadrilateral is a flat auxiliary hinge and must
remain uncut. Likewise, deleting the cap vertex from the capped-octahedron
graph does not justify appending a tetrahedral cap to an arbitrary safe
six-vertex net. The replacement faces can collide with remote faces.
A cap-attachment lemma would need to prove that missing geometric step.

The separate [bipyramid arguments](BIPYRAMID_PATCHES.html) extend several
of the old octahedral lemmas. They cover three complete conditional patch
patterns and additional curvature-restricted families. The bipyramid graph
as a whole remains open here. The new [insertion arguments](BIPYRAMID_MORPH.html)
prove a convex deformation from six vertices, nondecreasing inserted
curvature, and at least two octahedral reductions. Carrying a safe net to
the target is the separate missing lemma; minimum curvature alone does not
preserve an arbitrary safe tree. The [overnight proofs](BIPYRAMID_OVERNIGHT.html)
now give a universal local slit rule and larger complete two-patch
curvature branches. The [first collision](BIPYRAMID_COLLISION.html) on
one exact insertion path is also classified.

## What does not automatically extend from the six-vertex proof

- The four-patch exhaustion in Lemma F does not cover a five-patch fan.
  There are more separated patch pairs and longer intervening chains.
- Lemma L's local geometry extends with an explicit curvature threshold;
  the proof that the old choice automatically meets that threshold used
  **four**, rather than five, equator vertices.
- The paired-pole rule's wider-angle identity closes a three-petal block
  using the one remaining petal. A five-petal fan leaves two petals outside
  that block. The old identity cannot simply be cited with a renamed index.
- Removing a degree-three vertex or merging two vertices does not by itself
  transfer an edge unfolding back to the original polytope.
- The legacy seven-vertex experiment keys some samples by degree sequence.
  Our catalogue does not reuse that identification: different graphs can
  have the same degrees. The old archived bipyramid solver runs returned
  unknown; they supply no proof premise here.

## Next work, in order

1. Focus on [pentagonal bipyramid insertion](BIPYRAMID_MORPH.html#next-lemma):
   analyze the first collision and prove a suitable change of cuts. Keep
   the alternative deletion vertices as additional choices.
2. As a secondary route, work on the single residual pair of N7-A992, with an explicit alternative
   tree if its fixed candidate fails. This would settle one additional whole graph.
3. Use the five-patch census to attack the still-open bipyramid patterns,
   especially two inward patches. This is the closest structural continuation
   of the octahedron work.
4. Prove a controlled cap-attachment lemma for N7-A1205. Preserve the six-vertex
   proof as a dependency rather than editing it while the Lean audit runs.
5. Track flat auxiliary hinges when applying either core theorem to the two
   nonsimplicial core graphs. A proof that needs to cut the new diagonal is
   not enough.

Every later update should retain the earlier status in the overview history.
New experiments must be labelled as examples; a whole graph changes status
only after its universal argument and hypotheses are written down.
