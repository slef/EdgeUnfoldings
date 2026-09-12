# A992 continuation notes — 12 September 2026

These notes preserve ideas and failed routes. The positive geometric result
is written separately in [A992_CONES.md](../../A992_CONES.md). All research
remains in the n7 worktree. No six-vertex or Lean proof is modified.

## The roof-edge split

In the existing normal form, write $p_2=0$, $p_4=(1,0,0)$ and
$p_0=a p_3+b p_4$, with $a,b>0$, $a+b>1$ and $p_3$ above the base plane.
When $a\ne1$, the line 03 meets the base plane at

$$c=\frac{b}{1-a}p_4.$$

Thus $a<1$ puts c beyond 4 on the line 24; $a>1$ puts it beyond 2; and
$a=1$ makes 03 parallel to 24. These identities are exact. This is a
projective ordering split, separate from the R0/R6 metric-angle split;
no equivalence between the two splits has been proved.

When $a>1$, all seven vertices lie in the tetrahedron with vertices
**c, 0, 4, 6**. Indeed 3 lies strictly on segment c0 and 2 on segment c4.
Q lies in the tetrahedral face c04, E in c06, and 046 is a full tetrahedral
face. On the base plane, the supporting half-planes from Q, E, and 046
bound triangle c46. The original base pentagon lies in it. Faces 235,
135, and 136 replace the virtual corner c by a roof over its missing
part. This containment alone does not give a nonoverlapping net.

When $a<1$, c lies across the line 46 from 2. It violates the supporting
half-plane for face 046, so the same containing-tetrahedron construction
does not apply.

## A promising published theorem, with a specific obstruction

Benton and O'Rourke's [Unfolding Polyhedra via Cut-Tree Truncation (2007)](https://cccg.ca/proceedings/2007/03b4full.pdf)
proves that truncating a degree-three leaf of an unfolding cut tree preserves
nonoverlap and an empty-sector property. The truncation replaces the final
cut edge by a three-branch cut through the new triangular face. Tetrahedral
star unfoldings have the required empty-sector property. Section 4 also
permits the limit in which the remaining **cut** edge to the parent shrinks
to zero.

The a>1 containing tetrahedron suggests repeated truncation at c, starting
from the star centered at 0. A tentative order uses the base intersections
v = line(25) intersect line(c6), followed by
w = line(51) intersect line(c6), with successive new roof triangles.
The required ordering and convexity of all these intermediate cuts have not
been established for arbitrary realizations.

There is a further obstruction even if those intermediate steps are valid.
The final move to the desired vertices can collapse an **uncut** hinge at 6.
The naive limiting cut list is 03, 04, 06, 13, 23, 35, 36: it contains the
cycle 0–3–6–0 and disconnects E from the rest of the surface. Rejoining E
along 06, 36, or 03 gives the three candidate attachments, but the published
empty-sector theorem does not itself prove that one of these reattachments
is safe. A limit of nonoverlapping pictures can have disconnected face
interiors after its only hinge vanishes. It is therefore not an edge net of
the required kind. Do not promote this truncation route to a proof without
resolving that step.

The distinction between a vanishing cut edge and a vanishing uncut hinge is
essential. The source explicitly addresses the former; it does not license
the latter application.

## Searches retained from this continuation

`local_corner_search.py` deliberately explored negative x6 and large a, then
inserted vertices 1 and 5 just outside triangle 246. It found 154 apparent
Left failures extendible to the required full graph, among 14,000 attempts.
The finite run did not show a robust joint Left/Right failure. One discovery
was rounded and independently certified in
[a992-corner-six-counterexample.json](../../results/a992-corner-six-counterexample.json).
Its four strict angle-sign tests prove that it belongs to R6. Its Left
overlap and Right separation are separately certified.

`conditional_base_search.py` fixes each of those 154 local obstructions and
the five earlier ones, and varies only vertices 1 and 5. This is justified
as a search strategy by the localization lemma: the Left Q/E placement is
independent of these two vertices. Of 159 × 350 attempted extensions, 2,086
passed the floating geometry filter. There was no joint failure above the
recorded threshold. Near-zero values remain inconclusive. The seed, all
parameters of the best extension for each source, and the floating scores
are retained in the corresponding JSON file. This run is not evidence that
all possible extensions were covered.

## What to try next

Use the cone proof before any further search: actual Left overlap implies
either R0 or R6. For each, prove Right keeps E away from Q, 135, and 235.
In R0, both angles at 0 in triangles 046 and 036 are obtuse, with the stronger
squared-length inequalities written in the proof. In R6, curvature at 4 is
strictly greater than pi. These are necessary conditions on an actual Left
failure. Neither regime's defining inequalities alone imply overlap.

In both attachments the six-face base neighborhood remains fixed, and
vertex 6 is the same planar point. The two placements of E are related by
a rotation about that point through the curvature at 6, in the appropriate
orientation. An argument that this rotation escapes a forbidden region,
or an empty-sector argument adapted to the last truncation step, may be
more useful than another unconstrained fixed-tree search. This is a proof
idea, not an established repair theorem.
