# Two inward patches: the genuine remaining obstruction

**13 September 2026 · Exact example and a smaller proof target.** The
two patches can prefer opposite poles, and both can extend beyond their
receiving wedge plus the curvature gap. That situation is real, even for
a planar pentagonal equator. It does not imply overlap: the exact example
below has six independently certified safe star-plus-slit nets.

[Overview](index.html#bipyramid) ·
[Proved curvature branches](BIPYRAMID_OVERNIGHT.html#receiver-gate) ·
[Patch notation](BIPYRAMID_PATCHES.html)

## 1. A small integer example defeats both cone shortcuts {#example}

Use these exact coordinates, with the equator in the displayed cyclic order:

| Vertex | Coordinates |
| --- | --- |
| $u_0$ | $(-75,4,0)$ |
| $u_1$ | $(-60,-7,0)$ |
| $u_2$ | $(12,-10,0)$ |
| $u_3$ | $(54,-7,0)$ |
| $u_4$ | $(81,0,0)$ |
| $v$ | $(18,-8,1)$ |
| $w$ | $(-20,-3,-5)$ |

The ten triangular facets have strict supporting-plane certificates.
Their patch pattern is **FCCBC**: $Q_0$ points forward into $Q_1$, and
$Q_3$ points backward into $Q_2$. The two receiving patches are convex.
This is the canonical BCFCC class after cyclic relabelling/reflection.

The following rounded angles explain the geometry; the strict conclusions
are checked using rational intervals and trigonometric products.

| Fan pole | First bad extension $\ell_0$ | Receiver $Q_1$ | Other bad extension $\ell_3$ | Receiver $Q_2$ | Gap $\kappa$ |
| --- | ---: | ---: | ---: | ---: | ---: |
| $v$ | $29.66^\circ$ | $20.79^\circ$ | $125.74^\circ$ | $160.16^\circ$ | $1.41^\circ$ |
| $w$ | $72.36^\circ$ | $156.08^\circ$ | $23.18^\circ$ | $10.37^\circ$ | $7.61^\circ$ |

At $v$, the first patch exceeds its receiver and the gap. At $w$, the
other patch does. In exact form,

$$\ell_0^v>\nu_1+\kappa_v,\qquad
\ell_3^w>\omega_2+\kappa_w.$$

So neither pole has both bad extensions short, and neither passes the
remaining one-long-extension cone test. The simpler rule of always taking
the blunter pole also fails that test.

Nevertheless, the slits $u_0,u_2,u_4$ give safe nets **at either fan pole**.
The [exact record](results/bipyramid-receiver-conflict.json) and
[replay checker](bipyramid_receiver_conflict.py) verify all 45 face pairs
for each of these six nets. No assertion about the four other candidates
is needed here.

This example refutes sufficient angular shortcuts, not the existence of
an edge unfolding. It shows why the remaining proof must use more of the
triangle geometry than the angular cones alone.

### How the strict failed inequalities are certified

Each pole has curvature in $(0,\pi)$. Multiplying its face-angle complex
factors gives the phase of $2\pi-\kappa_p$; conjugating gives the phase
of $\kappa_p$. Multiply by the receiver's angle factor. Its positive
imaginary part certifies that receiver angle plus gap is below $\pi$.
Both the extension and this bound therefore lie in $(0,\pi)$, where
cosine is strictly decreasing. The checker proves

$$\cos(\text{receiver angle}+\kappa_p)-\cos(\ell_i^p)>0.$$

All coordinates are integers. Square roots and divisions use outward
rational intervals; the saved positive margins are recomputed. The rounded
angle table is not a proof premise.

## 2. The opposing-chain class reduces to two face pairs {#chain}

Now consider **every** convex pentagonal bipyramid with pattern FCCBC,
not just the example. Write $a_p=\angle_p(Q_1)$ and
$b_p=\angle_p(Q_2)$ for the two receiver angles at pole $p$.

**Two-receiver chain reduction.** One can choose a fan pole so that the
star-plus-slit net with slit at $u_0$ has at most two unresolved face
pairs. If an extension is long, those are its petal against the two
triangles of the other receiving patch. Every other pair is proved safe.

First, sum the angle identities at $u_1,u_2,u_3$ and subtract the full
angle sums of $Q_1,Q_2$. With $\rho_0=f_0-\pi$ and
$\rho_3=e_3-\pi$, the result is

$$\rho_0+\rho_3=
\omega_1+\nu_1+\omega_2+\nu_2
-\kappa_{u_1}-\kappa_{u_2}-\kappa_{u_3}.$$

Since $\rho_i=\ell_i^v+\ell_i^w$, at least one pole $p$ satisfies

$$\ell_0^p+\ell_3^p<a_p+b_p.$$

Call this strict inequality (1).

Choose such a pole and put the slit at $p u_0$. Both bad patches point
into the receiver chain $Q_1,Q_2$, so neither extends toward the outer
convex patch $Q_4$ or across this slit.

The two bad cones are disjoint by (1). If both extensions are short
($\ell_0^p\le a_p$ and $\ell_3^p\le b_p$), each meets only its own
adjacent receiver, and the entire net is safe.

Otherwise exactly one is long: both cannot be long because that would
contradict (1). Suppose $\ell_0^p>a_p$. Then $\ell_3^p<b_p$ and
$\ell_0^p<a_p+b_p$. The cone of $Q_0$ can enter $Q_2$'s fan wedge,
but cannot reach the wedge of $Q_3$. Its fan triangle stays in its own
wedge, so only its petal can meet $Q_2$. The other bad patch reaches
only its adjacent receiver $Q_2$. All other patches are convex.

Adjacent pairs remain safe by their common uncut equator vertex. The
only unchecked pairs are therefore

$$V_0/W_2,\qquad V_0/V_2,$$

with the notation $W$ for the chosen pole's fan and $V$ for its petals.
If $\ell_3^p>b_p$ instead, reflection gives the two unchecked pairs
$V_3/W_1$ and $V_3/V_1$.

Thus **43 of 45 pairs are settled for a specifically selected candidate**
throughout this whole symbolic class. The remaining two are linked metric
questions; this count does not establish that most shapes are solved.
Equality in an individual short-extension comparison is safe, while (1)
is strict because the three intervening vertex curvatures are positive.

The angle-sum identity extends to any chain of convex receivers. The
two-pair conclusion here uses exactly two receivers and the pentagonal
ring; it should not be read as a proof for an arbitrary longer chain.

### The fan pair follows from the petal pair

In fact there is just **one independent separation question**. Suppose
$V_0/V_2$ is safe. The three edges of $W_2$ border, respectively, $V_2$,
$W_1$, and $W_3$. The first neighbor is safe by this premise, the second
by the common vertex $u_1$, and the third because the two bad cones
$Q_0,Q_3$ are disjoint under (1). An interior point of $V_0$ cannot lie
on any open edge of $W_2$: a small disk inside $V_0$ would overlap the
already-safe neighbor on that edge.

The petal $V_0$ has interior points outside $W_2$, near its own equator
edge in its own fan wedge. If it also had an interior point inside $W_2$,
a generic line segment between two such interior points would cross an
open target edge, which was just excluded. Thus $V_0/W_2$ is safe as well.
Reflection gives the corresponding implication for $V_3/W_1$.

The count remains 43 pairs already settled, with two linked pairs left;
it would be misleading to count the conditional implication as an
independent unconditional 44th separation. Proving the one remaining
petal/petal pair settles both and completes this pattern's selected net.

## 3. An auxiliary octahedron closes a further branch {#auxiliary}

The six-vertex work can finish the two remaining pairs under explicit,
checkable conditions. This is a geometric implication for a family of
shapes; the subsequent integer example is only one application.

**Auxiliary-octahedron bridge.** Use the pole $p$ from (1), and suppose
the long extension is $\ell_0^p>a_p$. Let $q$ be the other pole. Assume:

1. Deleting $u_4$ gives the convex octahedron with equator
   $u_0,u_1,u_2,u_3$ and poles $p,q$.
2. In that six-vertex hull, $q$ has at least as much curvature as $p$.
3. One of the endpoints $u_0,u_3$ has maximum curvature among that hull's
   four equator vertices. All comparisons here concern the reduced hull.

Then the original seven-vertex net from the chain reduction is safe.

Apply the six-vertex [paired-pole rule](../n6/PAIRED_POLE_RULE.html) to the
auxiliary octahedron: cut the source star at $q$ and slit at the stated
endpoint. Its whole net is nonoverlapping. The three consecutive patches
$Q_0,Q_1,Q_2$ are unchanged in the reduced hull. Both endpoint slits leave
their internal fan joins $pu_1,pu_2$ uncut, and all three equator hinges
remain uncut. Their connected developed placement is therefore congruent
to their placement in the original seven-vertex candidate.

In particular the auxiliary theorem separates $V_0$ from both triangles
of $Q_2$. These are exactly the two remaining pairs. The chain reduction
settles every other pair in the original net, proving the conclusion.
The auxiliary closing edge $u_3u_0$ is not used as a cut or inserted into
the original net; it serves only to justify those two face separations.

For a long $Q_3$, reflection uses deletion of $u_0$ and auxiliary equator
$u_1,u_2,u_3,u_4$, with an endpoint maximum at $u_1$ or $u_4$.
Ties in the auxiliary source and slit comparisons are allowed by the
six-vertex theorem. The octahedral bridge needs these orders; the
other deletion types have the simpler argument just below.

**The integer example satisfies this branch.** With $p=v$, delete $u_4$.
The reduced curvatures, rounded only for explanation, are

| Vertex | $u_0$ | $u_1$ | $u_2$ | $u_3$ | $v$ | $w$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Curvature | $293.45^\circ$ | $65.42^\circ$ | $11.06^\circ$ | $337.99^\circ$ | $1.64^\circ$ | $10.44^\circ$ |

Thus $w$ is the sharper auxiliary pole and $u_3$ the largest-curvature
auxiliary equator vertex. The exact checker proves these comparisons,
the reduced convex hull, and inequality (1), then independently separates
all 28 auxiliary face pairs. So the example that defeats both earlier
cone shortcuts is covered by a **proved family-level bridge** as well as
by its six individual safe-net certificates.

The paired-pole theorem is a written n6 dependency, undergoing separate
formalization. Its files are not changed by this argument, and the n7
checker does not claim to formalize that theorem.

**Further progress:** [the local pair analysis](BIPYRAMID_CHAIN_PAIR.html)
now excludes the small-fan pocket, proves the entire large-angle branch,
and extends the wider-apex separator with an explicit seventh-vertex
correction. Only its remaining small-angle configurations are open.

### Pole-edge and flat-cap reductions need no curvature orders {#other-caps}

The remaining six-vertex cap has boundary $p,u_3,q,u_0$. If it is
triangulated by $pq$, both poles are universal vertices in the reduced
hull. Cut all five edges at $q$, including $pq$. This is a shortest-path
star and its whole net is safe. The three consecutive original patches
$Q_0,Q_1,Q_2$ keep all their internal joins, so their placement is
congruent to that in the seven-vertex candidate. This proves the two
remaining separations at **either choice of fan pole**, with no curvature
ranking. The new edge $pq$ is only a comparison cut on the smaller hull.

If the cap is a planar quadrilateral, use its internal straight diagonal
$pq$ as the comparison cut. It is a shortest path because it realizes the
Euclidean distance. The same star theorem and congruent-three-patch
argument apply. Once again the actual seven-vertex net uses only its
original edges. Reflection gives the long-$Q_3$ case by deleting $u_0$.

These are all non-octahedral possibilities: the six inherited triangular
facets leave a four-edge cap, which is either a quadrilateral or has one
of its two diagonals. The reduced hull is full dimensional and its six
vertices remain extreme as a subset of the original vertices.

The exact example labelled `other-reduced-graph-Case-A` in
[the pair certificates](results/bipyramid-receiver-pairs.json) has the
$pq$ cap. Its replay verifies strict support and all 28 auxiliary face
pairs for both source choices. The flat-cap case is covered by the
written argument, not claimed as an additional sampled certificate.

## 4. Next proof question {#next}

When $\ell_0^p>a_p$, prove separation of $V_0$ from the whole convex
patch $Q_2$, or show that the other pole or a different slit repairs any
failure. The auxiliary bridge already does this when its three geometric
conditions hold; pole-edge and flat-cap reductions are also settled.
The remaining auxiliary branches are actual octahedra with the wrong
reduced pole ordering or an interior equator maximum. Check
which of those can coexist with the chain's one-long-extension condition;
do not assume the auxiliary hypotheses merely from six-vertex existence.

The other two distinct-receiver classes and adjacent same-direction
patches remain separate targets. The example above belongs to the
opposing-chain class and does not refute a more specific pole-choice rule
for either of those other classes.
