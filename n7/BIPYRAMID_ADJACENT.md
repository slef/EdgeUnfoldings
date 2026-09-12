# Two adjacent inward patches: the final two-patch case

**13 September 2026 · Complete written proof.** The adjacent same-direction
class **FFCCC**, canonical **BBCCC**, is now covered. Consequently **every
convex pentagonal bipyramid with at most two inward patches has a
nonoverlapping edge unfolding**. The remaining symbolic classes have
three or four inward patches: eight classes, with their large-pole and
aligned-pole families already proved.

The whole pentagonal bipyramid remains open. The argument below is not a
numerical extrapolation, and it does not require a pole-curvature order.
In fact this adjacent-run theorem works for any ring size when these are
the only two inward patches.

[Overview](index.html#bipyramid) · [Radial receiver lemmas](BIPYRAMID_RADIAL.html) ·
[All patch classes](BIPYRAMID_PATCHES.html)

## What makes this case different {#idea}

Both bad patches lean forward, one immediately after the other. The first
therefore points into another bad patch, so the convex-receiver theorem
cannot be applied to that first pair directly.

Instead, compare **where the two patches end around a pole**. If the first
ends earlier and the second reaches only its convex neighbor, the net is
safe. If that ordering fails, the second bad patch fits inside the first
patch's triangular indentation. Its pole copy is then unusually close to
the fan center. That distance bound is precisely what the radial argument
needs.

## 1. The two comparisons and the finite rule {#rule}

Normalize the pattern to $Q_0=F,Q_1=F$, with every other patch convex.
Write $\ell_i^s$ for bad patch $i$'s extension at fan pole $s$, and
$\omega_i^s$ for its fan-face angle. Put

$$A_s=\ell_0^s-\omega_1^s-\ell_1^s,
\qquad B_s=\ell_1^s-\omega_2^s.$$

Thus $A_s\le0$ means the first bad patch ends no later than the second;
$B_s\le0$ means the second bad patch's extension is short into $Q_2$.

The angle identities imply

$$A_p+A_q=-\kappa_{u_1}<0,\qquad B_p+B_q<0.$$

The second inequality is the usual convex-receiver identity. For the first,
write the two inward corner excesses as $\rho_0,\rho_1$. The corner sum
at $u_1$ and full angle sum of $Q_1$ give

$$\rho_0-\rho_1=\omega_1^p+\omega_1^q-\kappa_{u_1}.$$

Substitute $\rho_i=\ell_i^p+\ell_i^q$.

**Theorem Adjacent.** The following rule gives a safe edge unfolding.

1. Choose a pole $q$ with $B_q\le0$.
2. If $A_q\le0$, use $q$ as fan.
3. Otherwise $A_p<0$ at the other pole. If $B_p\le0$, use $p$ instead.
4. In the remaining situation, keep $q$ as fan. The second bad patch is
   short there and long at the other pole; the proof below handles it.

In every branch, slit at $u_0$: cut that one fan edge and all the edges at
the other pole. For a pentagonal bipyramid these are six original edges.
Equalities in the two short/ordering tests are included.

## 2. Two useful containment facts {#containments}

Let $O$ be the chosen fan center, $a=u_1$, and $P_0,P_1$ the source
copies of the two bad patches. Since the second patch is inward at its
**far** vertex $u_2$, it lies in its outer triangle

$$H_1=\operatorname{conv}\{O,a,P_1\}.$$

**The first bad patch is safe against the entire triangle $H_1$.**
At the shared, uncut vertex $a$, this larger triangle has exactly the
same angular corner as the two faces of $Q_1$. The two faces of $Q_0$
and that corner of $H_1$ form consecutive sectors of total angle
$2\pi-\kappa_a<2\pi$. Filling the missing part at $u_2$ therefore
introduces no overlap with $Q_0$.

**A convex receiver, where it enters the preceding bad cone, stays in
that bad patch's outer triangle.** Apply this to $Q_2$ and $Q_1$.
The receiver is convex and contains $O$. A radial segment from $O$
to an interior receiver point in the extension sector cannot pass
through the open cut side $u_2P_1$: immediately beyond that side lies
the bad petal of $Q_1$, which is safe against $Q_2$ by the uncut fan
at $u_2$. Thus those receiver points lie in the indentation
$\operatorname{conv}\{O,u_2,P_1\}\subset H_1$.

This statement is used for interior overlap. A boundary ray that merely
touches the cone need not be treated as a strict containment assertion;
it cannot create an interior overlap. The argument is valid whether the
bad extension is short or long.

## 3. The ordered, short case {#ordered}

Suppose $A_s\le0$ and $B_s\le0$ at the chosen fan pole. With slit $u_0$,
the angular endpoints satisfy

$$\omega_0^s+\ell_0^s
\le\omega_0^s+\omega_1^s+\ell_1^s
\le\omega_0^s+\omega_1^s+\omega_2^s.$$

The first bad patch cannot reach any patch beyond $Q_2$; the second
reaches only its own receiver $Q_2$. The adjacent pairs $Q_0/Q_1$ and
$Q_1/Q_2$ are safe by their uncut equator vertices.

Any possible interior overlap $Q_0/Q_2$ lies within the cone of $Q_1$,
because the first bad patch ends no later than that cone. The clipped
receiver fact puts the overlap in $H_1$, which is already safe against
$Q_0$. This is a contradiction. All further patches are convex and
have disjoint fan wedges. Neither bad patch extends across the slit.
The entire net is safe.

## 4. When the ordering fails {#pocket}

The only remaining branch of the rule has

$$A_q>0,\quad B_q<0,\quad A_p<0,\quad B_p>0.$$

Use $q$ as fan. The inequality $A_q>0$ says that the whole outer cone
of $Q_1$ fits into $Q_0$'s extension sector:

$$\omega_1^q+\ell_1^q<\ell_0^q.$$

The source copy $P_1$ is therefore strictly inside the indentation

$$T_0=\operatorname{conv}\{a,q,P_0\}.$$

For clarity, the cone condition controls the side $qP_0$; the positive
uncut angle at $a$ places $P_1$ between the other two sides. Also
$|aP_1|=|aP_0|$ because these are copies of the same original edge.

Let

$$D_1=|qP_1|,\qquad \Delta_0=\operatorname{dist}(q,[aP_0]).$$

The unit-circle argument in the [shield proof](BIPYRAMID_RADIAL.html#shield)
already proves the intermediate bound

$$D_1<\Delta_0.$$

This part uses only the strict pocket containment and equal radii; it does
not require $Q_1$ to be convex. The angle argument in the
[long-receiver proof](BIPYRAMID_CHAIN_RULE.html#pocket) likewise gives

$$\ell_0^q<\frac{\pi-\kappa_a}{2}<\frac\pi2.$$

Here it uses only the positive corner of $Q_1$ at $a$, not convexity at
its other endpoint. Explicitly, the circle gives
$\ell_0^p>(\pi-\kappa_a)/2$, while the corner at $a$ gives
$\ell_0^p+\ell_0^q<\pi-\kappa_a$.

At the **other** pole $p$, $B_p>0$ means that $Q_1$ has a long convex
receiver $Q_2$. That receiver's source angle at $q$ is obtuse. Therefore

$$\omega_2^q>\frac\pi2>\ell_0^q.$$

This prevents $Q_0$ from reaching any patch beyond $Q_2$ in the chosen
$q$-fan. The only nonadjacent pair still needing attention is $Q_0/Q_2$.

## 5. The distance barrier closes that last pair {#finish}

Apply the shield lemma to the long $Q_1$ at the other fan pole $p$.
Its receiver's far equator vertex is $u_3$. Write
$d_3=|pu_3|+|qu_3|$. The distance from $p$ to that bad cut segment is
at most its distance to the segment's source endpoint, which is $D_1$.
The developed pole-to-pole length of the same patch does not depend on
which pole is chosen as fan. Hence

$$d_3<D_1<\Delta_0.$$

Now apply the cone-and-disk lemma to that same long receiver, viewing it
in the chosen $q$-fan. It places $Q_2$ in the union of the bad $Q_1$
cone and the radius-$d_3$ disk centered at $q$.

Inside the cone, an interior overlap with $Q_0$ would lie in $H_1$ by
the clipped receiver fact, and $Q_0$ is safe against $H_1$. Outside that
cone, $Q_2$ lies in the disk. The protruding part of $Q_0$ cannot enter
it: every such point has radius at least $\Delta_0>d_3$.
Its own fan wedge cannot meet $Q_2$ either.

Thus $Q_0/Q_2$ is safe. The adjacent pairs were already safe, and the
angular bound in the previous section excluded every farther pair.
This proves the whole selected net and completes the theorem.

## What is now left {#status}

Every necessary patch class with zero, one, or two inward patches is
covered: **7 of 15 classes** in total. The remaining **eight** consist
of five three-inward and three four-inward patterns. All cases with a
pole curvature at least $180^\circ$ are already proved; the full
aligned-pole family is also proved at arbitrary heights.

The next task is to extend these containment and distance arguments to
three inward patches, where a patch may have to pass through a longer
run before reaching a convex receiver. The whole graph remains open.

[Exact applications](results/bipyramid-adjacent.json) independently check
all face pairs of the chosen nets and the strict comparisons used in
those instances. The [replay checker](bipyramid_adjacent.py) separates
those finite checks from the universal written proof. Boundary equality
cases are covered by the argument above. No numerical search is a proof
premise, and no Lean formalization is claimed.
