# Every convex prism with one diagonal has an original-edge unfolding

12 September 2026. **Complete written geometric argument, pending independent
mathematical review.** Numerical experiments and individual certificates are
not premises. This theorem is for the six original faces

    021, 0352, 013, 1254, 143, 345,

of every full-dimensional convex realization with this exact face lattice.
Both quadrilateral facets remain whole in the final net.

## The seven-candidate algorithm

Consider the six original degree-four-star-plus-one trees:

* star(1) plus one of 52,53,54;
* star(3) plus one of 20,21,25;

and the extra tree T={02,12,25,35,45}. At least one of these seven trees
has disjoint original face interiors. The proof gives an exhaustive rule
for selecting among them using curvature and middle-angle tests.

## Case 1: all curvatures are at most pi

The existing OCTA_FLAT_HINGES.md theorem supplies one of the six original
near-stars, including equality. It leaves the auxiliary diagonals 05 and
24 uncut. Recover the two original quadrilaterals along those hinges.

For the other cases, at least one curvature is strictly greater than pi.
Call any vertex with curvature at least pi sharp.

## Case 2: vertex 2 or 5 is sharp

Apply PRISM_SHARP_FAN_SWITCH.md. If both are sharp, T is already proved
safe by PRISM_TWO_SHARP_ENDS.md. If just one is sharp, the sharp-slit
near-star at the opposite low fan either passes its Case B/wider Case A
tests, or three exact angle identities prove T safe. This completes every
shape in this case, with equality included.

Hence in the remaining cases kappa_2<pi and kappa_5<pi.

## Case 3: vertex 0 or 4 is sharp

If 0 is sharp, then

    kappa_0+kappa_2>pi,   kappa_0+kappa_1>pi.

The fan at 2 is low. These are the hypotheses of PRISM_GATE_SWITCH.md,
so either star(3)+20 or T works. If 4 is sharp, its reflected gate lemma
supplies star(1)+54 or T. No original degree-three vertex is used as an
impermissible four-cut source.

## Case 4: an original degree-four source is sharp

Only vertices 1 and 3 remain eligible sharp vertices. Reflect if necessary
so vertex 1 is sharp. Its opposite is 5. The permitted original fifth
endpoints are c in {2,3,4}. If any obeys

    2*kappa_c+kappa_5>=pi,

use star(1)+5c, by the high-source weighted-threshold theorem in
OCTA_FLAT_HINGES.md.

Otherwise all three tests fail strictly. In particular, add the failures
for c=3 and c=4 to obtain

    kappa_3+kappa_4+kappa_5 < pi.

Gauss--Bonnet, whose total is 4*pi, gives

    kappa_0+kappa_1+kappa_2 > 3*pi,
    kappa_0+kappa_2 > 3*pi-kappa_1 > pi,

because every genuine convex vertex has curvature strictly below 2*pi.
Also kappa_0+kappa_1>pi since vertex 1 is sharp. With the low fan at 2,
these are exactly the hypotheses of PRISM_GATE_SWITCH.md. That lemma
supplies star(3)+20 or T. Thus the failure of the direct rule forces a
successful alternate source or the extra tree. Reflection handles source 3.

The four cases exhaust every possible actual curvature assignment. Each
branch yields one entire net whose own original face pairs are safe. This
proves original-edge unfoldability for the whole prism-with-one-diagonal type.

## Boundary, topology, and dependency audit

Every final tree is one of the seven listed original-edge trees. No branch
uses 05 or 24 as a cut. T's single-pair reduction compares with a shortest-
path star that cuts 23 and 24 inside original quads, but those are reference
paths only; its triangular chain is inherited by T without splitting its quads.

The original polyhedron has six genuine vertices, positive curvatures below
2*pi, nondegenerate triangular faces, and strict convex quadrilateral facets.
Flat auxiliary hinges are explicitly permitted by the earlier audit. This
proof does not silently include collapsed face lattices or zero-curvature
inserted vertices. Net boundaries may touch; face interiors do not overlap.

All non-strict thresholds route to a closed proved case. The only sums of
failed inequalities are strict failures of tests whose equality cases would
already have succeeded. No unique maximum, generic position, compact global
coordinate cover, or uniform positive clearance is assumed.

Dependencies are the selected octahedron theorem with flat hinges, the
cofacial curvature-gate reduction, the published shortest-path star theorem,
the base-cone and wider apex-cone lemmas, and the three displayed angle
identities. The new arguments are in PRISM_ONE_PAIR.md,
PRISM_SHARP_FAN_SWITCH.md, and PRISM_GATE_SWITCH.md. All deserve independent
mathematical review. Exact hypothesis checks and net certificates are useful
consistency checks, not formal verification of this written proof.

## Relation to n=6 and stronger questions

Together with MINUS_EDGE_PROOF.md and the five previously written type
proofs, this completes the repository's written argument for all seven
six-vertex types. This is a research proof awaiting independent review,
not a claim that a community-verified result or formal proof has been obtained.
The original every-slit Lemma F and the narrower fixed-two-tree minus-edge
conjecture remain separate stronger questions and are not proved here.

## Exact illustrations of the actual switches

The critical sharp-fan branch is nonempty: in the saved
[sharp-switch family](results/prism-switch-sharp-family.verification.json),
E_1 is obtuse and D_1 strictly fails the simple wider-angle bound. The
three identities supply the fallback, and every original face pair of T
also has an independent certificate throughout the nine-parameter family.
The [gate-switch family](results/prism-switch-gate-family.verification.json)
certifies the obtuse F_3 and acute F_5 conditions and all original pairs.
These examples validate the branch implementations; they are not proof
premises or a cover of the universal shape space.
