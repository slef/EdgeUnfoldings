# Every convex octahedron-minus-edge has an original-edge unfolding

12 September 2026. **Written geometric proof, pending independent review.**
No finite experiment, numerical search, or individual certificate is a
premise. The original quadrilateral is never cut by an added diagonal.

Label the original faces

    ACBD, ACP, APQ, ADQ, BDQ, BPQ, BCP,

with A=0, B=1, C=2, D=3, P=4, Q=5. We prove the theorem for every
full-dimensional convex realization with exactly these facets.

## Available proved ingredients

1. OCTA_FLAT_HINGES.md: the all-at-most-pi family is edge-unfoldable.
   Also, a degree-four source v with curvature at least pi gives a safe
   original star-plus-one tree whenever its original fifth edge wc obeys
   2*kappa_c+kappa_w>=pi. Flat auxiliary hinges are allowed; they are uncut.
2. COFACIAL_STAR_REDUCTION.md: source A or B changes only ACBD relative
   to a shortest-path star. Under fan curvature <=pi and the gate
   kappa_c+kappa_w>=pi, every obligation except one Case A pair is proved.
3. MINUS_COMPLEMENTARY_SOURCES.md: if A,B are below pi and
   kappa_C+kappa_A>=pi, kappa_C+kappa_B>=pi, one of star(A)+BC and
   star(B)+AC is safe. Their two residual Case A tests cannot both fail
   the four explicit angle-sum identities. Reflect for corner D.

Ingredient 3 in particular proves every sharp-C or sharp-D case. The
remaining step is to show that failure of the direct original rule at
sharp P or Q forces both complementary gates.

## Exhaustive choice of a branch

Every genuine convex vertex has curvature strictly between 0 and 2*pi,
and the sum of the six curvatures is 4*pi.

**All curvatures at most pi.** Apply ingredient 1.

**A or B has curvature at least pi.** Use it as source. Every possible
fifth edge at its opposite is an original edge. An equator maximum c
satisfies 2*kappa_c+kappa_w>pi by the existing maximum argument. Apply
ingredient 1. Equal source curvatures cause no problem.

**C or D has curvature at least pi.** If the preceding source branch
has not applied, A and B are both below pi. A sharp corner supplies both
gates in ingredient 3, so use its complementary-source theorem.

**Otherwise P or Q is sharp.** At least one is sharp because the all-low
case was already handled. Reflect if necessary so it is P. The original
neighbors of P are A,B,C,Q, its octahedral opposite is D, and the allowable
original fifth edges at D are DA, DB and DQ. If any c in {A,B,Q} satisfies

    2*kappa_c+kappa_D >= pi,                       (T)

use star(P)+Dc, by ingredient 1.

Suppose all three tests fail. Their failures are strict; equality would
have selected the preceding branch. In particular A and B are below pi/2.
Add the failures for B and Q:

    kappa_B+kappa_Q+kappa_D < pi.

Gauss--Bonnet now gives

    kappa_A+kappa_C+kappa_P > 3*pi,
    kappa_A+kappa_C > 3*pi-kappa_P > pi,           (G_A)

since kappa_P<2*pi. Add the failures for A and Q instead to get

    kappa_B+kappa_C > 3*pi-kappa_P > pi.           (G_B)

These are exactly the two gates of ingredient 3, with both fan choices
A,B strictly below pi/2. Use star(A)+BC or star(B)+AC as supplied by its
complementary-angle proof. This finishes the sharp-P branch. Reflection
finishes sharp Q.

These branches exhaust every possible curvature assignment of the actual
polyhedron. In every branch one original spanning cut tree is proved to
have all its face interiors disjoint. Therefore the whole original
minus-edge type is edge-unfoldable.

## What is, and is not, being combined

The fallback retains corner C in BOTH source choices. It does not assume
that the sharper source also has the right angle bounds. The complementary
angle identities prove that at least one entire candidate supplies its own
remaining Case A test; every other premise is already true in both.

The forbidden diagonal DC is used only in the auxiliary octahedral
bookkeeping. In the direct sharp-P branch the actual fifth cut is one of
DA, DB, DQ. In its fallback every cut belongs to the original source stars
and AC or BC. Thus no step splits the original quadrilateral ACBD.

All equalities in the branch tests are included. No uniform positive
clearance, generic curvature ranking, or compact parameter cover is needed.
The theorem concerns strict original convex facets and genuine vertices;
collapsed realizations with a different face lattice are not silently
included. Ordinary net-boundary contact is permitted.

The mathematical dependency chain still merits independent review. Exact
examples and parameter families are separate consistency checks of the
hypotheses and complete nets, not formal verification of this written proof.
The prism-with-one-diagonal type is still open; this result alone is not
a proof of the full n=6 theorem.
