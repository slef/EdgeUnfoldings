# The selected octahedron rule needs less than a sharpest source

**Later extension:** [the flat-hinge audit](OCTA_FLAT_HINGES.md) includes
original polygonal types at maximum curvature exactly pi, and proves
additional higher-curvature original-edge trees. Earlier strict-boundary
restrictions below record the scope of the earlier argument.

11 September 2026. Written geometric corollary of the complete proof in
[LEMMA_F_CHORD.md](LEMMA_F_CHORD.md). Independent review is still needed.
Numerical experiments are not premises.

## The stronger source-choice theorem

Let v,w be opposite vertices of a convex octahedron. Select a maximum-curvature
equator vertex c (R). The cut tree star(v) together with wc is nonoverlapping
under either of these conditions:

1. kappa_v >= pi; or
2. every vertex has curvature <= pi.

In the second condition **v may be any vertex**. In the first, v need not
be globally sharpest. Ties in R and equality in the curvature bounds are
included. This is not a theorem about arbitrary slits: R is retained.

## Audit each former use of H

The high-curvature finite-cut argument uses the spherical-link inequality
2*angle(w,v,a)<2*pi-kappa_v<=pi. This needs kappa_v>=pi, not global
maximality. Its projection and containment steps therefore remain valid
once the local lemma is available.

The low-curvature equal-length argument uses only that the three vertices
complementary to its neighboring blue face have curvatures at most pi.
The second condition supplies this for both cut targets, at any source v.

The through-fan part of Lemma L was already proved whenever kappa_v>=pi
or kappa_w<=pi (Section 3 of LEMMA_L_PROOF.md). In the obtuse original
pole-angle case, gamma<pi/2 and Gamma_w>=pi give its strict inequalities,
including kappa_w=pi. The across-slit argument and strict finite-edge
separation use R and kappa_v<2*pi, but no comparison of v with another
vertex. Thus all three local pairs and the boundary fact remain available.

The only additional global-maximality use in the whole-net reduction was
Case A's no-wrap bound. It requires

    nu_i+nu_j <= pi+kappa_u+kappa_u'.

If kappa_v>=pi, the left side is smaller than the whole source angle sum
Gamma_v<=pi, so the bound is immediate. If all six curvatures are <=pi,
the three vertices outside {v,u,u'} have total curvature at most 3*pi.
Gauss--Bonnet gives

    kappa_u+kappa_u' >= pi-kappa_v,
    pi+kappa_u+kappa_u' >= 2*pi-kappa_v = Gamma_v.

The left side of the required no-wrap inequality is at most Gamma_v.
This proves both no-wrap conditions at each triple, without H.

The base-cone partition has no curvature-ranking hypothesis. The small-fan
closed-curve contradiction uses R and Gauss--Bonnet to show

    kappa_c+kappa_w-nu_m >= (kappa_v+3*kappa_w)/4 > 0,

also without H. The surviving interior-fan implication uses local and
opposite-petal nonoverlap, which have now been supplied at this same slit.
These are all the dependencies; the complete selected-net proof follows.

## Why this matters for the quadrilateral-face cases

At an octahedral limit with a flat quadrilateral face, its artificial
diagonal must remain uncut. A forced sharpest source could be an endpoint
of that diagonal. The new second condition allows another source.

[NONSIMPLICIAL_LOW_CURVATURE.md](NONSIMPLICIAL_LOW_CURVATURE.md) uses this
freedom to prove original-edge existence for both remaining types when
all six curvatures are strictly below pi. Its proof supplies both the
refinements and the diagonal-avoiding trees; it does not appeal to
unrestricted octahedron existence alone.

This does not settle the every-slit Lemma F. It weakens the source
selection while retaining the maximum-curvature slit.
