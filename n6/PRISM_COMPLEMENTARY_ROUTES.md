# Prism: complementary routes when the two fan curvatures sum to at least pi

12 September 2026. Written geometric theorem, pending independent review.
The full prism-with-one-diagonal type remains open. Numerical tests are
not premises of the argument.

Use the original faces 021, 0352, 013, 1254, 143, 345. The two original
degree-four sources are 1 and 3; their octahedral opposites (fan centers)
are 5 and 2 respectively. The auxiliary diagonals 05 and 24 may not be cut.

## Theorem

If kappa_2<=pi, kappa_5<=pi, and kappa_2+kappa_5>=pi, then an original-edge
unfolding exists. All three equalities are included.

Together with PRISM_TWO_SHARP_ENDS.md this proves both the family with
both fan vertices sharp and this family where both are low but their
combined curvature is at least pi. This does not settle configurations
with just one fan sharp, or both fans below pi with sum below pi.

## A two-route lemma at one source

First use source 1, with fan 5. Its two cofacial routes cut 52 or 54.
Assume both curvature gates

    kappa_2+kappa_5>=pi,   kappa_4+kappa_5>=pi.       (G1)

The cofacial comparison in COFACIAL_STAR_REDUCTION.md applies to each.
Its curvature-gate extension supplies local, finite-cut and small-fan
premises. One opposite pair remains for each route, with middle base
34 (route 52) or 02 (route 54). Write nu_134 and nu_012 for the angles
at source 1 in those two middle triangles.

The sum of the two middle-base curvatures is

    (kappa_3+kappa_4)+(kappa_0+kappa_2)
        =4*pi-kappa_1-kappa_5
        =Gamma_1+Gamma_5
        >nu_134+nu_012.                            (1)

The final inequality is strict: the two displayed angles are only two
of the four positive original face angles at source 1, and Gamma_5>0.
Thus both routes cannot be Case A. One satisfies its own Case B condition
(middle-base curvature sum at least the corresponding middle angle),
and that same whole original net is safe by the cofacial reduction.

Reflect to source 3, fan 2. The two routes cut 20 or 25; their middle
bases are 45 and 01. The same argument works under

    kappa_0+kappa_2>=pi,   kappa_5+kappa_2>=pi.       (G3)

No successful pair is transferred from one net to another: equation (1)
selects a whole candidate whose remaining pair is already in Case B.

## The remaining failure forces a sharp original source

Assume the theorem's three hypotheses. If kappa_4+kappa_5>=pi, apply
(G1). If kappa_0+kappa_2>=pi, apply (G3). Otherwise both fail strictly:

    kappa_4+kappa_5<pi,   kappa_0+kappa_2<pi.

Gauss--Bonnet gives kappa_1+kappa_3>2*pi, so at least one original
source has curvature >pi. If it is source 1, choose original fifth cut
52. Its weighted threshold satisfies

    2*kappa_2+kappa_5 > kappa_2+kappa_5 >= pi.

The high-source flat-hinge theorem proves this entire net safe.
If source 3 is sharp, choose original fifth cut 25 and use the reflected
threshold 2*kappa_5+kappa_2>pi. This exhausts the alternatives.

Every final tree uses only original edges and leaves both quadrilaterals
whole. The old stronger claim that every slit is safe is not needed.

## Scope and the next residual cases

This theorem covers a continuous geometric family; it is not a claim
about a fraction of the entire shape space. The exact selector may fail
to choose a single tree uniformly on a large parameter box spanning its
switches, even when the pointwise existence theorem applies throughout.
That computational limitation is distinct from the mathematical result.

With the existing all-low and two-sharp-end theorems, an unresolved shape
must have some curvature >pi and either:

1. exactly one of the fan vertices 2,5 has curvature >=pi; or
2. both fan vertices are below pi and kappa_2+kappa_5<pi.

Each class has already-proved subfamilies. Neither is claimed empty.
