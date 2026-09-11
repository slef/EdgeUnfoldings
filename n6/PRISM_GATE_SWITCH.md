# Prism: a curvature gate and an obtuse middle angle force a safe switch

12 September 2026. Written geometric lemma, pending independent review.
Use the original face and angle notation of PRISM_SHARP_FAN_SWITCH.md.

## Statement

If

    kappa_2<=pi,
    kappa_0+kappa_2>=pi,
    kappa_0+kappa_1>=pi,

then one of the following original cut trees gives a nonoverlapping net:

    M=star(3)+20={03,13,34,35,02},
    T={02,12,25,35,45}.

The reflected statement exchanges 0<->4, 1<->3, 2<->5. In particular,
its hypotheses are kappa_5<=pi, kappa_4+kappa_5>=pi, and
kappa_3+kappa_4>=pi, with M'=star(1)+54 as the near-star alternative.

## Proof

The first two hypotheses are precisely the fan bound and curvature gate
for the cofacial reduction at source 3, route endpoint 0. All obligations
in M except B/E are proved. The remaining middle triangle is F=345,
with source angle F_3 and middle-base curvature sum kappa_4+kappa_5.

If this triple is Case B, M is safe. If it is Case A and F_3<=pi/2,
the nonobtuse-middle corollary of CASE_A_WIDE_CONES.md makes M safe.
We may therefore assume F_3>pi/2. The ordinary angle sum in triangle F
then gives F_5<pi/2.

The reference-star theorem PRISM_ONE_PAIR.md makes all pairs in T safe
except B/D. View that pair around lower cap A, with base 01 and copied
apex 2. The third hypothesis gives

    kappa_0+kappa_1 >= pi > A_2,

so this view is Case B. If its intervening central angle sum
T_A=pi-C_3+E_1 is at least pi, the base-cone lemma separates B/D.
Otherwise the upper view around cap F has central sum
T_F=2*pi-T_A>pi. Its Case B is safe by the base-cone lemma. Its Case A
has middle angle F_5<pi/2, so it is safe by the nonobtuse-middle corollary.
Thus B/D is safe in every alternative, and T is a whole original-edge net.

The Case A angle-sum premise is valid for these polygonal outer faces:
B_5+D_5=Gamma_5-F_5<2*pi-F_5+kappa_3+kappa_4=pi+theta_5.
The same identity at source 3 has the additional positive fourth angle.
All copied side lengths are actual equal edge copies, and each convex
quadrilateral lies within its apex cone. Thus no triangle-only premise
has been silently transferred to a quadrilateral.

All equality cases in the stated hypotheses are included. Equality in a
middle Case A/B threshold is assigned to Case B, and a right middle angle
is assigned to the nonobtuse branch. Both original quadrilaterals stay whole.

## Immediate applications

If vertex 0 is sharp and vertex 2 is low, all three hypotheses hold.
If vertex 4 is sharp and vertex 5 is low, use the reflection. More generally,
0 itself need not be sharp: a sharp vertex 1 supplies the third condition,
and failures of its own direct cuts can force the second. The complete
exhaustive argument is in PRISM_EDGE_PROOF.md.
