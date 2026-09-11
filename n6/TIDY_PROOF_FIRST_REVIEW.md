# Earlier complete review draft — seven prism candidates

Preserved from the first complete reconstruction during the 12 September review.
The current [TIDY_PROOF.md](TIDY_PROOF.md) has the subsequent cap simplification.
All text below retains the scope and state of this earlier draft.

12 September 2026. **Separate draft in progress during the proof review.**
The original notes, alternatives, failures, figures and certificates are
preserved. This is a shorter presentation under self-audit, not independent
review or formal verification. Numerical experiments are not proof premises.

## Scope and structure

The claim concerns full-dimensional convex polytopes with at most six
genuine vertices. Only original edges may be cut; face interiors must be
disjoint, while net-boundary contact is allowed. The argument below uses
one geometric core, one minus-edge identity, and two prism switches. All
geometric details of the new common criterion and planar separators are
collected in [TIDY_CORE.md](TIDY_CORE.md). The longer original dependency
map remains [N6_PROOF_MAP.md](N6_PROOF_MAP.md).

## A short classification, without a computer enumeration

The graph of a convex three-dimensional polytope is simple, planar and
3-connected; every vertex has degree at least three. If some vertex is
adjacent to every other vertex, cut its original edge star. Each edge is
a shortest surface path, since it attains the Euclidean distance of its
endpoints. The shortest-path star theorem gives a nonoverlapping net.
The theorem includes a source at a vertex; see Definition 1 and Theorem 4
of [Kiazyk and Lubiw, SoCG 2015](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SOCG.2015.390).

For four vertices this always applies. For five, absence of degree four
would make all five degrees three, contradicting the even degree sum.
Now take six vertices without a degree-five vertex. In the complement H
of its graph, every degree is one or two. Thus each component is a path
P_j with j>=2 or a cycle C_j with j>=3. The partitions of six give just:

| Complement H | Original graph / exclusion |
| --- | --- |
| P_2+P_2+P_2 | Octahedron |
| P_4+P_2 | Octahedron minus one edge |
| P_6 | Prism with one diagonal |
| C_6 | Triangular prism |
| P_3+P_3, C_3+P_3, C_3+C_3 | All nine edges between the two triples are in the original graph: a K_(3,3), contradicting planarity |
| C_4+P_2 | Removing the two P_2 vertices leaves two disjoint edges: a contradiction to 3-connectivity |

The four retained graphs have the usual original facet structures, which
are unique for a 3-connected planar graph. This also identifies directly
the face lists used below. The triangular-prism graph is a dome: any one
of its quadrilaterals shares an edge with every other facet. The established
dome unfolding theorem applies without requiring parallel metric bases;
see the “Domes” proof in [O'Rourke's author manuscript](https://www.science.smith.edu/~jorourke/Papers/PolyUnf0.pdf).
Only the other three graphs need the new argument. The existing seven-type
computer enumeration is retained as a separate check, not a proof premise.

## The common rule and the original-face comparison

Write kappa_x for the curvature at vertex x, so 0<kappa_x<2*pi and
the six curvatures sum to 4*pi. Complete the three remaining graphs to
an octahedron by adding the missing quadrilateral diagonals as flat hinges.
The common theorem in TIDY_CORE.md says:

> If v,w are opposite and either kappa_v>=pi or all curvatures<=pi,
> then star(v)+wc unfolds whenever 2*kappa_c+kappa_w>=pi.

An equator maximum c always passes this threshold: four times its curvature
is at least 4*pi-kappa_v-kappa_w, so

    2*kappa_c+kappa_w >= 2*pi-kappa_v/2+kappa_w/2 > pi.

Thus the octahedron is settled by a sharpest source and an equator maximum,
including all ties. For the other graphs, every final cut below is checked
to be original, so the flat hinges rejoin whole original quadrilaterals.

We also use a useful comparison. Let an original degree-four source v
and its sole nonneighbor w be opposite corners of an original quadrilateral
Q with other corners c,d. In the shortest-path star at v, the fifth path
is the straight face diagonal vw. Splitting Q along it gives two leaves
attached along wc and wd. Remove them. In star(v)+wc, removing the single
leaf Q leaves exactly the same uncut tree of other faces, in the same
relative planar positions. Therefore every pair outside Q is safe.

Under **kappa_w<=pi and kappa_c+kappa_w>=pi**, the common cofacial gate
proves all non-Case-A obligations at this same slit. One opposite-petal
pair is already safe by the star comparison. Only the other pair's Case A
remains. Here are the middle bases for that remaining triple:

| Original type | Source / fifth endpoint | Middle base |
| --- | --- | --- |
| Minus edge | A / C or B / C | DQ |
| Minus edge | A / D or B / D | CP |
| Prism diagonal | 1 / 2, 1 / 4, 3 / 0, 3 / 5 | respectively 34, 02, 45, 01 |

If its base-curvature sum is at least its middle apex angle, it is Case B
and the whole candidate is safe. Otherwise the Case A separators in
TIDY_CORE.md apply to the full original outer-face apex cones. The comparison
uses only star nonoverlap; it does not assume an empty infinite exterior
wedge, a stronger claim that is false.

## The minus-edge switch in one identity

The original facets are ACBD, ACP, APQ, ADQ, BDQ, BPQ, BCP. Suppose
A and B have curvature below pi and

    kappa_C+kappa_A>=pi,   kappa_C+kappa_B>=pi.

Compare the two original-edge cuts star(A)+BC and star(B)+AC. The
cofacial-star and curvature-gate reduction leaves only ACBD/APQ in the
first candidate and ACBD/BPQ in the second. Each statement concerns the
whole candidate in question; safe pairs are not moved between candidates.

Set K=kappa_D+kappa_Q, nu_A=angle(DAQ), nu_B=angle(DBQ). If K>=nu_X
for either source X, its remaining pair is Case B and that net is safe.
Otherwise theta_X=pi-nu_X+K lies in (0,pi) for both sources.

Let q_X be the quadrilateral angle at X, mu_A=angle(PAQ),
mu_B=angle(PBQ), and tau=angle(APQ)+angle(BPQ)>0. The original face-angle
sums and the two curvatures give

    K+q_D=nu_A+nu_B+mu_A+mu_B+tau,
    q_A+q_B+q_C+q_D=2*pi.

Consequently

    theta_A+theta_B
      = (q_A+mu_A)+(q_B+mu_B)+(K+q_C+tau).

The final parenthesis is positive, so at least one source satisfies
q_X+mu_X<theta_X. Both of its positive outer face angles are then below
theta_X. The Case A cone lemma separates its remaining pair and completes
that entire original-edge net. Reflection gives the corner-D statement.

This short proof replaces the four comparisons in
MINUS_COMPLEMENTARY_SOURCES.md without discarding them. The exhaustive
curvature argument selecting this switch or a direct net is as follows.

* If all curvatures are at most pi, use source A and any equator maximum.
  Its four star edges and every possible fifth cut at B are original.
* If A or B has curvature at least pi, use that source and an equator maximum.
* Otherwise A,B<pi. If C or D has curvature at least pi, the complementary
  gates above hold, so use its two-source switch.
* Otherwise P or Q is sharp. Reflect to take P, opposite D. Its allowed
  fifth endpoints are A,B,Q. If one passes 2*kappa_X+kappa_D>=pi, use it.
  If all fail, adding the B,Q failures gives kappa_B+kappa_Q+kappa_D<pi.
  Subtracting from 4*pi and using kappa_P<2*pi yields kappa_A+kappa_C>pi.
  Adding the A,Q failures similarly yields kappa_B+kappa_C>pi. Both
  complementary gates are forced, so the two-source switch works.

These alternatives exhaust every actual curvature assignment. The only
auxiliary edge CD is never cut. Every branch supplies one complete original
net, establishing the minus-edge type.

## Prism: one fixed fallback with two views

Use original faces

    A=021, B=0352, C=013, D=1254, E=143, F=345,

and let X_i denote the full corner angle of original face X at vertex i.
Add 05 and 24 only as uncut auxiliary hinges when using the common rule.
The six original near-stars are star(1)+5c for c in {2,3,4}, and
star(3)+2c for c in {0,1,5}. The seventh candidate is

    T={02,12,25,35,45}.

T's uncut adjacencies are C-A, C-B, C-E, E-D, E-F. Every pair except
A/F and B/D has a common uncut vertex. To settle A/F, compare with the
shortest-path star at vertex 2, cutting 20,21,25 and the straight original
face diagonals 23 in B and 24 in D. The four split quadrilateral triangles
are leaves. Removing them leaves the chain A-C-E-F, with exactly T's
uncut hinges. Thus A/F is safe as well. **Only B/D remains in T.**

View B/D around cap A, with base 01 and copied apex 2, or around cap F,
with base 34 and copied apex 5. Their intervening central angle sums are

    Sigma_A=pi-C_3+E_1, Sigma_F=pi-E_1+C_3,
    Sigma_A+Sigma_F=2*pi.

At least one view has Sigma>=pi. In that view either Case A's apex-cone
criterion or Case B's base-cone criterion suffices. Hence **if both views'
Case A branches are safe, T is safe**. It is enough for a view's Case A
to be impossible. The actual convex quadrilaterals lie in the full apex
cones, and their copied lengths are original edge lengths.

In either view the wider Case A lemma's extra angle-sum premise is automatic:
the two outer angles plus the middle angle equal the source's incident
angle sum. Two simple sufficient ways to settle its Case A are therefore:
a nonobtuse middle angle; or both outer apex angles <=(pi+theta)/2.
A source curvature >=pi gives the original, narrower bounds as well.

### Switch 1: a sharp vertex at 2 or 5

If both curvatures are at least pi, both views' Case A branches are safe,
and T works. Otherwise reflect so kappa_2>=pi and kappa_5<pi. Compare
N=star(1)+25 with T. The cofacial gate applies to N; only C/D's Case A
can remain, with middle E, source 1, K=kappa_3+kappa_4, and
theta_1=pi-E_1+K. If K>=E_1, N is safe. In Case A it is also safe if
E_1<=pi/2 or both C_1,D_1<=(pi+theta_1)/2.

To handle the remaining alternative, define

    f_C=2*C_1+E_1-2*pi-K, f_D=2*D_1+E_1-2*pi-K,
    g_B=2*B_5+F_5-2*pi-K, g_D=2*D_5+F_5-2*pi-K,
    L_Xi=(2*pi-kappa_i)-2*X_i>0.

The positivity of L_Xi is the strict spherical-link bound. The original
face-angle sums give the following identities, with ordinary parentheses
pi-X_i denoting positive corner-angle deficits:

    -f_C = C_0+F_5+(pi-B_3)+(pi-C_1)+(pi-D_4),

    -f_D-g_D = 2*D_2+E_1+F_5+2*(pi-B_3)+2*(pi-C_3),

    -f_D-g_B = L_A0+L_A2+L_B5+kappa_1+2*C_1
               +(pi-B_3)+(pi-C_3)+(pi-D_4)+2*(E_1-pi/2).

These shorter forms preserve the older identities in PRISM_SHARP_FAN_SWITCH.md.
The first gives f_C<0. If N has not passed its tests, E_1>pi/2 and f_D>0.
The other two identities then give g_B,g_D<0. These are exactly the two
wider outer-angle bounds for the upper F view of T whenever it is Case A.
The lower A view's Case A is already safe because kappa_2>=pi. The
two-view observation therefore makes T safe. This completes the switch.

### Switch 2: two curvature gates

Suppose

    kappa_2<=pi, kappa_0+kappa_2>=pi, kappa_0+kappa_1>=pi.

Compare M=star(3)+20 with T. The first two premises are M's cofacial
gate. Its residual pair is B/E, with middle F and apex angle F_3. If
it is Case B, or Case A with F_3<=pi/2, M is safe. Otherwise F_3>pi/2,
so the triangle angle sum gives F_5<pi/2. The upper F view of T has a
safe Case A by its nonobtuse middle. The lower A view cannot be Case A,
since kappa_0+kappa_1>=pi>A_2. Again the two-view observation makes T safe.
Reflection exchanges 0 with 4, 1 with 3, and 2 with 5; it fixes T and
permutes the six near-stars.

### Why one of the seven candidates always works

* **All curvatures<=pi:** one original source 1 or 3 has an allowed equator
  maximum. Otherwise the forbidden maximum at source 1 would require
  kappa_0>kappa_4, while that at source 3 would require kappa_4>kappa_0.
  Use the common rule with that allowed maximum. Ties cause no difficulty.
* **2 or 5 sharp:** Switch 1 applies.
* **Both 2,5 below pi, and 0 or 4 sharp:** Switch 2 or its reflection applies.
* **Only 1 or 3 can be sharp:** reflect to take 1. If an original endpoint
  c in {2,3,4} passes 2*kappa_c+kappa_5>=pi, use star(1)+5c. Otherwise
  the failures for 3 and 4 give kappa_3+kappa_4+kappa_5<pi. Subtracting
  from 4*pi and using kappa_1<2*pi forces kappa_0+kappa_2>pi. Also
  kappa_0+kappa_1>pi, so Switch 2 applies with the already-low fan at 2.

These cases exhaust every curvature assignment. Every final tree is one
of the seven original-edge candidates; neither auxiliary diagonal is cut.
Thus the prism-with-diagonal type, and with it every case through six
vertices, has the stated written existence argument.

## Equalities, preservation, and review status

All comparison equalities enter proved closed cases: source or fan curvature
pi, the slit threshold, a middle Case A/B boundary, a right middle angle,
and an outer wider-angle threshold. Only failed closed tests are added as
strict inequalities. Positive curvature at genuine vertices supplies the
strictness used elsewhere. No perturbation of a flat face lattice, unique
maximum, or uniform positive clearance is assumed.

The stronger every-slit Lemma F and original Triple Lemma are not premises
of this existence proof. Their statements and unresolved work remain in
the old notes, alongside failed rules, examples, certificates and figures.
Nothing has been discarded to obtain this shorter exposition.

This manuscript is a reconstructed research proof under self-audit.
Independent mathematical review and formal verification remain outstanding.
The accompanying exact algebra and finite-graph checks do not formally
verify the geometric arguments, and metric samples do not prove them.
