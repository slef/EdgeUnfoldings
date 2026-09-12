**Historical discovery note.** The family theorem and its unequal-height
extension are now proved in BIPYRAMID_ALIGNED.md. That page also proves a
fixed-tree insertion from a genuine pyramid and records a separate exact
21-coordinate neighborhood outside alignment. Preserve this early note
as history; its pending-work language is superseded.

# Mirror-symmetric bipyramids: new full-family proof under final audit

Research checkpoint around 18:40 UTC, 13 September Tokyo. This is n7-only.
Proposed theorem actually appears proved by the following elementary comparison.
Any convex bipyramid symmetric across its equator plane, ANY ring size m>=3:
choose either fan pole p, source its mirror q, slit at a ring vertex maximizing
|p u|. The star(q)+p u net is safe. In particular the SAME slit/tree works
throughout the symmetric height morph h>0, from a doubled convex polygon.

Key data: corresponding fan and petal triangles congruent, so petals are
reflections of fan triangles across their equator edges. At each uncut
equator vertex, the fan boundary angle equals half its full surface angle,
pi-kappa_u/2 < pi. Opened fan is simple and radially star-shaped, total
angle Gamma=2pi-kappa_p<2pi. Every fan triangular apex angle<pi.
At the chosen maximum-radius vertex, BOTH incident fan base angles are
strictly acute: cos angle=(r_max^2+edge^2-r_neighbor^2)/(2r_max edge)>0.

If kappa_p<pi, the missing gap has width kappa_p<pi. Add the triangle
p,u_start,u_end inside that gap. It is disjoint from the fan interior.
The union B has no vertex at p (angles sum2pi); other ring corners<pi.
Each new endpoint boundary angle = original acute fan base angle +
(pi-kappa_p)/2 < pi. Thus B is a strictly convex polygon, with p interior.

If kappa_p>=pi, Gamma<=pi and the fan polygon itself is convex (all other
corners<pi, p corner<=pi). Call it B; p is now on its boundary. No triangle
completion needed. This branch actually works for ANY slit.

Reflection lemma: for any convex planar polygon B and any point p in B,
the polygon and the reflected triangles reflect_edge(conv(p,a,b)), one
for each boundary edge a b, have pairwise disjoint interiors. Prove by
considering ordinary convex pyramids with base B and apex(p,epsilon),
epsilon>0. Apex is universal; edge-star unfolding leaves base B fixed
and every triangular lateral face attached along its base edge. This is
a published shortest-path star, safe for everyepsilon. As epsilon->0,
the attachments converge to the reflected triangles. Positive-area
interior overlap in a limit would persist for positiveepsilon, impossible.
If p is on boundary some limit triangles degenerate; ignore those, all
actual equator triangles are nondegenerate. A flat boundary vertex p at
Gamma=pi may be omitted from polygon vertex list; the associated extra
side triangles disappear in limit. No need to claim doubled polygons
were explicitly covered in the published theorem.

Apply reflection lemma to B. Original fan + all actual reflected petals
are a SUBSET of its safe arrangement. In low-curvature case omit the
added gap triangle and its reflection. In high-curvature case omit the
reflections of the two slit-side edges (degenerate because they containp).
Hence whole original-edge net safe in both regimes, includingkappa=pi.

For symmetric height morph p=(c,h),q=(c,-h), c inside fixed convex base:
|p ui|^2=|c-ui|^2+h^2. Maximum-radius ui therefore independentofh.
The same cut tree works for allh>0; equalitydistance tiesarbitrary.
At h=0 the limiting arrangement also has disjoint faceinteriors bysame
reflection lemma on originalbasepolygon; polesarenotgenuinevertices.
This is a real global deformation proof for a defined family, NOT for
arbitrary bipyramids or an arbitraryminimum-curvature vertex.

Concrete exact veryflat four-inward example (all10trees individually
check_net certified already, but theoremclaimsmaxradiusnotalltrees):
u0=(-1504,-547,0),u1=(100,0,0),u2=(129,153,0),u3=(-69,394,0),
u4=(-693,400,0),p=(0,0,1),q=(0,0,-1).
Pattern CBBBB; bothpolecurvatures~0.00992degrees; uniqueconvexshortestQ0
hasbothringcornersacute. Thus it isoutsidebothlargepoleandobtuseshortest
gates. Choosemaxradiusu0. Example provesfourbadbothlowisarealremaining
region, andnewmirrorfamilytheoremcovers thisexample andallheights.

Need writepolishedproof, exactcerts(symmetry/maxradius/all45pairs at
severalheights), suitablefigure andn7overview/updatecounts withseparate
familycondition. Nochangesn6orLean. Alsoarchive/commitpreviousnewstarproofs.

## Strengthening immediately found: unequal heights on the same perpendicular line

Mirror symmetry is unnecessary! Let original planar convex base have point c
strictly inside, poles p=(c,h),q=(c,-H), H>=h>0. Choose LOWER pole p asfan.
For everyringvertex |q ui|^2-|p ui|^2=C=H^2-h^2>=0, constant.
Fan boundary convexity holds by comparing cap p to itsown reflected cap,
which isaconvex symmetricbipyramid. SameBcompletionworks unchanged.
Build AUXILIARY PYRAMID withplanarbase B andapex(P,sqrt(C)),wherePisthe
fan'splanarcenter. Its lateraltriangle on eachoriginalequator edge has
apex-edge lengths sqrt(|P Ui|^2+C)=|q ui|. Thus itdevelops EXACTLY toour
originalpetal, notmerelyacontainingtriangle. The safeedge-star unfolding
ofthisauxpyramidcontainsourentirenet as asubset. C=0 isthelimit argument
alreadygiven. IfPisonboundary/highgap, apexoverboundaryisstillavalid
convexpyramid; degenerateextraedgesatC0 maybediscarded.

Therefore ALL verticallyalignedpolesoveroneinteriorpoint ofANYconvex
planarbase haveedgeunfoldingby: lower-heightpolefan, higher-heightpole
source, farthestringvertexslit. No assumption ofregularbase/equalheights.
Thisiswrittenfamilytheorem, notwholecombinatorialbipyramidcase.
Forp(t)=(c,t*h),q(t)=(c,-t*H), t>0, sourcesideandmaxradiusunchanged;
SAME tree works forallt. Directlyanswersuser'smorphidea fordefinedfamily.
Needname BIPYRAMID_ALIGNED.md ratherthanonlySYMMETRIC andexactexamples
withCpositiveandzero pluslow/highfanregimes.
