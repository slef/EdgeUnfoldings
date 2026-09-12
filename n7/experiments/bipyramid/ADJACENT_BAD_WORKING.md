# Adjacent same-direction two-bad class: COMPLETE PROOF FOUND around20:20UTC

PRIORITY audit/install AFTER finishing radial6/15checkpoint. ThisclosesBBCCC
(normalizedFFCCC), lasttwo-badclass, raises7/15. Worksanyringm>=3 withonlyQ0,Q1F.
No curvatureorder/highpoleassumptions orhalf-fanneeded!

## local tools

Q0Freflexata=u1; Q1Freflexatb=u2. SamefanO, sourcesP0,P1.
H1=conv(O,a,P1) isoutertriangleofbadQ1, bstrictinsideH1.
**Q0 disjoint ENTIRE H1** unconditionally byuncutvertex a:
Q1ataisnonreflex, andouterH1hasEXACTsameangularcornerataastwooriginalQ1faces.
Q0'stwotrianglesplusH1angularsectorareconsecutive total<2pi atuncuta.
No neednesthypothesisforthis. Boundaryequalityfine.

**Clipped convex receiver lemma**: ifbadQ1 pointsintoC Q2, then
Q2∩(fullQ1cone atO) liesinsideH1 (actuallyinsideindentationT1=conv(O,b,P1)).
ReasonQ2convexcontainsO. InoverlapangularsectorbetweenObandOP1, a radial
segmentO→x inQ2 cannotcrossbP1: beyondwouldoverlapbadQ1petal, forbidden
bycommonuncutvertexb. Q2doesnotenterQ1ownfanwedge. Thisworkswhether
Q1extensionisshortorlong. Thislemma VERYUSEFULgeneralization.

**Pocket source bound**: ifMstrictinsideT=conv(a,O,P), |aM|=|aP|, then
|OM|<dist(O,[aP])=delta. ThiswasprovedasintermediatestepinradialShieldlemma:
normalizePunit,F=(x,h), MunitcircleinsideT =>Drec<FE; FE<=delta inx>=1,
FE<deltaotherwise. Requiresno receiverconvexity. Alsoell_bad^O<pi/2 from
circlepocket anglebound andpositiveadjacentcornerata (Q1canbadatotherend).

## selection identity

ell0p+ell0q=rho0, ell1p+ell1q=rho1.
Atu1 sharedcorner f0+e1=2pi-kappa1, whileQ1sum e1+f1+omega1p+omega1q=2pi,
f0=pi+rho0,f1=pi+rho1. So
 rho0-rho1=omega1p+omega1q-kappa1.
DefineA_s=ell0s-omega1s-ell1s. ThenA_p+A_q=-kappa1<0.
AtlastbadQ1→C Q2, B_s=ell1s-omega2s; B_p+B_q<0.

ChoosefanqwhereB_q<=0(lastbadshort), slitu0.
- IfA_q<=0, nested-shortcase, works.
- ElseA_q>0. ThenA_p<0. IfB_p<=0 switchtop,nested-short,works.
- ElseB_p>0: q nonnestedbutlastshort, otherp lastlong. Proveqworksbelow.
Finite2polerule, inequalitiesequalityallowed.

## nested-shortcase
Q0coneendsomega0+ell0 <=omega0+omega1+ell1 (Q1coneend)
<=omega0+omega1+omega2 (endQ2), soQ0canonlyQ1/Q2. Q1shortonlyQ2.
Q0Q1/Q1Q2safeadjacent. AnyQ0Q2intersectionliesinsideQ1cone, henceinsideH1
byclippedreceiverlemma; Q0disjointH1 =>none. OtherpatchesC, noacrossslit
extension (bothF). Thuswhole net.

## nonnested/otherlongcase
Atchosenq: ell0q>omega1q+ell1q. ThusP1strictinsideT0=conv(a,q,P0):
Q1outerconeentirelyinsideQ0extensionsectoratq; commonvertexaangularsector
putsP1betweentheother2T0sides. Equalcopiededges |aP1|=|aP0|.
Pocket sourcebound givesD1=|qP1|<delta0=distance(q,[aP0]).
Pocketangleargument givesell0q<pi/2. Q1notconvexbutitscornerataispositive,
whichisallthatpartofangleproofuses.

Atotherp, Q1islongintoC Q2. Itsreceiver SOURCE angleatq isobtuse,
soomega2q>pi/2. Consequentlyell0q<omega2q andQ0cannotreachQ3orfarther:
omega0+ell0 <omega0+omega1+omega2.

Otherp longQ1 also givesd3<delta1p<=D1 (shieldlemma; distancep tothe
badcutsegment<=distancetoitsqsourcecopy, developedpolelengthD1 isintrinsic
andindependentofthefanchoice). Hence d3<D1<delta0.

Cone-and-disk lemma fromotherp longQ1 saysQ2inchosenqnet liesinQ1cone
UNIONdiskqcenter radiusd3. Insidecone,itliesH1 andcannotmeetQ0.
Outsidethecone,itliesdiskd3<delta0, whereasQ0protrusionradiallyoutside
 delta0. ItsownfanwedgecannotQ2. ThusQ0Q2safe. Q1Q2adjacent,Q0Q1adjacent,
alllaterCwedges, nofarreach/acrossslit. Entireqnetproved.

ThisfinishesallFFCCC /canonicalBBCCC, anyringm>=3withallremainingC.
NeedwriteBIPYRAMID_ADJACENT.md, smallidentityexactchecker, examplesfornested
andnonnested/otherlong ifrealizable. Couldsomebranchimpossible,don'tassume.
Radiallemmascodecurrentlyinstalledandbuildrunning toolsession71343.
Currentwholecountinfiles6, uncommitted; priorHEAD32ddfe0chain4. 50testsatHEAD.
Update7ONLYafterthisauditandproofready. Deadline22:04UTC.
