# New radial receiver lemmas — PRIORITY audit and install, around20:05UTC

Deadline22:04UTC. CompletedchainwholeclassHEAD32ddfe0, current4/15. NewradialproofbelowshouldcloseFCFCC(canonicalBCBCC) andFCCCB(canonicalBFCCC), raisingto6/15afteraudit. Nothingnewinstalledyet. n7only; noagents,nopush.

## Existinglongreceiverpocket

LongfanF, badsourcecopyP, sharedreflexa, receiversourceM, farreceiverb.
T=conv(a,F,P), Mstrictinterior, |aM|=|aP|=s. ConvexreceiverF,a,M,b.
0<kappa_a<pi; M isP rotatedtowardF bykappa. r=|aF|>s.
Otherpoleextensionell_other>(pi-kappa)/2; receiverfanacute,sourceobtuse.

## NEW LEMMA R1: farreceiver distance sum < distanceF tosegmentaP

Normalizea=(0,0),P=(1,0),F=(x,h),h>0,r=|F|>1. MunitcircleinsideT.
Let B=ray aM intersectsegmentFP. Convexity putsb inconv(F,M,B).
B liesoutsideunitcircle, beyondM. LetE beunitcircleexit onsegmentP→F:
ifx>=1,E=P andFE=D=|FP|;
ifx<1, FE=(r²-1)/D (circlepower), withEstrictbetweenP,F.
B liesinsegmentEF. Drec=FM<FE sinceM circlearc fromE towardray aF,
anddistancefromF strictlydecreases alongthat arc.
For b, f(z)=|Fz|+|Mz| convex. AtF,M: f=Drec.
AtB: f(B)=FB+BM=FB+|B|-1. Thislastfunctiong isconvex onEF, endpoint
valuesg(E)=FE,g(F)=r-1. Thereforedb<=max(FE,r-1),withstrictwhenneeded.

Letdelta=distance(F,segmentaP).
- x<=0:delta=r,FE=(r²-1)/D<r sinceD>r, andr-1<r.
- 0<x<1:delta=h, r-1<h; FE<h because
  (r²-1)²-h²D²=(1-x)[(1-x)(1+x)²-h²(x+3)]<0,
  usingh²>1-x²(r>1).
- x>=1:delta=D=FE, r-1<D; BstrictbetweenEandF andMstrictinsideT,
  so f(b)<D. x=1included; x=0firstcase.
Hence STRICT db<delta. Also delta<=min(r,D)<da=r+s.

Badpetal portion OUTSIDE its own fanwedge is behindsegmentaP asviewedfromF;
anyraytoit firstcrossessegmentaP, soitsradius>=delta. DoNOTsaywholebadpetal
outsidecircle: withinownfanwedge itcancloser, butotherpatcheswontenterthatwedge
inapplications. Thisisradialshielding.

## NEW LEMMA R2: receiver atOTHERfan isinside badcone UNION disk radiusdb

Switchfan. Inframea0,P=(s,0), originalF=r angle delta0, M=s anglekappa.
Rotate receiver clockwisebykappa abouta toalignMwithP. Newsourcecopy
F'=r angle d, d=delta0-kappa>0. Fan nowP. Badcone extendsfromPa torayPF.
F' andb' arebeyondthatcone ray; b' fartherangularly thanF' byconvexity.
RayPF meetssegmentaF' atY=tF', anduncoveredreceiverpart isconv(P,b',F',Y).
NeedPY<PF'; thenallverticesradius<=db (PF'<db bytriangleineq, Pb'<db).

SetR=r/s>1,delta0=d+kappa. MinsideT gives
 R(sin(delta0)-sin d)>sin kappa.
ThisalsoimpliesRcosd>1 (sourceangleobtuse).
 t=sin(delta0)/(R sin kappa+sin d), 0<t<1.
To showPY<PF', enough t>2cosd/R-1. Multiplypositivedenom:
 N=R sin(delta0)-(2cosd-R)(R sin kappa+sin d)
 > [R²-2Rcosd+1]sin kappa+2(R-cosd)sin d >0.
ThusPY²-PF'²=(t-1)r²(t+1-2cosd/R)<0.
Circle-clippedreceiveroutsidebadconeliesinsideclosed diskdb, in factstrict.
Needcheckthiswithexactfourcurrentlongexamplesatbothfanplacements.

## Half-fan dependency VERIFIED read-onlyn6/TIDY_CORE.md lines44-81
Ifsourcecurv>=pi ORfan<=pi, everyfullpatchspan<Gammafan/2. Proofusesclosed
sphericallink, no4ringassumption. Thereforewhenbothpoles<pi, validbothfans.
ForinwardQ0F andlastQ4B,conespointtowardeachotherthroughfanbuttheirwhole
spanssum<Gamma, sotheyaredisjointwithslit0; neitherextendsacrossslit.
AlsoQ0F vsQ4C slitadjacent safe bysamehalf-fan(sumfullbadspan+faceangle<Gamma).
Largepolecasesalreadyprovedbyshortestpatchtheorem.

## WHOLE FCFCC / BCBCC proof (two same-direction badpatches, separated)

Bothreceiveridentitieseachensurebadextensionstrictshortatonepole.
Ifsomepolebothshort, standardrule safe. Ifsamepolebothlong, otherbothshort.
Onlyopposingpreferencesremain. Choosefanp whereQ0long; qwhereQ2long.
Q2 isshortatp. Frombadcornerdistance+R1:
 d0>d1>d2>d3>d4. HereQ0Fshareda1,farb2;Q2Fshareda3,farb4.
Slitu0. Q0forwardextensionoutside diskdelta0>d2.
AllverticesofQ2 andQ3 havefanradius<d2: ringr2,r3,r4<=respective d,
sourcecopiesDi<min(endpointd's). SoQ0cannotmeetQ2,Q3.
Q0vsQ4 safehalf-fan (noacrossslit extension);Q0Q1safeuncutvertex.
Q2shortonlymeetsQ3, safeadjacent; allotherCwedgesdisjoint.
Wholeclassproved, no needrealizableopposingexample.

## WHOLE FCCCB / BFCCC proof (two badpatches withthreeCreceiversbetween)

Againonlyopposingpreferencesremain:Q0longatp,Q4longatq; Q4shortatp.
R1givesd0>d1>d2 andd0>d4>d3.
Choosefanpifd2>=d3; otherwisefanqandreflect(i→-i) toexchangeroles.
Slitu0. Q0forwardextensionoutside diskdelta0>d2.
Q2 C entirelyinside diskmax(d2,d3)=d2 =>safeQ0Q2.
ByR2fromlongqQ4, Q3 atfanp liesinside badQ4cone UNION diskd3.
BadQ0 andQ4conesdisjointbyhalf-fan; diskd3<=d2<delta0.
ThusQ0Q3safe. Q0Q1adjacent safe. Q4onlyitsadjacentQ3 (short);
Q0Q4conesdisjoint. AllothersC. Thiscloseswholeclass.

Thuscount6/15 ifallgeometryaudits. Remaining2badclassBBCCC;5threebad;3fourbad.
PotentialR1,R2 canhelprunofadjacentbadpatchesnext, butdontclaimyet.

## Finite searchrecords (NOTproofs)
/private/tmp/n7_opposing_other_search.py/json (moduleunfortunatelyrunsmainonimport)
/private/tmp/n7_opposing_many_rings.py/json:50planarrings, oppositepreferences
forFCFCC/FCCCB notfound; approachdegeneracy. Bothmayactuallyimpossiblebut
ourconditionalargumentscoverregardless. No activeprocess,toolsession86841done.
LPnecessaryanglearraysfeasibleforallthreepatterns, notspatialrealizations.
/private/tmp/n7_two_receiver_lp.py/json.
No universalclaimbasedonnumerics.
