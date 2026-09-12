# Opposing-chain FCCBC: complete proof found around19:25UTC

PRIORITY: audit, write, exact-check, update whole class count from3to4.
No need to finish the old H>=0 route. It remains a useful independentlemma.
Everything stays n7. Overnight deadline22:04UTC, about2h35remain.

Existing setup: FCCBC, badQ0F→C Q1 andbadQ3B→C Q2, outerQ4C.
Choosefanp with ell0p+ell3p<omega1p+omega2p viaidentity sumcurv(a,b,c)>0.
Slitu0. Bothshort=>whole safe. One long (assumeQ0, reflectionQ3).
Knownchainreduction leaves only V0/V2 independent; V0/W2 followsboundary.
Knownlong0 implies sigma+tau>pi, so theta>=pi safebybasecones.
CaseA theta<pi: two copiedcutlengths have s+t<L+T, soatleastoneshort.
Widerseparator works if bothouterapexangles below(pi+theta)/2.

## New universal long-receiver pocket lemma

Notationa=u1,P=badQ0sourcecopy, M=receiverQ1sourcecopy,fanp.
T=conv(a,p,P) is the TRIANGULAR INDENTATION missing from concaveQ0,
not its outerhull. Existingproof shows entireconvexQ1 insideT, Mstrictinside.
At a, |aP|=|aM|, anglePaM=kappa_a. BecauseQ0isreflexata,
0<kappa_a<pi (itsincidentfaceangle sum>pi).
Thus angle(aP,MP) atP is(pi-kappa_a)/2.
SinceMstrictinsideT, angleaPp > (pi-kappa_a)/2.
But angleaPp is EXACTLY the OTHER-POLE extension ell0q.
Hence ell0q > (pi-kappa_a)/2.
Adjacentconvexreceiverangleata = pi-kappa_a-eta0 >0,
whereeta0=ell0p+ell0q. Thus
 ell0p < pi-kappa_a-ell0q <(pi-kappa_a)/2 <pi/2.
Sinceell0p>omega1p, EVERY long receiver has ACUTE FAN apex omega1p<pi/2.
We already proved its SOURCE apexomega1q>pi/2.

Also badsourceapexlambda0 +ell0q = ordinaryoutertriangleangle atP <pi.
So lambda0 <(pi+kappa_a)/2. Since theta>kappa_a,
 lambda0 < (pi+theta)/2 ALWAYS. This disposesofthebadouterwidebound.
These factsaregeometric, notinferredfromLP. LP helpedspot them only.
Straight corneratthe OTHER endpointofreceiverallowed; sharedreflexendpoint
receivercornerstrict<pi, soMstillstrictinsideindentation. Allfaceinteriors
nondegenerate. Equalityshortextensionsallowed byearlierconeproof.

## Finite algorithm completing WHOLE FCCBC / canonicalBCFCC

1 chooseanychaineligiblefanp (strictcombinedextensionmargin>0).
2 ifbothpbadextensionsshort, usep,slit0.
3 assumelongp0. Atotherfanq, Q0extensionisstrictshort: follows
 eta0 <omega1p+omega1q andell0p>omega1p, oracute/obtuselonglemma.
4 ifQ3also shortatq, useq,slit0; bothshort=>whole safe.
5 otherwise Q3islongatq. ItsreceiverisQ2, soNEWlong-fanlemma gives
 omega2q <pi/2. Thisisexactlyrho, the OTHERouterapexofV2 inoriginalpnet.
 Thusrho<pi/2<(pi+theta)/2. Badlambdaalreadyhaswideboundabove.
 If theta<pi, bothouterwidebounds hold=>one short copiedcut=>widerseparator.
 If theta>=pi, large-fan basecones alreadyapply.
 Wholepnet safe. Reflectionhandlesinitiallong3, swappingouterroles.

No polecurvatureorder and NO N6global theorem needed. Onlyelementary
localwiderseparator writtenexplicitly inCHAIN_PAIR.md + existingchain
cone/localsharedvertexarguments. ValidALL convexpentagonalbipyramids
withthissymbolicpattern, inclnonplanarequatorsandallallowedstraightCcorners.
Cannotclaimwholepentagonalbipyramidgraph. Wholepatchclassesbecome4/15,
11remainopen. Bothgenericlargepole andalignedfamilystillusefulelsewhere.

## Pending validation/work

- Fourcurrentexactchainpairexamples plusoldchainsearch shouldverify new
 pocket bound ell_other>(pi-kappa_corner)/2 and acute receiverfan.
- Write selector/replay withbranchesbothshort,switch-bothshort,opposinglong
 CaseA/basecone. Independentlycheck45pairsat selectednet.
- OldBIPYRAMID_CHAIN_PAIR.md remainingtablebecomeshistorical: addstrong
 completedbannerandlinkto new BIPYRAMID_CHAIN_RULE.md/html.
- Add theorem-chain anchor onBIPYRAMID_PATCHES; generatorproveddict
 BCFCC:'Chain', updatecurrentoverviewcounts4/15 (retainhistoryold3/15).
- CurrentgitHEAD960d8a2 allalignedproofscommitted.48Pythontests+3Nodepassed.

Floating outputsnotproofs:
/private/tmp/n7_chain_neighbor_opt.json found source rho>pi/2 possible
(butnotwidefailure), so doNOTclaimallotherreceiversareacuteunconditionally.
/private/tmp/n7_chain_angle_lp*.py/json arelinearrelaxations,notrealizable
shapes. LastLPwithotherqchainfailure+pocketbound hadobjective<=0 andled
tosimplepocketlemmaabove. No needpublishLPasanexactcertificate; algebra
andgeometrynowstandalone. Optimizerfinished(session57775),noactivesearch.
