Require Import Strands.
Require Import Bundles.
Require Import BundleInductive.
Require Import MinimalMPT.
Require Import StrandsTacticsFunctor.
Require Import Universe.

Module MakeDefaultInstance
  (Import U : UniverseSig)
  (Import T : TermSig)
  (Import St : StrandSig T)
  (Import SSp : StrandSpaceSig T St)
  (Import TT : TermTacticsSig).

  Export U.
  Export T.
  Export St.
  Export SSp.

  Module Export StrandTactics := MakeStrandsTactics T St SSp TT.
  Module Export BundleInstance := Bundle T St SSp.
  Module Export BundleInductiveInstance := BundleInductive T St SSp BundleInstance.
  Module Export MPTInstance := MPT T St SSp BundleInstance.
End MakeDefaultInstance.
