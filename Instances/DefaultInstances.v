Require Import StrandList.
Require Import StrandsTactics.

Require Import UTerms.
Require Import UTermsTactics.

Require Import MinimalMPT.

Require Import Bundles.

(* Export the basic structures *)
Export UniverseNat.
Export TermNat.
Export StrandList. (* Signature of StrandSpaces *)
Export StrandSpaceList. (* Definitions/Properties over StrandsList *)

(* Plus the modules implementing the tactics for such structures *)
Module Export TermNatTactics := UTermsTactics UniverseNat TermNat.
Module Export StrandListTactics := StrandsTactics UniverseNat TermNat StrandList StrandSpaceList.

(* Bundles *)
Module Export BundleList := Bundle TermNat StrandList StrandSpaceList.
Module Export StrandListMPT := MPT UniverseNat TermNat StrandList StrandSpaceList BundleList.
