# StrandsRocq

This repository contains the Coq/Rocq mechanization of strand spaces.
It includes the full mechanization of the strand framework, new general results about strands and three case studies with a number of variants, as detailed in our paper "Strands Rocq: Why is a Security Protocol Correct, Mechanically?".

# Structure of the project

The project is structured as follows:
* `Common` this folder contains the Coq mechanization of the common abstract structures of strand spaces:
    + `Strands.v` is the entry point of the strands formalization, with all the basic definitions;
    + `StrandTactics.v` include the tactics that help in automating the proofs;
    + `Bundles.v` and `BundleRelations.v` include definitions and facts about bundles;
    + `MinimalMPT.v` generalization of concepts ideas from the paper about minimal elements of sets of terms;
    + `RelMinimal.v` small helper library with facts about minimal elements of sets
    + `LogicalFacts.v` subset of `FSetLogicalFacs` module from `FSetDecide.v` in the standard Coq library.
* `Instances` this folder includes the part of the development that concretely instantiates various modules from the `Common`folder:
    + `StrandList.v` instantiates strands as pairs `(nat * list sT)`. The first element serves as a strand identifies, the second represents the actual  trace of the strand.
    + `UTerms.v` and `Penetrator.v` actual instances of Strand's terms and Dolev-Yao intruder, building on top of `StrandsList`;
    + `UTermsTactics.v` and `UTermTacticsTests.v` tactics (and corresponding test suite) for terms on `Universes` described within `StrandsList`;
    + `DefaultInstances.v` is a file with default implementation of the module types as used in the case studies.
* `Examples` includes our case studies:
    + `simple_auth` is the full development of Section III of the paper
    + `nsl` and `ns_original` correspond to the development of Needham-Schroeder and Needham-Schroeder-Lowe protocols;
    + `kmp` is for the key management policies case study.

# Checking the proof

The proof can of course be inspected with your favorite editor.
If you wish to check the proof in batch mode you need `dune` and `coq` (tested and developed on `dune` 3.14 and `coq` 8.17.0) and you can run:
```
$ dune clean
$ dune build
```
in this directory. The process requires about 20 seconds on a machine with an Apple M2 processor.

# The Rosetta stone: paper <-> Coq code

Here we reconstruct the correspondence between the concepts presented in the paper and those mechanized here.
Notice that the mechanization includes a lot of details that are omitted in the paper, hence we encourage the interested reader to inspect the proof with their favorite editor.

## Section III (and other general Strand spaces concepts)
| Paper | Coq code |
|---|---|
| Strand spaces and bundles  | `Common/Strands.v` and `Common/Bundles.v` |
| Terms  | `𝔸` in `Instances/UTerms.v` |
| Subterm relation  | `subterm` in `Instances/UTerms.v` |
| Penetrator  | `penetrator_trace` in `Instances/Penetrator.v` |
| Bound on penetrator power  | `penetrator_bound` in `Instances/Penetrator.v` |
| (Uniquely) originates  | `originates` and `uniquely_originates` in `Common/Strands.v` |
| Proof technique facts | Sec. `BundleMinimal` in `Common/Bundles.v` |

## Section IV

| Paper | Coq code |
|---|---|
|Sec. B, C | `Examples/simple_auth/SimpleAuth.v`|
|Sec. D, Replacing A with B in the ciphertext | `Examples/simple_auth/SimpleAuthWithB.v`|
|Sec. D, A flawed version of the protocol | `Examples/simple_auth/SimpleAuthFlawed.v`|
|Sec. D, Relaxing the term typing | `Examples/simple_auth/SimpleAuthUntyped.v`|
|Sec. E | `Examples/simple_auth/SimpleAuthDual.v` and `Examples/simple_auth/SimpleAuthDualBProtected.v`|
|Sec. F | `Examples/simple_auth/SimpleAuthMaximalEnc*.v` |

## Section V.A: Needham-Schroeder-Lowe Protocol (NSL)

| Paper | Coq code |
|---|---|
| Protocol definitions | `Examples/nsl/NSL_protocol.v`, `Examples/nsl/NSL_initiator.v`, and `Examples/nsl/NSL_responder.v`|
| Responder authentication guarantees (classical and new proof technique) | `Examples/nsl/NSL_auth_responder.v` and `Examples/nsl/NSL_auth_responder_simple.v` |
| Responder secrecy guarantees (classical and new proof technique) | `Examples/nsl/NSL_secrecy_responder.v` and `Examples/nsl/NSL_secrecy_responder_simple.v` |
| Initiator authentication guarantees | `Examples/nsl/NSL_auth_initiator.v` |
| Initiator secrecy guarantees | `Examples/nsl/NSL_secrecy_initiator.v` and `Examples/nsl/NSL_secrecy_initiator_simple.v` |
| Original NS protocol | `Examples/original_ns` |

## Section V.B: Key Management Policies (KMP)

| Paper | Coq code |
|---|---|
| Basic definition | `Examples/kmp/KMP_protocol.v` |
| Typed key management policies | `Examples/kmp/KMP_policies.v` |
| Security properties | `Examples/kmp/KMP_closure.v` and `Examples/kmp/KMP_secrecy.v` |
