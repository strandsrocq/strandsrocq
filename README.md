# StrandsRocq

This repository contains the Rocq mechanization of strand spaces.
It includes the full mechanization of the strand framework, new general results about strands and three case studies with a number of variants, as detailed in the paper "Strands Rocq: Why is a Security Protocol Correct, Mechanically?" by Matteo Busi, Riccardo Focardi, and Flaminia Luccio ([published version](https://ieeexplore.ieee.org/document/11097857), [arXiv version](https://arxiv.org/abs/2502.12848)).

# Installation and proof checking
> ⚠️ We are currently migrating StrandsRocq to Rocq 9.x, at the moment it is recommended sticking to Coq<=8.20, e.g., by pinning it using ``opam``

> 📣 Now you can run [StrandsRocq directly in your browser]((https://strandsrocq.vercel.app/)), without installing anything!

📄 You can of course inspect StrandsRocq in your editor and check the proofs interactively from there.
You can also check the proofs in batch mode using `dune` and `coq` (tested and developed on `dune` 3.14 and `coq` 8.17.0):
```
$ dune clean
$ dune build
```
in the root of this repository.
The process requires about 20 seconds on a machine with an Apple M2 processor.


# Documentation

- Our [paper](https://arxiv.org/abs/2502.12848) explains the ideas and design principles behind StrandsRocq, and includes some examples;
- For a more hands-on introduction you may also want to consider our [online tutorial](https://strandsrocq.vercel.app/);
- If you are interested in StrandsRocq's internals there's an [AI-generated wiki](https://deepwiki.com/strandsrocq/strandsrocq) (⚠️ May include errors! ⚠️)

# Citing our work

If you plan citing our work, you can use the following bib entry:
```
@inproceedings{strandsrocq,
  author       = {Matteo Busi and
                  Riccardo Focardi and
                  Flaminia L. Luccio},
  title        = {Strands Rocq: Why is a Security Protocol Correct, Mechanically?},
  booktitle    = {38th {IEEE} Computer Security Foundations Symposium, {CSF} 2025, Santa
                  Cruz, CA, USA, June 16-20, 2025},
  pages        = {33--48},
  publisher    = {{IEEE}},
  year         = {2025},
  doi          = {10.1109/CSF64896.2025.00022}
}
```

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
