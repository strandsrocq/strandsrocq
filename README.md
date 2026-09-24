![StrandsRocq](assets/logo.png)

> 📣 **September 2026 Release**: the partial order semantics of the JLAMP paper, unique origination relative to a bundle, and a witness for every guarantee. See the [release notes](https://github.com/strandsrocq/strandsrocq/releases/tag/sep-2026-release).

This repository contains a Rocq mechanization of strand spaces.
It includes the full mechanization of the strand framework, new general results about strands, and case studies with a number of variants.
StrandsRocq originally appeared in:

> ["Strands Rocq: Why is a Security Protocol Correct, Mechanically?"](https://ieeexplore.ieee.org/document/11097857) by Matteo Busi, Riccardo Focardi, and Flaminia Luccio ([arXiv version](https://arxiv.org/abs/2502.12848))

and is extended in:

> "Partial Order Semantics and Operational Semantics for Strand Spaces, via Rocq" by Matteo Busi, Riccardo Focardi, Joshua Guttman, and Flaminia Luccio (to appear in the Journal of Logical and Algebraic Methods in Programming, JLAMP)

with an inductive characterization of bundles, a CPSA-style protocol syntax embedded in Rocq, a structured operational semantics for protocol execution, and correspondence theorems proving that reachable thread pools and bundles carry exactly the same information.

The code that accompanies each paper is tagged: [`csf25`](https://github.com/strandsrocq/strandsrocq/tree/csf25) for the CSF 2025 paper and [`partial-order-semantics`](https://github.com/strandsrocq/strandsrocq/tree/partial-order-semantics) for the JLAMP one, whose artifact is also archived on [Zenodo](https://doi.org/10.5281/zenodo.22299361).
This README describes the current version, and [Changes since the CSF 2025 paper](#changes-since-the-csf-2025-paper) lists where it departs from the first.

# Installation and proof checking

You can download StrandsRocq locally and use your favorite editor to check the proofs interactively.
For a complete build of StrandsRocq, you can simply run:
```
$ dune clean
$ dune build
```
A successful build requires `dune>=3.21` and Rocq 9.1.0.
The process requires about 15 seconds on a machine with an Apple M4 Pro processor.

# Documentation

- Our [CSF 2025 paper](https://arxiv.org/abs/2502.12848) explains the ideas and design principles behind StrandsRocq, and includes some examples;
- The [documentation of the current version](https://strandsrocq.github.io/strandsrocq/) shows the statements and comments of every module, with identifiers linked to their definitions;
- An [online tutorial](https://strandsrocq.vercel.app/) walks through the SimpleAuth protocol of the CSF 2025 paper in the browser, running the code of the `csf25` version.

## Generating the documentation

To generate HTML documentation, run the following script, which builds the project first and also needs `python3`:
```
$ bash scripts/generate-docs.sh
```
The generated pages are written to `docs/coqdoc-noproofs/`. Open `docs/coqdoc-noproofs/index.html` in a browser to browse them. The documentation covers all the modules in `Common/`, `CPSA/`, and `Original/`, rendered without proof bodies and with identifiers linked to their definitions.
Maintainers publish it online with `bash scripts/publish-docs.sh --push`, which commits the pages to the `gh-pages` branch served by GitHub Pages.

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
We will add an entry for the JLAMP paper once it is published.

# Contributing

Thanks for your interest in contributing, you can get started [here](CONTRIBUTING.md).

# Structure of the project

The project is structured as follows:

* `Common/` contains the Rocq mechanization of the common abstract structures of strand spaces:
    + `Strands.v` is the entry point of the strands formalization, with all the basic definitions;
    + `StrandsTacticsFunctor.v` includes the tactics that help in automating the proofs (functor-based);
    + `Universe.v` and `UniverseNat.v` introduce a `UniverseSig` module type for the term universe with a concrete `nat`-indexed instantiation;
    + `Bundles.v` and `BundleRelations.v` include definitions and facts about bundles, using a `bundle_type` record with separate `nodes`, `intra` (strand-succession), and `inter` (communication) edge lists; `Bundles.v` also defines origination relative to a bundle (`originates_at_most_once_in` and `uniquely_originates_in`);
    + `BundleInductive.v` contains the inductive characterization of bundles (`IndBundle`) with five constructors (Empty, Send0, Send, Recv0, Recv), together with soundness (`IndBundle_sound`) and completeness (`IndBundle_complete`) theorems;
    + `Enumerate.v` develops finite enumerations compatible with a causal ordering;
    + `BundleSizeInduction.v` provides bundle-size and sink-removal induction principles;
    + `DefaultInstanceFunctor.v` and `EmbeddedTraceStrandsFunctor.v` are functors that assemble tactics, bundle definitions, and MPT into concrete instances;
    + `SanityTactics.v` contains the tactics that build witness bundles: well-formedness through `IndBundle`, membership in a role and in a strand space, origination, and uniqueness of strands;
    + `MinimalMPT.v` generalizes concepts from the paper about minimal elements of sets of terms;
    + `RelMinimal.v` is a small helper library with facts about minimal elements of sets;
    + `LogicalFacts.v` is a subset of `FSetLogicalFacts` from `FSetDecide.v` in the standard Rocq library.

* `CPSA/` contains the CPSA-style protocol syntax and operational semantics (new in the JLAMP paper):
    + `RoleSyntax.v` defines an intrinsically sorted term language for CPSA messages (sorts: Name, Text, Data, Tag, Skey, Akey, Mesg) and role/protocol records with valuation-based instantiation into the concrete message algebra;
    + `ChoiceRoles.v` implements the desugaring of CPSA `choice` constructs into flat role lists with shared prefixes;
    + `PenetratorProtocol.v` defines the standard Dolev-Yao adversary as a CPSA protocol (atom, pair, sep, enc, dec, hash roles);
    + `Semantics.v` defines the `reachable_pool` operational semantics (`P ⊨ T`) with five rules (Base, SpawnSend, ExtendSend, SpawnRecv, ExtendRecv), and proves `bundle_of_reachable` (soundness) and `reachable_of_wf_bundle` (completeness);
    + `ComputableSemantics.v` refines the `Prop`-level semantics to `Type`, recording indexed communication witnesses to enable computation over derivations and bundle extraction;
    + `LabelledSemantics.v` defines a labeled transition system over thread pools where each label carries the destination node, the event, and the communication source;
    + `EnumerationSemantics.v` proves that every compatible enumeration of a well-formed protocol bundle is realized by a labelled execution;
    + `ProtocolExamples.v` contains worked examples: a simple initiator/responder, choice roles (yes-or-no protocol), and the Concurrent Yahalom protocol;
    + `PaperExamples.v` is a proof index collecting the Rocq developments referenced directly by the JLAMP paper;
    + `examples/` contains the CPSA sources of the yes-or-no, Yahalom, and Concurrent Yahalom protocols, and the CPSA output for yes-or-no;
    + `Instances/` concretely instantiates `UTerms`, `Penetrator`, `UTermsTactics`, and `DefaultInstances` for use in the CPSA development.

* `Original/` contains the development of the CSF 2025 paper, with the changes described in [Changes since the CSF 2025 paper](#changes-since-the-csf-2025-paper):
    + `Instances/` instantiates strands as pairs `(nat, list sT)` and provides `UTerms.v`, `Penetrator.v`, `UTermsTactics.v`, `UTermTacticsTests.v`, and `DefaultInstances.v`;
    + `Examples/` includes the protocol case studies:
        - `simple_auth/` is the full development of Section IV of the CSF 2025 paper;
        - `nsl/` and `ns_original/` cover the Needham-Schroeder-Lowe and original Needham-Schroeder protocols, and `nsl/NSL_sanity.v` holds the NSL witnesses;
        - `kmp/` is the key management policies case study: `KMP_policy_examples.v` and `KMP_policy_examples_improved.v` exhibit policies and their closures, `KMP_runs.v` the witness bundles, and `KMP_sanity.v` and `KMP_sanity_improved.v` what the two closure definitions prove about them.

* `scripts/` contains `generate-docs.sh` and `publish-docs.sh`, described above.

* `docs/coqdoc-assets/` contains the style of the generated documentation.

# The Rosetta stone: paper ↔ Rocq code

Here we reconstruct the correspondence between the concepts presented in the papers and those mechanized here.
The mechanization includes many details omitted from the papers; we encourage the interested reader to inspect the proofs with their favorite editor.

## Strands Rocq (CSF 2025)

The tables refer to the current code; [Changes since the CSF 2025 paper](#changes-since-the-csf-2025-paper) lists where it departs from the paper.

### Section III (and other general strand spaces concepts)
| Paper | Rocq code |
|---|---|
| Strand spaces and bundles | `Common/Strands.v` and `Common/Bundles.v` |
| Terms | `𝔸` in `Original/Instances/UTerms.v` |
| Subterm relation | `subterm` in `Original/Instances/UTerms.v` |
| Penetrator | `penetrator_strand` in `Original/Instances/Penetrator.v` |
| Bound on penetrator power | `penetrator_bound` in `Original/Instances/Penetrator.v` |
| Originates | `originates` in `Common/Strands.v` |
| Uniquely originates | `originates_at_most_once_in` and `uniquely_originates_in` in `Common/Bundles.v` |
| Proof technique facts | Sec. `BundleMinimal` in `Common/Bundles.v` |

### Section IV
| Paper | Rocq code |
|---|---|
| Sec. B, C | `Original/Examples/simple_auth/SimpleAuth.v` |
| Sec. D, Replacing A with B in the ciphertext | `Original/Examples/simple_auth/SimpleAuthWithB.v` |
| Sec. D, A flawed version of the protocol | `Original/Examples/simple_auth/SimpleAuthFlawed.v` |
| Sec. D, Relaxing the term typing | `Original/Examples/simple_auth/SimpleAuthUntyped.v` |
| Sec. E | `Original/Examples/simple_auth/SimpleAuthDual.v` and `Original/Examples/simple_auth/SimpleAuthDualBProtected.v` |
| Sec. F | `Original/Examples/simple_auth/SimpleAuthMaximalEnc*.v` |

### Section V.A: Needham-Schroeder-Lowe Protocol (NSL)
| Paper | Rocq code |
|---|---|
| Protocol definitions | `Original/Examples/nsl/NSL_protocol.v`, `Original/Examples/nsl/NSL_initiator.v`, and `Original/Examples/nsl/NSL_responder.v` |
| Responder authentication guarantees (classical and new proof technique) | `Original/Examples/nsl/NSL_auth_responder.v` and `Original/Examples/nsl/NSL_auth_responder_simple.v` |
| Responder secrecy guarantees (classical and new proof technique) | `Original/Examples/nsl/NSL_secrecy_responder.v` and `Original/Examples/nsl/NSL_secrecy_responder_simple.v` |
| Initiator authentication guarantees | `Original/Examples/nsl/NSL_auth_initiator.v` |
| Initiator secrecy guarantees | `Original/Examples/nsl/NSL_secrecy_initiator.v` and `Original/Examples/nsl/NSL_secrecy_initiator_simple.v` |
| Original NS protocol | `Original/Examples/ns_original` |

### Section V.B: Key Management Policies (KMP)
| Paper | Rocq code |
|---|---|
| Basic definition | `Original/Examples/kmp/KMP_protocol.v` |
| Typed key management policies | `Original/Examples/kmp/KMP_policies.v` |
| Security properties | `Original/Examples/kmp/KMP_closure.v` and `Original/Examples/kmp/KMP_secrecy.v` |

## Partial Order Semantics (JLAMP)

### Section 2: Background
| Paper | Rocq code |
|---|---|
| Examples 1–2 - Yes-or-no and Concurrent Yahalom | `CPSA/PaperExamples.v` |

### Section 3: Formalizing Bundles
| Paper | Rocq code |
|---|---|
| Definition 2 - Bundle | `is_bundle` in `Common/Bundles.v` |
| Figure 2 - Rules generating bundles inductively | `IndBundle` in `Common/BundleInductive.v` |
| Theorem 1 - Soundness of inductive bundles | `IndBundle_sound` in `Common/BundleInductive.v` |
| Theorem 2 - Bundle size induction | `bundle_size_induction` and `bundle_size_induction_cor` in `Common/BundleSizeInduction.v` |
| Lemma 1 - Bundle sink removal | `remove_sink_bundle` and `remove_sink_smaller` in `Common/BundleSizeInduction.v` |
| Corollary 1 - Bundle sink induction | `bundle_sink_induction` and `bundle_sink_induction_alt` in `Common/BundleSizeInduction.v` |
| Theorem 3 - Completeness of inductive bundles | `IndBundle_complete` in `Common/BundleInductive.v` |

### Section 4: Protocols
| Paper | Rocq code |
|---|---|
| Section 4.1 - Roles, parameters, valuations, and trace instantiation | `CPSA/RoleSyntax.v` |
| Section 4.2 - CPSA-style role and protocol declarations | `defrole` in `CPSA/RoleSyntax.v` |
| Figure 4 - A role with choice and the roles it expands to | `paper_yes_no_choice_desugars` in `CPSA/PaperExamples.v` |
| Section 4.3 - Penetrator roles | `CPSA/PenetratorProtocol.v` |

### Section 5: An Operational Semantics
| Paper | Rocq code |
|---|---|
| Section 5.1 - Threads, thread pools, role-prefix compatibility and occurred events | `CPSA/Semantics.v` |
| Figure 5 - Five rules for reachable pools | `reachable_pool` in `CPSA/Semantics.v` |
| Examples 6–7 - Reachability and choice | `CPSA/PaperExamples.v` |
| Section 5.3 - Origination assumptions | `wf_protocol_no_mesg_origination` in `CPSA/RoleSyntax.v` and its semantic consequences in `CPSA/Semantics.v` |

### Section 6: Semantic Correctness
| Paper | Rocq code |
|---|---|
| Section 6.1 - Representation and extension relations | `represents_pool` and `extends_pool_trace` in `CPSA/Semantics.v` |
| Example 8 - Representation of Concurrent Yahalom | `CPSA/PaperExamples.v` |
| Theorem 4 - Soundness of the operational semantics | `bundle_of_reachable` in `CPSA/Semantics.v` |
| Theorem 5 - Completeness of the operational semantics | `reachable_of_wf_bundle` in `CPSA/Semantics.v` |
| Section 6.4 - Combined semantic correspondence | `bundle_of_reachable` and `reachable_of_wf_bundle` in `CPSA/Semantics.v` |

### Section 7: Computational Labeled Semantics
| Paper | Rocq code |
|---|---|
| Section 7.1 - Indexed occurrences and type-level semantics | `CPSA/ComputableSemantics.v` |
| Section 7.2 and Figure 7 - Labelled transition system | `CPSA/LabelledSemantics.v` |
| Section 7.2 - Labelled executions and reachability derivations determine one another | `reachable_poolT_has_labelsT` and `bundle_has_labelled_executionT` in `CPSA/LabelledSemantics.v` |
| Example 9 - Labelled yes-or-no execution | `paper_yes_no_yes_labels` and `paper_yes_no_yes_labelled_execution` in `CPSA/PaperExamples.v` |
| Section 7.3 - Finite enumerations and causal-order compatibility | `enumerates`, `is_compatible`, and `compat_enum` in `Common/Enumerate.v` |
| Section 7.3 - Removing the last scheduled node | `omit_at`, `compat_enum_omit`, and `list_of_enum_omit_last` in `Common/Enumerate.v` |
| Theorem 2 and Corollary 1 - Induction principles used in Section 7.3 | `Common/BundleSizeInduction.v` |
| Section 7.3 - Compatible enumeration of a bundle | `compatible_bundle_enumeration` in `CPSA/EnumerationSemantics.v` |
| Section 7.3 - Final node, sink removal, and execution extension lemmas | `compatible_last_is_sink`, `compatible_remove_last`, and `enumeration_execution_snoc` in `CPSA/EnumerationSemantics.v` |
| Theorem 6 - Realization of compatible enumerations | `compatible_enumeration_has_labelled_execution` in `CPSA/EnumerationSemantics.v` |

### Section 8: Worked Example - Concurrent Yahalom
| Paper | Rocq code |
|---|---|
| Figure 8 - Concurrent Yahalom in CPSA-like syntax | `concurrent_yahalom_protocol` and its three roles in `CPSA/PaperExamples.v` |
| Section 8.1 - Ground run | `paper_concurrent_yahalom_pool_reachable` in `CPSA/PaperExamples.v` |
| Section 8.2 - From an operational history to a bundle | `paper_concurrent_yahalom_soundness_witness`, `paper_concurrent_yahalom_computed_bundle`, and `paper_concurrent_yahalom_computed_bundle_sound` in `CPSA/PaperExamples.v` |
| Section 8.3 - From the bundle back to an operational history | `reachable_of_wf_bundle` in `CPSA/Semantics.v` |

# Changes since the CSF 2025 paper

Every security guarantee in `Original/Examples/` is now paired with witness bundles.
Building them showed that two hypotheses could never hold, so the guarantees that assumed them were vacuously true; fixing them changed a few definitions.

## Unique origination is relative to a bundle

In the CSF version, `uniquely_originates t` asked for a unique node originating `t` among all the nodes of the strand space.
Strands such as `(0, [⊕ t])` and `(1, [⊕ t])` always exist there, so the hypothesis was false for every term.
It is replaced by `originates_at_most_once_in C t` in `Common/Bundles.v`, which only constrains the nodes of the bundle `C`; `uniquely_originates_in C t` adds existence for the statements that need it.
In KMP, freshness is a premise of the key creation role, and `fresh_sound_for` in `Original/Examples/kmp/KMP_protocol.v` states that it agrees with the bundle.

## Key management policies

- The closure asked the reachability relation to be reflexive on every key type, which a finite list cannot be, so no policy had a closure. Reflexivity is now required only on the types that the policy mentions (`policy_types` in `Original/Examples/kmp/KMP_policies.v`), and the key creation role only creates keys of those types. `KMP_policy_examples.v` and `KMP_policy_examples_improved.v` exhibit closures, and a policy on which the two closure definitions differ.
- Encryption and decryption carry a key rather than a text, so that wrap-then-decrypt can be expressed.
- The usage rules no longer assume that the keys they are given are device keys, so that an attacker's key can be injected.

## Witnesses

An honest run is a bundle that satisfies all the hypotheses of a guarantee at once, so the guarantee is not vacuous.
A counterexample shows that a hypothesis is needed, or that a flawed protocol is indeed flawed.
The tactics that build them are in `Common/SanityTactics.v`.

| Case study | Honest runs | Counterexamples |
|---|---|---|
| `simple_auth/` | a `*Sanity` section in every file but `SimpleAuthFlawed.v` | replay in `SimpleAuth.v`; impersonation in `SimpleAuthDual.v` and `SimpleAuthDualBProtected.v`; reflection in `SimpleAuthFlawed.v` and `SimpleAuthMaximalEncComposition.v`; key leak in `SimpleAuthUntyped.v` |
| `ns_original/` | Lowe's attack in `NS_orig_auth_responder_simple.v`, which the NS guarantees account for | |
| `nsl/` | one run for all the guarantees, in `NSL_sanity.v` | nonce collapse in `NSL_sanity.v`, for the responder guarantees without `Na <> Nb` |
| `kmp/` | `KMP_runs.v` | type confusion and key injection in `KMP_runs.v`; `KMP_sanity.v` and `KMP_sanity_improved.v` read the three runs through the two closure definitions |

The witnesses also led to two corrections:
- the injective agreement of `ns_original` was Proposition 4.8 of the original strand spaces paper, with uniqueness on the initiator; it is now stated on the responder, as for NSL, and the original is kept as `injective_agreement_orig`;
- the NSL secrecy corollaries no longer carry a premise that their conclusion already implied.
