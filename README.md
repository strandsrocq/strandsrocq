![StrandsRocq](assets/logo.png)

This artifact accompanies the paper:

> "Partial Order Semantics and Operational Semantics for Strand Spaces, via Rocq" by Matteo Busi, Riccardo Focardi, Joshua Guttman, and Flaminia Luccio

This paper extends the StrandsRocq framework, a full mechanization of the strand framework, with: an inductive characterization of bundles, a CPSA-style protocol syntax embedded in Rocq, a structured operational semantics for protocol execution, and correspondence theorems proving that reachable thread pools and bundles carry exactly the same information.

The original paper covering StrandsRocq is:
> ["Strands Rocq: Why is a Security Protocol Correct, Mechanically?"](https://ieeexplore.ieee.org/document/11097857) by Matteo Busi, Riccardo Focardi, and Flaminia Luccio ([arXiv version](https://arxiv.org/abs/2502.12848))


# Installation and proof checking

You can download our artifact locally and use your favorite editor to check the proofs interactively.
For a complete build, you can simply run:
```
$ dune clean
$ dune build
```
A successful build requires `dune>=3.21` and Rocq 9.1.0.
The process requires about 20 seconds on a machine with an Apple M2 processor.

## Generating documentation for the CPSA modules

To generate HTML documentation for the `CPSA` modules, first build the project, then run:
```
$ bash scripts/generate-cpsa-docs.sh
```
The generated pages are written to `docs/coqdoc-noproofs/`. Open `docs/coqdoc-noproofs/index.html` in a browser to browse them. The documentation covers the enumeration and bundle-induction libraries, the CPSA syntax and semantic modules, the protocol examples, and all `CPSA/Instances/` files, rendered without proof bodies.

# Structure of the project

The project is structured as follows:

* `Common/` contains the Rocq mechanization of the common abstract structures of strand spaces:
    + `Strands.v` is the entry point of the strands formalization, with all the basic definitions;
    + `StrandsTacticsFunctor.v` includes the tactics that help in automating the proofs (functor-based);
    + `Universe.v` and `UniverseNat.v` introduce a `UniverseSig` module type for the term universe with a concrete `nat`-indexed instantiation;
    + `Bundles.v` and `BundleRelations.v` include definitions and facts about bundles, using a `bundle_graph` record with separate `nodes`, `intra` (strand-succession), and `inter` (communication) edge lists;
    + `BundleInductive.v` contains the inductive characterization of bundles (`IndBundle`) with five constructors (Empty, Send0, Send, Recv0, Recv), together with soundness (`IndBundle_sound`) and completeness (`IndBundle_complete`) theorems;
    + `Subbundles.v` contains the subbundle relation and supporting lemmas;
    + `Enumerate.v` develops finite enumerations compatible with a causal ordering;
    + `BundleSizeInduction.v` and `BundleSizeInductionFixed.v` provide bundle-size and sink-removal induction principles;
    + `DefaultInstanceFunctor.v` and `EmbeddedTraceStrandsFunctor.v` are functors that assemble tactics, bundle definitions, and MPT into concrete instances;
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
    + `Instances/` concretely instantiates `UTerms`, `Penetrator`, `UTermsTactics`, and `DefaultInstances` for use in the CPSA development.

* `Original/` contains the original development from the CSF 2025 paper:
    + `Instances/` instantiates strands as pairs `(nat, list sT)` and provides `UTerms.v`, `Penetrator.v`, `UTermsTactics.v`, `UTermTacticsTests.v`, and `DefaultInstances.v`;
    + `Examples/` includes the protocol case studies:
        - `simple_auth/` is the full development of Section IV of the CSF 2025 paper;
        - `nsl/` and `ns_original/` cover the Needham-Schroeder-Lowe and original Needham-Schroeder protocols;
        - `kmp/` is the key management policies case study.

# The Rosetta stone: paper ↔ Rocq code

Here we reconstruct the correspondence between the concepts presented in the paper and those mechanized here.
The mechanization includes many details omitted from the paper; we encourage the interested reader to inspect the proofs with their favorite editor.

### Section 3: Formalizing Bundles
| Paper | Rocq code |
|---|---|
| Definition 2 - Bundle | `is_bundle` in `Common/Bundles.v` |
| Figure 2 - Rules generating bundles inductively | `IndBundle` in `Common/BundleInductive.v` |
| Theorem 1 - Soundness of inductive bundles | `IndBundle_sound` in `Common/BundleInductive.v` |
| Theorem 2 - Bundle size induction | `bundle_size_induction` and `bundle_size_induction_cor` in `Common/BundleSizeInduction.v` |
| Corollary 1 - Bundle sink induction | `bundle_sink_induction` and `bundle_sink_induction_alt` in `Common/BundleSizeInduction.v` and `Common/BundleSizeInductionFixed.v` |
| Theorem 3 - Completeness of inductive bundles | `IndBundle_complete` in `Common/BundleInductive.v` |

### Section 4: Protocols
| Paper | Rocq code |
|---|---|
| Section 4.1 - Roles, parameters, valuations, and trace instantiation | `CPSA/RoleSyntax.v` |
| Section 4.2 - CPSA-style role and protocol declarations | `defrole` and `defprotocol` in `CPSA/RoleSyntax.v` |
| Section 4.3 - Penetrator roles | `CPSA/PenetratorProtocol.v` |
| Examples 1–2 - Yes-or-no and Concurrent Yahalom | `CPSA/PaperExamples.v` |

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
| Example 9 - Labelled yes-or-no execution | `paper_yes_no_yes_labels` and `paper_yes_no_yes_labelled_execution` in `CPSA/PaperExamples.v` |
| Section 7.3 - Finite enumerations and causal-order compatibility | `enumerates`, `is_compatible`, and `compat_enum` in `Common/Enumerate.v` |
| Section 7.3 - Removing the last scheduled node | `omit_at`, `compat_enum_omit`, and `list_of_enum_omit_last` in `Common/Enumerate.v` |
| Theorem 2 and Corollary 1 - Induction principles used in Section 7.3 | `Common/BundleSizeInduction.v` and `Common/BundleSizeInductionFixed.v` |
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
