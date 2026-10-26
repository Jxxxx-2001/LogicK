# LogicK

A Coq/Rocq formalization of first-order logic with equality, using a Hilbert-style deductive system with named variables. The development proves soundness and Gödel completeness by a Henkin construction, and includes a compactness corollary.

This repository accompanies the paper **Formalization of the Completeness Theorem for First-Order Logic with Equality in Rocq**, by **Xiang Ji, Dakai Guo, and Wensheng Yu**, accepted at **SETTA 2026**.

## Requirements

The development has been checked with **Coq 8.13.2**. This release predates the renaming of Coq to Rocq; the paper uses the current name, Rocq. Compatibility with newer Coq/Rocq releases has not been verified.

Only the Coq standard library is required. No external libraries or plugins are needed. Source comments are primarily in Chinese; this README provides an English guide.

## Build from a clean checkout

Install Coq 8.13.2 and ensure `coqc` is on your `PATH`.

On Windows, from PowerShell:

```powershell
git clone https://github.com/Jxxxx-2001/LogicK.git
cd LogicK
.\compile.ps1
```

On Linux or macOS:

```sh
git clone https://github.com/Jxxxx-2001/LogicK.git
cd LogicK
sh ./compile.sh
```

Both scripts read the dependency order from `_CoqProject`, use a flat load path, and stop at the first compilation error. All 14 development files are compiled, including the compactness extension. Generated Coq files are excluded by `.gitignore`.

To inspect the assumptions of the final completeness theorem, run the following from the repository root.

PowerShell:

```powershell
'Require Import complete_K_System. Print Assumptions Godel_complete_theorem.' | coqtop -quiet -I .
```

Linux or macOS:

```sh
printf '%s\n' 'Require Import complete_K_System.' \
  'Print Assumptions Godel_complete_theorem.' | coqtop -quiet -I .
```

The recorded output is provided in [ASSUMPTIONS.txt](ASSUMPTIONS.txt).

## Paper-to-code guide

The source uses `Γ ├ p` for derivability and `Γ ╞ p` for semantic consequence.

| Paper topic | Coq declaration | Source |
| --- | --- | --- |
| Syntax, substitution, and capture avoidance | `term`, `Formula`, `substitute_f`, `t_x_free` | `formulas_K_System.v` |
| Hilbert axioms and derivability | `Axiom_system`, `Γ ├ p` | `syntax_K_System.v` |
| Tarski semantics | `satisfy_R`, `Γ ╞ p` | `semantic_K_System.v` |
| Countability infrastructure | `Countable`, `Bernstein_Theorem` | `Mappings_ML.v`, `Bernstein_theorem_ML.v` |
| First-order formula countability | `Formula_contable`, `bijection_nat_formula` | `bijection_nat_formula_K.v` |
| MapC: syntactic preservation | `map_C_preserves_deduce` | `complete_K_System_pre.v` |
| MapC: semantic transfer under a left inverse | `map_C_satisfy_fwd`, `map_C_satisfy_bwd` | `complete_K_System_pre.v` |
| Fresh-constant generalization, Lemma 1 | `Lemma_Flexible` | `extension_K_System.v` |
| Henkin extension theorem | `max_consistence_extension` | `extension_K_System.v` |
| Canonical model and truth lemma | `model_sat`, `model_sat_complexity` | `satisfiability_K_System.v` |
| Satisfiability theorem | `satisfiable_theorem` | `satisfiability_K_System.v` |
| Soundness | `soundness_K` | `soundness_K_System.v` |
| Completeness | `complete_K` | `complete_K_System.v` |
| Gödel completeness | `Godel_complete_theorem` | `complete_K_System.v` |
| Additional compactness results | `compactness_K`, `compactness_equiv` | `compactness_K_System.v` |

The central result is:

```coq
Theorem Godel_complete_theorem : forall p Γ, Γ ├ p <-> Γ ╞ p.
```

The compactness file is an additional result in the repository; it is not part of the 13-file completeness development counted in the paper.

## Proof architecture

1. Establish countability of first-order terms and formulas, including their arity-indexed dependent vectors, to obtain a formula enumeration.
2. Reindex constants using MapC. Its syntactic preservation results hold for any constant-index map; semantic recovery assumes a left inverse. The concrete doubling map reserves odd-indexed constants for Henkin witnesses.
3. Extend a consistent formula set to a maximally consistent set with the witness property.
4. Construct a canonical model from terms modulo provable equality. Prove the truth lemma by rank-bounded induction, then assemble satisfiability, soundness, and completeness.

## Trusted base

The development uses classical principles from the Coq standard library. `Print Assumptions Godel_complete_theorem` reports:

- `Classical_Prop.classic`
- `Epsilon.epsilon_statement`
- `FunctionalExtensionality.functional_extensionality_dep`
- `Ensembles.Extensionality_Ensembles`
- `Eqdep.Eq_rect_eq.eq_rect_eq`
- `JMeq.JMeq_eq`

There are no `Admitted`, `admit`, or `Abort` commands in the development sources. Successful compilation checks all proof terms in Coq's kernel; it does not remove the standard-library axioms listed above.

## Scope and design choices

- Binding uses variable names, with explicit capture-avoidance conditions for substitution.
- Equality is a primitive formula constructor, interpreted as identity in the model.
- The signature is fixed rather than parameterized: variables, constants, function symbols, and relation symbols are indexed by natural numbers.
- `arity_F (F a b) = S a` and `arity_R (R a b) = S a`, so function and relation symbols have positive arity. Individual constants are represented separately.
- The completeness result concerns this countably infinite signature. It does not establish the corresponding theorem for arbitrary uncountable languages.

## Source size

The 13 core completeness files contain **4,429 physical lines**, or **3,405 nonblank lines after removing Coq comments**. The additional compactness file contains 99 physical lines, or 76 nonblank lines after removing comments. These counts exclude build scripts and documentation.

| File | Physical lines | Code lines | Purpose |
| --- | ---: | ---: | --- |
| `Base_ML.v` | 37 | 20 | Basic set notation and classical decision principle |
| `Mappings_ML.v` | 188 | 116 | Countability and closure properties |
| `Bernstein_theorem_ML.v` | 119 | 80 | Cantor–Bernstein theorem |
| `formulas_K_System.v` | 337 | 241 | Syntax and substitution |
| `syntax_K_System.v` | 854 | 728 | Axioms, derivability, and syntactic metatheorems |
| `semantic_K_System.v` | 604 | 466 | Semantics and substitution lemmas |
| `consistency_K_System.v` | 106 | 70 | Consistent and maximally consistent sets |
| `bijection_nat_formula_K.v` | 298 | 233 | Rank-based term and formula countability |
| `complete_K_System_pre.v` | 788 | 638 | Parameterized MapC framework |
| `extension_K_System.v` | 392 | 316 | Henkin expansion and extension theorem |
| `satisfiability_K_System.v` | 567 | 407 | Canonical model and truth lemma |
| `soundness_K_System.v` | 68 | 49 | Soundness |
| `complete_K_System.v` | 71 | 41 | Completeness and final equivalence |
| **Core total** | **4,429** | **3,405** | |
| `compactness_K_System.v` | 99 | 76 | Additional compactness results |

## Citation and contact

The paper has been accepted for the SETTA 2026 proceedings. Final proceedings metadata and a DOI will be added when available. Until then, the following identifies the accepted paper without inventing publication details:

```bibtex
@misc{ji2026completeness,
  author = {Ji, Xiang and Guo, Dakai and Yu, Wensheng},
  title = {Formalization of the Completeness Theorem for
           First-Order Logic with Equality in {Rocq}},
  year = {2026},
  note = {Accepted at SETTA 2026},
  url = {https://github.com/Jxxxx-2001/LogicK}
}
```

Corresponding author: Wensheng Yu, `wsyu@bupt.edu.cn`.

Supported by the National Natural Science Foundation (NNSF) of China under Grant 62476028.

## License

The code is distributed under the **GNU Lesser General Public License, version 3**, as stated in the source headers. See [LICENSE](LICENSE) for LGPLv3 and [COPYING](COPYING) for the GPLv3 terms it incorporates. Individual source files retain their contributor and copyright notices.
