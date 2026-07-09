# Identifiability of Attention-Only Transformers with k Heads per Layer

> **Identifiability of deep causal attention-only transformers with skip connections and k heads per layer**
>
> Nathan W. Henry, Center for Human-Compatible AI, UC Berkeley, `nathan.henry@berkeley.edu`

[![Build Lean formalization](https://github.com/nathanwhenry1/transformer_identifiability/actions/workflows/build-lean.yml/badge.svg)](https://github.com/nathanwhenry1/transformer_identifiability/actions/workflows/build-lean.yml)
[![Lean 4.30.0](https://img.shields.io/badge/Lean-4.30.0-blue)](lean-toolchain)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

This repository contains a complete Lean 4 formalization of an identifiability theorem
for attention-only transformers with `k` attention heads per layer: for a generic such
network, the merged QK and OV matrices of every head in every layer are determined by
the function the network computes — exactly, up to the unavoidable symmetry of
relabelling the `k` heads within each layer.

It extends the single-head formalization in
[`attention_only_transformer_identifiability`](https://github.com/nathanwhenry1/attention_only_transformer_identifiability),
which is included here in full: the `k`-head development builds on the single-head
foundations, and the single-head theorem (`identifiability`) remains available alongside
the `k`-head theorem (`identifiability_perm`).

## Result

Consider an `L`-layer attention-only transformer with causal masking, `k` attention
heads per layer, and additive skip connections, with layer `ℓ` acting by

```
X ↦ X + ∑_{h=1}^{k} V_{ℓ,h} · X · softmax_causal(Xᵀ · A_{ℓ,h} · X).
```

The head sum is symmetric, so relabelling the heads of any layer leaves the network
unchanged; exact recovery of the parameters is therefore impossible for `k ≥ 2`, and
identifiability up to per-layer head permutations is the strongest possible statement.
The formalization proves both directions:

- **Forward** (`identifiability_perm`): for depth `L ≥ 1`, heads `k ≥ 1`, context
  multiplicity `r ≥ 2` (sequence length `r + 1`), and dimension
  `d ≥ d*(L, k) = max(2, k·L + 1)`, there is a Lebesgue-null set `N` of parameters such
  that every `θ'` outside `N` is identified, among *all* parameters and up to a
  per-layer permutation of its heads, by the input-output map of its network.
- **Converse** (`transformerK_eq_of_permute`): parameters that agree up to per-layer
  head permutations compute the same network on every input.

Together these exhibit the per-layer head permutations as exactly the symmetry group of
the realization map. The dimension threshold is linear in both `L` and `k`; for
`k = 1` it reads `d ≥ L + 1`.

The public Lean declaration is:

```lean
TransformerIdentifiability.identifiability_perm :
  ∀ (L k r d : ℕ), 1 ≤ L → 1 ≤ k → 2 ≤ r → NLayer.KHead.dStar L k ≤ d →
    ∃ N : Set (ParamsK L k d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : ParamsK L k d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ, transformerK θ X = transformerK θ' X) →
        ∃ σ : Fin L → Equiv.Perm (Fin k),
          ∀ (ℓ : Fin L) (h : Fin k), θ ℓ h = θ' ℓ (σ ℓ h)
```

## Start here

- **For the model and the final theorems:** open
  [`AnyLayerIdentifiabilityProof/Identifiability.lean`](AnyLayerIdentifiabilityProof/Identifiability.lean)
  — it holds the trusted model definitions (`causalSoftmax`, `attnLayerK`,
  `transformerK`, and their single-head counterparts) and both public theorems, then
  defers to the proof library under
  [`AnyLayerIdentifiabilityProof/NLayer/KHead/`](AnyLayerIdentifiabilityProof/NLayer/KHead).
- **For the result statement:** read [`problem_statement.md`](problem_statement.md).
- **For verification details:** inspect the GitHub Actions run.

## Proof at a glance

The proof is by induction on depth, in the spirit of Fefferman's "Reconstructing a
neural net from its output" (1994). Complex-analytic continuation in an
inverse-temperature dial exposes the innermost layer through a tier hierarchy of
accumulating singularities; with `k` heads per layer the tiers carry `k` competing
Laurent branches, and a dominance/window-avoidance analysis of the pole arcs matches
the branches head-by-head, identifying the first layer's attention matrices up to a
head permutation. Saturated limits of the attention gates and a structural trichotomy
then recover the value matrices, and a peeling argument relabels the matched heads and
descends to a network of depth `L − 1`. Genericity throughout is maintained by explicit
polynomial nonvanishing certificates, so the exceptional set is a finite union of
proper algebraic subsets — in particular Lebesgue-null.

## Repository contents

```text
.
├── AnyLayerIdentifiabilityProof.lean          # Lean root importing the project
├── AnyLayerIdentifiabilityProof/
│   ├── Identifiability.lean                    # Trusted model defs + public theorems
│   │                                           #   `identifiability` (single-head) and
│   │                                           #   `identifiability_perm` (k-head)
│   ├── IdentifiabilityProof.lean               # Single-head proof bridge → all-depth core
│   └── NLayer/
│       ├── IdentifiabilityMain.lean            # Single-head all-depth assembly
│       ├── Foundations/                         # Polynomial genericity / Zariski foundations  (4 files)
│       ├── Analytic/                            # Toolkit: complex-analytic, stratification, quadric  (8 files)
│       ├── Step1/                               # Single-head attention-matrix identification  (12 files)
│       ├── IDL/                                 # Inductive descent lemma: cascade, trichotomy, matching  (23 files)
│       ├── Step2/                               # Single-head realization, sweep, matching realization  (5 files)
│       ├── Genericity/                          # Certificates, anchors, witnesses, null set  (7 files)
│       └── KHead/                               # The k-head development  (48 files)
│           ├── IdentifiabilityMain.lean         # k-head all-depth assembly (`thm_main_statement_holds`)
│           ├── Core.lean, Permutation.lean, DimensionThreshold.lean, ...  # model, head matching, `d*`
│           ├── Analytic/                        # Laurent normal forms, pole arcs, dominance, window avoidance  (12 files)
│           ├── Step1/                           # Tier cascade: first attention matrices up to head permutation  (9 files)
│           ├── Step2/                           # Dial limits, saturation, trichotomy: value matrices  (7 files)
│           ├── Induction/                       # Peeling, relabelling, depth descent  (5 files)
│           └── Genericity/                      # k-head certificates, polynomial cover, null set  (4 files)
├── scripts/
│   ├── check_no_placeholders.py
│   ├── check_local_imports.py
│   ├── check_axioms.py
│   └── print_axioms.sh
├── problem_statement.md
├── Makefile
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain                              # Lean 4.30.0
├── CITATION.cff
├── NOTICE
└── LICENSE                                     # Apache-2.0 for code and repository text
```

The formalization is roughly 94,000 lines of Lean across 111 files; the k-head
development contributes about 42,000 lines across 48 files on top of the single-head
formalization.

## Build and verify

Install [`elan`](https://github.com/leanprover/elan), then run:

```bash
lake exe cache get
make check
```

The individual commands are:

```bash
make imports   # all project-local imports resolve
make audit     # no active sorry/admit or project assumption declarations
make build     # compile the project
make axioms    # print and check final kernel dependencies
```

The axiom check confirms that `identifiability`, `identifiability_perm`, and
`transformerK_eq_of_permute` depend only on the standard Lean principles `propext`,
`Classical.choice`, and `Quot.sound` (in particular, no `sorryAx`).

Lean and Mathlib are pinned to `v4.30.0` in `lean-toolchain` and `lake-manifest.json`.

## Citation

```bibtex
@misc{henry2026identifiabilitykheads,
  author       = {Nathan W. Henry},
  title        = {Identifiability of deep causal attention-only transformers with skip connections and k heads per layer},
  year         = {2026},
  howpublished = {GitHub repository},
  url          = {https://github.com/nathanwhenry1/transformer_identifiability}
}
```

See [`CITATION.cff`](CITATION.cff) for machine-readable metadata.
