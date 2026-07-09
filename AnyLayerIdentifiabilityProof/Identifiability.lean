import Mathlib
import AnyLayerIdentifiabilityProof.IdentifiabilityProof
import AnyLayerIdentifiabilityProof.NLayer.KHead.Core
import AnyLayerIdentifiabilityProof.NLayer.KHead.IdentifiabilityMain

set_option autoImplicit false

open MeasureTheory Matrix

namespace TransformerIdentifiability

/-- Column-wise causal softmax: entry `(i, j)` is
`exp (M i j) / ∑_{i' ≤ j} exp (M i' j)` for `i ≤ j`, and `0` otherwise. -/
noncomputable def causalSoftmax {T : ℕ} (M : Matrix (Fin T) (Fin T) ℝ) :
    Matrix (Fin T) (Fin T) ℝ :=
  Matrix.of fun i j =>
    if i ≤ j then Real.exp (M i j) / ∑ i' ∈ Finset.Iic j, Real.exp (M i' j) else 0

/-- One single-head causal attention layer with additive skip connection:
`X ↦ X + V·X·causalSoftmax (Xᵀ·A·X)`  (eq. (1) of the paper; note
`(Xᵀ * A * X) i j = X_{:,i}ᵀ A X_{:,j}`, the paper's score convention). -/
noncomputable def attnLayer {d T : ℕ} (V A : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin T) ℝ) : Matrix (Fin d) (Fin T) ℝ :=
  X + V * X * causalSoftmax (Xᵀ * A * X)

/-- Depth-`L` parameter space: layer `ℓ` carries `(V ℓ, A ℓ)`,
so `Params L d ≅ (ℝ^{d×d})^{2L}`. -/
abbrev Params (L d : ℕ) : Type :=
  Fin L → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ

/-- The network `TF_θ = Layer_{V_L,A_L} ∘ ⋯ ∘ Layer_{V_1,A_1}`, by recursion:
the empty network is the identity, and a depth-`(L+1)` network applies its
first layer `θ 0`, then the depth-`L` network of the remaining layers. -/
noncomputable def transformer {d T : ℕ} :
    {L : ℕ} → Params L d → Matrix (Fin d) (Fin T) ℝ → Matrix (Fin d) (Fin T) ℝ
  | 0, _, X => X
  | _ + 1, θ, X => transformer (Fin.tail θ) (attnLayer (θ 0).1 (θ 0).2 X)

/-- `Matrix (Fin n) (Fin m) ℝ` is definitionally `Fin n → Fin m → ℝ`; give it
the measure-space structure of that pi type.  Mathlib's `Pi` and `Prod`
instances then make `volume` on `Params L d` the product Lebesgue measure,
i.e. Lebesgue measure on `ℝ^(2·L·d²)`. -/
noncomputable instance {n m : ℕ} : MeasureSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasureSpace (Fin n → Fin m → ℝ))

/-! ## Proof-module bridge — not part of the trusted model definition -/

@[simp] theorem causalSoftmax_eq_nlayer {T : ℕ}
    (M : Matrix (Fin T) (Fin T) ℝ) :
    causalSoftmax M = NLayer.causalSoftmax M := by
  rfl

@[simp] theorem attnLayer_eq_nlayer {d T : ℕ}
    (V A : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin T) ℝ) :
    attnLayer V A X = NLayer.attnLayer V A X := by
  rfl

@[simp] theorem transformer_eq_nlayer {d T : ℕ} :
    ∀ {L : ℕ} (θ : Params L d) (X : Matrix (Fin d) (Fin T) ℝ),
      transformer θ X = NLayer.transformer θ X
  | 0, _, _ => rfl
  | L + 1, θ, X => by
      simp [transformer, NLayer.transformer, transformer_eq_nlayer (Fin.tail θ)]

/-! ## Public theorem -/

/-- **Main theorem** (Theorem 3.4 of the paper, null-set form).
For depth `L ≥ 1`, context multiplicity `r ≥ 2` (sequence length `r + 1`) and
dimension `d ≥ max 2 (C(L,2) + 2(L-1))`, there is a Lebesgue-null set `N` of
parameters such that every `θ'` outside `N` is identified, among *all*
parameters, by the input-output map of its network. -/

theorem identifiability (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d) :
    ∃ N : Set (Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          transformer θ X = transformer θ' X) →
        θ = θ' := by
  simpa [Params, transformer, attnLayer, causalSoftmax,
    NLayer.transformer, NLayer.attnLayer, NLayer.causalSoftmax] using
    IdentifiabilityProof.identifiability_all_depth L r d hL hr hd₁ hd₂

-- Kernel dependency report for the public theorem.  CI re-elaborates this file and
-- checks that the printed dependencies are limited to the standard Lean principles
-- `propext`, `Classical.choice`, and `Quot.sound` (in particular, no `sorryAx`).
#print axioms identifiability

/-! ## k-head variant: model and identifiability up to per-layer head permutation

With `k` attention heads per layer, the layer map sums the `k` head contributions,
`X ↦ X + ∑_{h} V_{ℓ,h}·X·softmax_causal(Xᵀ·A_{ℓ,h}·X)`.  This sum is symmetric in the
heads, so relabelling the `k` heads of a layer leaves the network unchanged
(`transformerK_eq_of_permute` below).  Hence — unlike the single-head case, where (paper
§1) "because the layers are ordered and there is one head per layer, no permutation
symmetries occur" — the parameters can be recovered only *up to a per-layer head
permutation*.  Both directions are proved in this file: the forward statement
`identifiability_perm` and the converse symmetry `transformerK_eq_of_permute`.

The single-head model above is the `k = 1` case (`attnLayer V A = attnLayerK ![(V, A)]`).
These definitions are kept separate from, and leave untouched, the single-head model and
its complete proof. -/

/-- One `k`-head causal attention layer with additive skip connection:
`X ↦ X + ∑_{h} V_h · X · causalSoftmax (Xᵀ · A_h · X)`, where head `h` carries the
pair `W h = (V_h, A_h)`. -/
noncomputable def attnLayerK {k d T : ℕ}
    (W : Fin k → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin T) ℝ) : Matrix (Fin d) (Fin T) ℝ :=
  X + ∑ h : Fin k, (W h).1 * X * causalSoftmax (Xᵀ * (W h).2 * X)

/-- Depth-`L`, `k`-head parameter space: layer `ℓ` carries `k` head pairs `(V, A)`,
so `ParamsK L k d ≅ ((ℝ^{d×d})²)^{L·k}`. -/
abbrev ParamsK (L k d : ℕ) : Type :=
  Fin L → Fin k → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ

/-- The depth-`L`, `k`-head network, by the same recursion as `transformer`: apply the
first layer's `k`-head `attnLayerK`, then recurse on the remaining layers. -/
noncomputable def transformerK {k d T : ℕ} :
    {L : ℕ} → ParamsK L k d → Matrix (Fin d) (Fin T) ℝ → Matrix (Fin d) (Fin T) ℝ
  | 0, _, X => X
  | _ + 1, θ, X => transformerK (Fin.tail θ) (attnLayerK (θ 0) X)

@[simp] theorem transformerK_zero {k d T : ℕ} (θ : ParamsK 0 k d)
    (X : Matrix (Fin d) (Fin T) ℝ) :
    transformerK θ X = X :=
  rfl

/-! ### Head-permutation symmetry (the converse direction)

A per-layer relabelling of heads is invisible to the input-output map; this is the
obstruction that makes exact identifiability impossible once `k ≥ 2`. -/

/-- Permuting the `k` heads of a single layer leaves the layer map unchanged: the head
sum is symmetric. -/
theorem attnLayerK_permute {k d T : ℕ} (σ : Equiv.Perm (Fin k))
    (W : Fin k → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin T) ℝ) :
    attnLayerK (fun h => W (σ h)) X = attnLayerK W X := by
  simp only [attnLayerK]
  congr 1
  exact Equiv.sum_comp σ fun h => (W h).1 * X * causalSoftmax (Xᵀ * (W h).2 * X)

/-- Relabelling the `k` heads of every layer by per-layer permutations `σ` leaves the
whole network unchanged. -/
theorem transformerK_permute {k d T : ℕ} :
    ∀ {L : ℕ} (σ : Fin L → Equiv.Perm (Fin k)) (θ : ParamsK L k d)
      (X : Matrix (Fin d) (Fin T) ℝ),
      transformerK (fun ℓ h => θ ℓ (σ ℓ h)) X = transformerK θ X
  | 0, _, _, _ => rfl
  | L + 1, σ, θ, X => by
      have hhead : attnLayerK (fun h => (θ 0) (σ 0 h)) X = attnLayerK (θ 0) X :=
        attnLayerK_permute (σ 0) (θ 0) X
      simp only [transformerK]
      rw [hhead]
      exact transformerK_permute (Fin.tail σ) (Fin.tail θ) (attnLayerK (θ 0) X)

/-- **Head-permutation symmetry.**  If `θ` and `θ'` agree up to a per-layer permutation
of heads (`θ ℓ h = θ' ℓ (σ ℓ h)`), then they compute the same network on every input.
This is why identifiability for `k ≥ 2` heads can hold only up to such permutations. -/
theorem transformerK_eq_of_permute {L k d r : ℕ}
    (θ θ' : ParamsK L k d) (σ : Fin L → Equiv.Perm (Fin k))
    (hσ : ∀ (ℓ : Fin L) (h : Fin k), θ ℓ h = θ' ℓ (σ ℓ h))
    (X : Matrix (Fin d) (Fin (r + 1)) ℝ) :
    transformerK θ X = transformerK θ' X := by
  have hθ : θ = fun ℓ h => θ' ℓ (σ ℓ h) := by
    funext ℓ h; exact hσ ℓ h
  rw [hθ]
  exact transformerK_permute σ θ' X

/-! ### k-head model bridge to the `KHead` proof library

The top-level `k`-head model (`ParamsK`, `attnLayerK`, `transformerK`) coincides with the
`KHead` proof-library model (`NLayer.KHead.Params`, `NLayer.KHead.layer`,
`NLayer.KHead.transformer`).  This mirrors the single-head bridge `transformer_eq_nlayer`
above and is what wires the forward `identifiability_perm` target to the `KHead`
development.

`ParamsK L k d` and `NLayer.KHead.Params L k d` are the *same* type — both unfold to
`Fin L → Fin k → (Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)` (with `ℝ = Real`)
— so the two networks are compared at a single type with no transport. -/

/-- The `k`-head parameter space of the model and of the proof library are the *same*
type (definitionally equal `abbrev`s). -/
example {L k d : ℕ} : ParamsK L k d = NLayer.KHead.Params L k d := rfl

/-- One `k`-head layer of the model equals one `k`-head layer of the `KHead` library, by
`rfl`: `valueMatrix θ l a = (θ l a).1`, `attentionMatrix θ l a = (θ l a).2`, and
`softmaxColC = causalSoftmax = NLayer.causalSoftmax` (cf. `causalSoftmax_eq_nlayer`) all
hold definitionally. -/
@[simp] theorem attnLayerK_eq_khead_layer {L k d T : ℕ} (θ : ParamsK L k d) (l : Fin L)
    (X : Matrix (Fin d) (Fin T) ℝ) :
    attnLayerK (θ l) X = NLayer.KHead.layer θ l X :=
  rfl

/-- **k-head model bridge.**  The top-level `transformerK` equals the `KHead` library
`NLayer.KHead.transformer` on every input, by induction on depth `L` (mirrors
`transformer_eq_nlayer`; the per-layer step is `attnLayerK_eq_khead_layer`). -/
@[simp] theorem transformerK_eq_khead {k d T : ℕ} :
    ∀ {L : ℕ} (θ : ParamsK L k d) (X : Matrix (Fin d) (Fin T) ℝ),
      transformerK θ X = NLayer.KHead.transformer θ X
  | 0, _, _ => rfl
  | L + 1, θ, X => by
      simp [transformerK, NLayer.KHead.transformer,
        attnLayerK_eq_khead_layer, transformerK_eq_khead (Fin.tail θ)]

-- The k-head model bridge is a genuine proof (`rfl`/induction), not an assumption; its
-- only axiom dependencies are the standard Lean principles (no `sorryAx`).
#print axioms transformerK_eq_khead

/-! ### Forward identifiability up to head permutation -/

/-- **k-head identifiability up to per-layer head permutation** (main theorem of the
`_k_heads` project).  For depth `L ≥ 1`, `k ≥ 1` heads per layer, context multiplicity
`r ≥ 2` (sequence length `r + 1`), and `d` large enough, there is a Lebesgue-null set
`N` of parameters such that every `θ'` outside `N` is identified — *up to a per-layer
permutation of its heads* — among all parameters by its input-output map: if
`TF_θ(X) = TF_{θ'}(X)` for every input `X`, then `θ ℓ h = θ' ℓ (σ ℓ h)` for some
per-layer permutations `σ ℓ ∈ S_k`.

`transformerK_eq_of_permute` is the matching converse, so the per-layer head permutations
are exactly the symmetry group of the realization map.

The dimension hypothesis is the genuine `k`-head bound
`d ≥ dStar L k = max 2 (k·L + 1)` (`NLayer.KHead.dStar`), which is linear in `L` and in
`k`; for `k = 1` it recovers `d ≥ L + 1`.  The proof routes through the `KHead` proof
library: the exceptional set is the recursive-generic bad set, which is Lebesgue-null under
this bound; outside it the unconditional main theorem
`NLayer.KHead.thm_main_statement_holds` supplies a unique per-layer target-to-source head
permutation `σ`, and inverting it (`(σ ℓ).symm`) yields the source-to-target form stated
here. -/
theorem identifiability_perm (L k r d : ℕ) (hL : 1 ≤ L) (hk : 1 ≤ k) (hr : 2 ≤ r)
    (hd : NLayer.KHead.dStar L k ≤ d) :
    ∃ N : Set (ParamsK L k d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : ParamsK L k d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          transformerK θ X = transformerK θ' X) →
        ∃ σ : Fin L → Equiv.Perm (Fin k),
          ∀ (ℓ : Fin L) (h : Fin k), θ ℓ h = θ' ℓ (σ ℓ h) := by
  refine ⟨NLayer.KHead.mainTheoremExceptionalSet r L k d, ?_, ?_⟩
  · -- The exceptional set is Lebesgue-null under the dimension threshold.
    exact NLayer.KHead.mainTheoremExceptionalSet_null
      (NLayer.KHead.DimensionHypothesis.mk hd)
  · intro θ' hθ' θ hIO
    -- Rewrite the top-level input-output agreement into `KHead` agreement.
    have hagree : NLayer.KHead.TransformerAgreement r θ θ' := by
      intro X
      simpa using hIO X
    -- The unconditional main theorem gives a unique per-layer head permutation.
    have hmain := NLayer.KHead.thm_main_statement_holds L k r d hL hk hr
      (NLayer.KHead.DimensionHypothesis.mk hd)
    obtain ⟨σ, hσ, _⟩ := hmain.identify hθ' hagree
    -- Invert `σ` to the source-to-target orientation stated by the theorem.
    refine ⟨fun ℓ => (σ ℓ).symm, ?_⟩
    intro ℓ h
    -- `HeadPairMatchedBy` matches value and attention at `σ ℓ ((σ ℓ).symm h) = h`.
    have hval := hσ.value ℓ ((σ ℓ).symm h)
    have hatt := hσ.attention ℓ ((σ ℓ).symm h)
    rw [Equiv.apply_symm_apply] at hval hatt
    -- `valueMatrix = ·.1`, `attentionMatrix = ·.2`, so both components agree.
    exact Prod.ext hval hatt

-- Both the forward `identifiability_perm` and the head-permutation converse
-- `transformerK_eq_of_permute` are fully proved and axiom-clean (no `sorryAx`); the printed
-- dependencies must be limited to the standard Lean principles.
#print axioms identifiability_perm
#print axioms transformerK_eq_of_permute

end TransformerIdentifiability
