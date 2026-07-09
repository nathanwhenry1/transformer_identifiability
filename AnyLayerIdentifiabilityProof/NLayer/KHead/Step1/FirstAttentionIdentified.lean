import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.PoleTransfer

/-!
# Capstone: the first attention layer is identified up to head-relabeling

This file packages the headline corollary of **Step 1** (`prop:first-A`, packet K06C)
into two clean, showable statements.  Both are thin wrappers around results already
proved in `Step1/PoleTransfer.lean`:

* `step1FirstAttentionPermutation` — the unique target→source head permutation;
* `step1FirstLayerAttentionIdentificationResult` — the same permutation together with
  its uniqueness and matched value-activity.

Nothing new is proved here analytically; this is a readable presentation layer.
-/

open TransformerIdentifiability.NLayer.KHead

namespace TransformerIdentifiability.NLayer.KHead.Step1

variable {m k d : Nat} {r : Nat} {θ θ' : Params (m + 1) k d}

/-- **First attention layer identified up to head-relabeling symmetry.**
If two `(m+1)`-layer, `k`-head transformers `θ, θ'` satisfy the Step-1 standing
hypotheses (they realize the same input→output map, the target `θ'` is regular, and
`1 < r`), then their first-layer attention matrices coincide up to a UNIQUE
permutation of the `k` heads:  there is a unique `σ : Equiv.Perm (Fin k)` with
`attentionMatrix θ 0 (σ h) = attentionMatrix θ' 0 h` for every head `h`.
This is the headline corollary of Step 1 (`prop:first-A`). -/
theorem firstAttentionLayer_identified_upToPermutation
    (hr : 1 < r) (H : Step1StandingHypotheses r θ θ') :
    ∃! σ : Equiv.Perm (Fin k),
      ∀ h : Fin k, attentionMatrix θ 0 (σ h) = attentionMatrix θ' 0 h :=
  step1FirstAttentionPermutation hr H

/-- **First attention layer identified, with matched value-activity.**
The same unique head permutation `σ` additionally matches ACTIVE heads: every
matched source head `σ h` has nonzero first-layer value matrix
`valueMatrix θ 0 (σ h) ≠ 0`.  So the first attention layer is pinned down exactly
up to relabeling, and no matched head is a spurious zero-value head. -/
theorem firstAttentionLayer_identified
    (hr : 1 < r) (H : Step1StandingHypotheses r θ θ') :
    ∃ σ : Equiv.Perm (Fin k),
      (∀ h, attentionMatrix θ 0 (σ h) = attentionMatrix θ' 0 h) ∧
      (∀ ρ : Equiv.Perm (Fin k),
        (∀ h, attentionMatrix θ 0 (ρ h) = attentionMatrix θ' 0 h) → ρ = σ) ∧
      (∀ h, valueMatrix θ 0 (σ h) ≠ 0) := by
  -- The proved result object carries the permutation, its uniqueness, and matched
  -- unprimed activity, all stated through the `FirstLayerAttentionIdentificationData`
  -- projections and the `FirstLayer…Predicate` defs.  We force each field into its
  -- plain `attentionMatrix`/`activeHeads` form via type-ascribed `have`s.
  let R := step1FirstLayerAttentionIdentificationResult hr H
  refine ⟨R.sigma, ?_, ?_, ?_⟩
  · -- attention equality: defeq to the predicate `∀ h, unprimedAttention (σ h) = …`.
    have heq : ∀ h : Fin k,
        attentionMatrix θ 0 (R.sigma h) = attentionMatrix θ' 0 h := R.attention_eq
    exact heq
  · -- uniqueness of the matching permutation.
    intro ρ hρ
    have hpred : FirstLayerAttentionPermutationPredicate
        (step1FirstLayerAttentionIdentificationData θ θ') ρ := hρ
    exact R.attention_unique ρ hpred
  · -- matched activity, converted from `σ h ∈ activeHeads θ 0` to `V ≠ 0`.
    intro h
    have hact : R.sigma h ∈ activeHeads θ (0 : Fin (m + 1)) := R.matched_active h
    exact (mem_activeHeads_iff_valueMatrix_ne_zero θ 0 (R.sigma h)).mp hact

end TransformerIdentifiability.NLayer.KHead.Step1
