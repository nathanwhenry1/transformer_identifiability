import AnyLayerIdentifiabilityProof.NLayer.KHead.Core

/-!
# Matrix-level fiber for the k-head model

This file is the Lean statement/API scaffold for
`tex_modular/sections/09-matrix-fiber.tex`.  It does not assert the full
generic identifiability theorem.  Instead, it packages the exact fiber/orbit
corollary as a `Prop` interface and proves the easy formal steps:

* layerwise head relabeling preserves the realization map;
* a target-to-source paired matrix matching puts a parameter in the inverse
  layerwise permutation orbit;
* pairwise distinct target attentions imply freeness of the layerwise action.
-/

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

noncomputable section

/-- A tuple of one head permutation for each layer. -/
abbrev LayerPermutations (L k : Nat) : Type :=
  Fin L → Equiv.Perm (Fin k)

namespace LayerPermutations

/-- Tail of a layerwise permutation tuple after deleting the first layer. -/
def tail {L k : Nat} (π : LayerPermutations (L + 1) k) :
    LayerPermutations L k :=
  fun l => π l.succ

@[simp] theorem tail_apply {L k : Nat}
    (π : LayerPermutations (L + 1) k) (l : Fin L) :
    tail π l = π l.succ :=
  rfl

/-- Layerwise inverse permutations, converting target-to-source matches to orbit actions. -/
def inv {L k : Nat} (π : LayerPermutations L k) :
    LayerPermutations L k :=
  fun l => (π l).symm

@[simp] theorem inv_apply {L k : Nat} (π : LayerPermutations L k)
    (l : Fin L) :
    inv π l = (π l).symm :=
  rfl

end LayerPermutations

/-- Apply one head permutation in each layer.  The convention is
`(π • θ)_{l,a} = θ_{l,π_l(a)}`. -/
def layerwisePermute {L k d : Nat} (π : LayerPermutations L k)
    (θ : Params L k d) : Params L k d :=
  fun l a => θ l (π l a)

@[simp] theorem valueMatrix_layerwisePermute {L k d : Nat}
    (π : LayerPermutations L k) (θ : Params L k d)
    (l : Fin L) (a : Fin k) :
    valueMatrix (layerwisePermute π θ) l a =
      valueMatrix θ l (π l a) :=
  rfl

@[simp] theorem attentionMatrix_layerwisePermute {L k d : Nat}
    (π : LayerPermutations L k) (θ : Params L k d)
    (l : Fin L) (a : Fin k) :
    attentionMatrix (layerwisePermute π θ) l a =
      attentionMatrix θ l (π l a) :=
  rfl

@[simp] theorem tail_layerwisePermute {L k d : Nat}
    (π : LayerPermutations (L + 1) k) (θ : Params (L + 1) k d) :
    Fin.tail (layerwisePermute π θ) =
      layerwisePermute (LayerPermutations.tail π) (Fin.tail θ) :=
  rfl

/-- A finite head-sum is unchanged by relabeling the heads in one layer. -/
theorem layer_layerwisePermute {L k d T : Nat}
    (π : LayerPermutations L k) (θ : Params L k d) (l : Fin L)
    (X : Matrix (Fin d) (Fin T) ℝ) :
    layer (layerwisePermute π θ) l X = layer θ l X := by
  classical
  have hsum := Equiv.sum_comp (π l)
    (fun a : Fin k =>
      valueMatrix θ l a * X * softmaxColC (Xᵀ * attentionMatrix θ l a * X))
  simp [layer, layerwisePermute] at hsum ⊢
  exact hsum

/-- Layerwise head relabeling preserves the full realization map. -/
theorem transformer_layerwisePermute {L k d T : Nat} :
    ∀ (π : LayerPermutations L k) (θ : Params L k d)
      (X : Matrix (Fin d) (Fin T) ℝ),
      transformer (T := T) (layerwisePermute π θ) X =
        transformer (T := T) θ X := by
  induction L with
  | zero =>
      intro _π _θ _X
      rfl
  | succ L ih =>
      intro π θ X
      calc
        transformer (T := T) (layerwisePermute π θ) X
            = transformer (T := T) (Fin.tail (layerwisePermute π θ))
                (layer (layerwisePermute π θ) 0 X) := rfl
        _ = transformer (T := T)
                (layerwisePermute (LayerPermutations.tail π) (Fin.tail θ))
                (layer θ 0 X) := by
              rw [tail_layerwisePermute, layer_layerwisePermute]
        _ = transformer (T := T) (Fin.tail θ) (layer θ 0 X) :=
              ih (LayerPermutations.tail π) (Fin.tail θ) (layer θ 0 X)
        _ = transformer (T := T) θ X := rfl

/-- Equality of realizations on all sequence inputs of length `T`. -/
def sameRealization {L k d T : Nat} (θ θ' : Params L k d) : Prop :=
  ∀ X : Matrix (Fin d) (Fin T) ℝ,
    transformer (T := T) θ X = transformer (T := T) θ' X

/-- The full matrix-level fiber through `θ'`. -/
def matrixFiber {L k d T : Nat} (θ' : Params L k d) :
    Set (Params L k d) :=
  {θ | sameRealization (T := T) θ θ'}

/-- The layerwise head-permutation orbit through `θ'`. -/
def layerwisePermutationOrbit {L k d : Nat} (θ' : Params L k d) :
    Set (Params L k d) :=
  Set.range fun π : LayerPermutations L k => layerwisePermute π θ'

/-- Freeness of the layerwise head-permutation action at one parameter. -/
def LayerwiseFreeAt {L k d : Nat} (θ : Params L k d) : Prop :=
  ∀ π : LayerPermutations L k, layerwisePermute π θ = θ → π = 1

/-- The primed same-layer attention matrices are pairwise distinct. -/
def PairwiseDistinctAttention {L k d : Nat} (θ : Params L k d) : Prop :=
  ∀ l : Fin L, Function.Injective fun a : Fin k => attentionMatrix θ l a

/-- Target-to-source paired matrix matching, with the single permutation matching
both attention and value matrices. -/
def LayerwisePairedBy {L k d : Nat} (θ θ' : Params L k d)
    (σ : LayerPermutations L k) : Prop :=
  ∀ l : Fin L, ∀ h : Fin k,
    attentionMatrix θ l (σ l h) = attentionMatrix θ' l h ∧
      valueMatrix θ l (σ l h) = valueMatrix θ' l h

/-- The uniqueness surface supplied by the main theorem for a fixed pair
`(θ, θ')`. -/
def HasUniqueLayerwisePairedMatching {L k d : Nat}
    (θ θ' : Params L k d) : Prop :=
  ∃! σ : LayerPermutations L k, LayerwisePairedBy θ θ' σ

/-- The part of `thm:main` needed by `cor:matrix-fiber`, stated as an input API. -/
def mainTheoremMatrixMatchingInterface {L k d T : Nat}
    (Generic : Set (Params L k d)) : Prop :=
  ∀ θ' : Params L k d, θ' ∈ Generic →
    ∀ θ : Params L k d,
      θ ∈ matrixFiber (T := T) θ' →
        HasUniqueLayerwisePairedMatching θ θ'

/-- Convert a target-to-source matching into the inverse layerwise orbit equality. -/
theorem eq_layerwisePermute_inv_of_layerwisePairedBy {L k d : Nat}
    {θ θ' : Params L k d} {σ : LayerPermutations L k}
    (hmatch : LayerwisePairedBy θ θ' σ) :
    θ = layerwisePermute (LayerPermutations.inv σ) θ' := by
  apply Params.ext
  · intro l a
    have hvalue := (hmatch l ((σ l).symm a)).2
    simpa [LayerPermutations.inv, layerwisePermute] using hvalue
  · intro l a
    have hattention := (hmatch l ((σ l).symm a)).1
    simpa [LayerPermutations.inv, layerwisePermute] using hattention

/-- A paired target-to-source matching places `θ` in the orbit of `θ'`. -/
theorem mem_layerwisePermutationOrbit_of_layerwisePairedBy {L k d : Nat}
    {θ θ' : Params L k d} {σ : LayerPermutations L k}
    (hmatch : LayerwisePairedBy θ θ' σ) :
    θ ∈ layerwisePermutationOrbit θ' :=
  ⟨LayerPermutations.inv σ,
    (eq_layerwisePermute_inv_of_layerwisePairedBy hmatch).symm⟩

/-- The orbit is contained in the fiber by finite-sum relabeling invariance. -/
theorem mem_matrixFiber_of_mem_layerwisePermutationOrbit {L k d T : Nat}
    {θ θ' : Params L k d}
    (horbit : θ ∈ layerwisePermutationOrbit θ') :
    θ ∈ matrixFiber (T := T) θ' := by
  rcases horbit with ⟨π, rfl⟩
  intro X
  exact transformer_layerwisePermute π θ' X

/-- Pairwise distinct target attentions give freeness of the layerwise action. -/
theorem layerwiseFreeAt_of_pairwiseDistinctAttention {L k d : Nat}
    {θ : Params L k d} (hθ : PairwiseDistinctAttention θ) :
    LayerwiseFreeAt θ := by
  intro π hfix
  funext l
  apply Equiv.ext
  intro a
  have hhead : θ l (π l a) = θ l a := by
    simpa [layerwisePermute] using congrFun (congrFun hfix l) a
  have hattention :
      attentionMatrix θ l (π l a) = attentionMatrix θ l a := by
    simpa [attentionMatrix] using congrArg Prod.snd hhead
  simpa using hθ l hattention

/-- Matrix-level fiber conclusion: exact orbit equality plus freeness. -/
structure MatrixFiberConclusion {L k d T : Nat}
    (θ' : Params L k d) : Prop where
  fiber_eq_orbit :
    matrixFiber (T := T) θ' = layerwisePermutationOrbit θ'
  free_at : LayerwiseFreeAt θ'

/-- TeX `cor:matrix-fiber`, statement/API form.  The argument `Generic`
represents `P_{L,k} \ N_{L,k}`. -/
def cor_matrix_fiber {L k d T : Nat}
    (Generic : Set (Params L k d)) : Prop :=
  ∀ θ' : Params L k d, θ' ∈ Generic →
    MatrixFiberConclusion (T := T) θ'

/-- Formal reduction from the main-theorem matching interface to
TeX `cor:matrix-fiber`. -/
theorem cor_matrix_fiber_of_mainTheoremMatrixMatchingInterface {L k d T : Nat}
    {Generic : Set (Params L k d)}
    (hmain : mainTheoremMatrixMatchingInterface (T := T) Generic)
    (hsep : ∀ θ' : Params L k d, θ' ∈ Generic →
      PairwiseDistinctAttention θ') :
    cor_matrix_fiber (T := T) Generic := by
  intro θ' hθ'
  refine ⟨?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro θ hθ
      rcases hmain θ' hθ' θ hθ with ⟨σ, hσ, _huniq⟩
      exact mem_layerwisePermutationOrbit_of_layerwisePairedBy hσ
    · intro θ hθ
      exact mem_matrixFiber_of_mem_layerwisePermutationOrbit (T := T) hθ
  · exact layerwiseFreeAt_of_pairwiseDistinctAttention (hsep θ' hθ')

end

end TransformerIdentifiability.NLayer.KHead
