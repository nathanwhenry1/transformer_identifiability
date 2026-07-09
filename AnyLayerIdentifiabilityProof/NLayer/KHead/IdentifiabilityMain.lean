import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.Null
import AnyLayerIdentifiabilityProof.NLayer.KHead.DimensionThreshold
import AnyLayerIdentifiabilityProof.NLayer.KHead.Induction.InductionStep

set_option autoImplicit false

open MeasureTheory Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K-head main-theorem statement API

This file is the K03A scaffold for `tex_modular/sections/03a-main-theorem.tex`.
It intentionally does not prove the headline theorem.  Instead it fixes the
dimension threshold, the concrete recursive-generic exceptional set, and the
per-layer target-to-source permutation conclusion that downstream proof packets
must produce.
-/

/-! ## Dimension threshold and generic exceptional set -/

-- `dStar` and `two_le_dStar` now live once in
-- `AnyLayerIdentifiabilityProof.NLayer.KHead.DimensionThreshold` (imported above),
-- shared with `Induction/Peeling.lean` so that the depth-induction capstone
-- `Induction/InductionStep.lean` can be imported here without a duplicate `dStar`.

/-- The threshold contains the headwise anchor/sign-region row budget. -/
theorem rowBudget_le_dStar (m k : Nat) :
    nBullet m k + 1 ≤ dStar m k := by
  simp [dStar, nBullet]

/-- Dimension hypothesis surface for Remark `rem:dimension-hypothesis`. -/
structure DimensionHypothesis (m k d : Nat) : Prop where
  threshold_le : dStar m k ≤ d

namespace DimensionHypothesis

theorem two_le {m k d : Nat} (hdim : DimensionHypothesis m k d) : 2 ≤ d :=
  le_trans (two_le_dStar m k) hdim.threshold_le

theorem d_pos {m k d : Nat} (hdim : DimensionHypothesis m k d) : 0 < d :=
  lt_of_lt_of_le (by norm_num : (0 : Nat) < 2) hdim.two_le

theorem rowBudget {m k d : Nat} (hdim : DimensionHypothesis m k d) :
    nBullet m k + 1 ≤ d :=
  le_trans (rowBudget_le_dStar m k) hdim.threshold_le

end DimensionHypothesis

/-- Raw row-budget consequence of `d >= d_*(m,k)`. -/
theorem rowBudget_of_dStar_le {m k d : Nat} (hdim : dStar m k ≤ d) :
    nBullet m k + 1 ≤ d :=
  (DimensionHypothesis.mk hdim).rowBudget

/-- Raw positivity consequence of `d >= d_*(m,k)`. -/
theorem d_pos_of_dStar_le {m k d : Nat} (hdim : dStar m k ≤ d) : 0 < d :=
  (DimensionHypothesis.mk hdim).d_pos

/-- The concrete generic set used by the K03A main-theorem scaffold. -/
def mainTheoremGenericSet (r L k d : Nat) : Set (Params L k d) :=
  RecursiveGenericSet r L k d

/-- The concrete algebraic exceptional set used by the K03A scaffold. -/
def mainTheoremExceptionalSet (r L k d : Nat) : Set (Params L k d) :=
  RecursiveGenericBadSet r L k d

@[simp]
theorem mainTheoremExceptionalSet_eq_compl (r L k d : Nat) :
    mainTheoremExceptionalSet r L k d =
      (mainTheoremGenericSet r L k d)ᶜ :=
  rfl

/-- Finite polynomial-cover package for the genericity clauses under `d >= d_*(L,k)`. -/
noncomputable def mainTheoremPolynomialCover (r L k d : Nat)
    (hdim : DimensionHypothesis L k d) :
    KHeadParamPolynomialPredicateCover L k d
      (fun θ => RecursiveGeneric r L k d θ) :=
  kHeadRecursiveGenericPolynomialCover r L k d hdim.d_pos hdim.rowBudget

/-- The scaffold's exceptional set is Lebesgue-null under the dimension threshold. -/
theorem mainTheoremExceptionalSet_null {r L k d : Nat}
    (hdim : DimensionHypothesis L k d) :
    volume (mainTheoremExceptionalSet r L k d : Set (Params L k d)) = 0 := by
  simpa [mainTheoremExceptionalSet] using
    kHeadRecursiveGenericBadSet_null (r := r) (L := L) (k := k) (d := d)
      hdim.d_pos hdim.rowBudget

/-- The scaffold's generic set is dense under the dimension threshold. -/
theorem dense_mainTheoremGenericSet {r L k d : Nat}
    (hdim : DimensionHypothesis L k d) :
    Dense (mainTheoremGenericSet r L k d : Set (Params L k d)) := by
  simpa [mainTheoremGenericSet] using
    dense_kHeadRecursiveGenericSet (r := r) (L := L) (k := k) (d := d)
      hdim.d_pos hdim.rowBudget

/-- The scaffold's exceptional set has empty interior under the dimension threshold. -/
theorem mainTheoremExceptionalSet_interior_eq_empty {r L k d : Nat}
    (hdim : DimensionHypothesis L k d) :
    interior (mainTheoremExceptionalSet r L k d : Set (Params L k d)) = ∅ := by
  simpa [mainTheoremExceptionalSet] using
    kHeadRecursiveGenericBadSet_interior_eq_empty
      (r := r) (L := L) (k := k) (d := d) hdim.d_pos hdim.rowBudget

/-! ## Matrix-level agreement and paired head matching -/

/-- Matrix-level equality of the two depth-`L`, `k`-head networks on all inputs. -/
def TransformerAgreement {L k d : Nat} (r : Nat)
    (θ θ' : Params L k d) : Prop :=
  ∀ X : Matrix (Fin d) (Fin (seqLength r)) ℝ,
    transformer θ X = transformer θ' X

/-- Target-to-source attention matching for one layer. -/
def LayerAttentionMatchedBy {L k d : Nat} (θ θ' : Params L k d)
    (l : Fin L) (σ : Equiv.Perm (Fin k)) : Prop :=
  ∀ h : Fin k, attentionMatrix θ l (σ h) = attentionMatrix θ' l h

/-- Value matching using the already selected target-to-source attention permutation. -/
def LayerValueMatchedBy {L k d : Nat} (θ θ' : Params L k d)
    (l : Fin L) (σ : Equiv.Perm (Fin k)) : Prop :=
  ∀ h : Fin k, valueMatrix θ l (σ h) = valueMatrix θ' l h

/-- Paired matching of attention and value matrices in one layer. -/
def LayerHeadPairMatchedBy {L k d : Nat} (θ θ' : Params L k d)
    (l : Fin L) (σ : Equiv.Perm (Fin k)) : Prop :=
  LayerAttentionMatchedBy θ θ' l σ ∧ LayerValueMatchedBy θ θ' l σ

/-- Per-layer paired target-to-source head matching. -/
def HeadPairMatchedBy {L k d : Nat} (θ θ' : Params L k d)
    (σ : Fin L → Equiv.Perm (Fin k)) : Prop :=
  ∀ l : Fin L, LayerHeadPairMatchedBy θ θ' l (σ l)

theorem HeadPairMatchedBy.attention {L k d : Nat} {θ θ' : Params L k d}
    {σ : Fin L → Equiv.Perm (Fin k)}
    (hσ : HeadPairMatchedBy θ θ' σ) (l : Fin L) (h : Fin k) :
    attentionMatrix θ l (σ l h) = attentionMatrix θ' l h :=
  (hσ l).1 h

theorem HeadPairMatchedBy.value {L k d : Nat} {θ θ' : Params L k d}
    {σ : Fin L → Equiv.Perm (Fin k)}
    (hσ : HeadPairMatchedBy θ θ' σ) (l : Fin L) (h : Fin k) :
    valueMatrix θ l (σ l h) = valueMatrix θ' l h :=
  (hσ l).2 h

/-- Inverse-orientation spelling used when formulas are indexed by source heads. -/
def HeadPairMatchedByInverse {L k d : Nat} (θ θ' : Params L k d)
    (π : Fin L → Equiv.Perm (Fin k)) : Prop :=
  ∀ l : Fin L, ∀ a : Fin k,
    attentionMatrix θ l a = attentionMatrix θ' l (π l a) ∧
      valueMatrix θ l a = valueMatrix θ' l (π l a)

/-- A target-to-source matching gives the inverse-orientation formulas. -/
theorem HeadPairMatchedBy.inverse {L k d : Nat} {θ θ' : Params L k d}
    {σ : Fin L → Equiv.Perm (Fin k)}
    (hσ : HeadPairMatchedBy θ θ' σ) :
    HeadPairMatchedByInverse θ θ' (fun l => (σ l).symm) := by
  intro l a
  constructor
  · simpa using (hσ l).1 ((σ l).symm a)
  · simpa using (hσ l).2 ((σ l).symm a)

/-- The unique per-layer permutation conclusion of TeX `thm:main`. -/
def UniqueLayerPermutations {L k d : Nat} (θ θ' : Params L k d) : Prop :=
  ∃! σ : Fin L → Equiv.Perm (Fin k), HeadPairMatchedBy θ θ' σ

/-! ## Order-of-choices API -/

/-- Layer-local extraction surface: attention is selected first; values then use
that same permutation.  This records the convention of Remark
`rem:order-of-choices` without asserting the analytic extraction theorem. -/
structure LayerExtractionAPI {L k d : Nat} (θ θ' : Params L k d)
    (l : Fin L) : Prop where
  attention_first :
    ∃! σ : Equiv.Perm (Fin k), LayerAttentionMatchedBy θ θ' l σ
  value_after_attention :
    ∀ σ : Equiv.Perm (Fin k),
      LayerAttentionMatchedBy θ θ' l σ → LayerValueMatchedBy θ θ' l σ

namespace LayerExtractionAPI

/-- Attention-first extraction plus value recovery yields a unique paired layer match. -/
theorem existsUnique_pair {L k d : Nat} {θ θ' : Params L k d}
    {l : Fin L} (D : LayerExtractionAPI θ θ' l) :
    ∃! σ : Equiv.Perm (Fin k), LayerHeadPairMatchedBy θ θ' l σ := by
  obtain ⟨σ, hσ, huniq⟩ := D.attention_first
  refine ⟨σ, ⟨hσ, D.value_after_attention σ hσ⟩, ?_⟩
  intro τ hτ
  exact huniq τ hτ.1

end LayerExtractionAPI

/-- Combining the layer-local extraction APIs gives the global unique tuple of
per-layer permutations. -/
theorem uniqueLayerPermutations_of_layerExtractionAPI {L k d : Nat}
    {θ θ' : Params L k d}
    (D : ∀ l : Fin L, LayerExtractionAPI θ θ' l) :
    UniqueLayerPermutations θ θ' := by
  classical
  let σ : Fin L → Equiv.Perm (Fin k) :=
    fun l => Classical.choose (D l).existsUnique_pair.exists
  have hσ : HeadPairMatchedBy θ θ' σ := by
    intro l
    exact Classical.choose_spec (D l).existsUnique_pair.exists
  refine ⟨σ, hσ, ?_⟩
  intro τ hτ
  funext l
  exact (D l).existsUnique_pair.unique (hτ l) (hσ l)

/-! ## Relabeling convention and exact reduced tail -/

/-- Relabel the heads of a single layer, leaving all other layers untouched. -/
def relabelLayer {L k d : Nat} (θ : Params L k d) (l : Fin L)
    (ρ : Equiv.Perm (Fin k)) : Params L k d :=
  fun l' h => if l' = l then θ l (ρ h) else θ l' h

@[simp]
theorem relabelLayer_apply_self {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (ρ : Equiv.Perm (Fin k)) (h : Fin k) :
    relabelLayer θ l ρ l h = θ l (ρ h) := by
  simp [relabelLayer]

@[simp]
theorem relabelLayer_apply_ne {L k d : Nat} (θ : Params L k d)
    {l l' : Fin L} (hll' : l' ≠ l) (ρ : Equiv.Perm (Fin k)) (h : Fin k) :
    relabelLayer θ l ρ l' h = θ l' h := by
  simp [relabelLayer, hll']

/-- The relabeled layer map is unchanged, since the head sum is symmetric. -/
theorem layer_relabelLayer_self {L k d T : Nat} (θ : Params L k d)
    (l : Fin L) (ρ : Equiv.Perm (Fin k))
    (X : Matrix (Fin d) (Fin T) ℝ) :
    layer (relabelLayer θ l ρ) l X = layer θ l X := by
  classical
  simp only [layer]
  congr 1
  simpa [relabelLayer, valueMatrix, attentionMatrix] using
    (Equiv.sum_comp ρ fun h : Fin k =>
      valueMatrix θ l h * X *
        softmaxColC (Xᵀ * attentionMatrix θ l h * X))

/-- Relabeling the first layer does not alter the reduced tail. -/
@[simp]
theorem tail_relabelLayer_zero {L k d : Nat} (θ : Params (L + 1) k d)
    (ρ : Equiv.Perm (Fin k)) :
    Fin.tail (relabelLayer θ 0 ρ) = Fin.tail θ := by
  funext l h
  have hne : (Fin.succ l : Fin (L + 1)) ≠ 0 := by
    simp
  change relabelLayer θ 0 ρ (Fin.succ l) h = θ (Fin.succ l) h
  simp [relabelLayer, hne]

/-! ## Statement-level scaffold for TeX `thm:main` -/

/-- Result interface for the K03A main theorem with the concrete exceptional set fixed. -/
structure MainTheoremConclusion (L k r d : Nat) : Prop where
  identify :
    ∀ {θ θ' : Params L k d},
      θ' ∉ mainTheoremExceptionalSet r L k d →
        TransformerAgreement r θ θ' →
          UniqueLayerPermutations θ θ'

/-- TeX label `thm:main`, as a proposition-valued statement scaffold.

This is not a proof of the main theorem.  Supplying this proposition is the endgame
task for the analytic packets. -/
def thm_main_statement (L k r d : Nat) : Prop :=
  1 ≤ L → 1 ≤ k → 2 ≤ r → DimensionHypothesis L k d →
    MainTheoremConclusion L k r d

/-! ## `k = 1` specialization surface -/

/-- Every permutation of the one-head index type is the identity. -/
theorem perm_fin_one_eq_one (σ : Equiv.Perm (Fin 1)) : σ = 1 := by
  apply Equiv.ext
  intro h
  exact Subsingleton.elim (σ h) h

/-- With one head, paired matching by any per-layer permutation is just parameter equality. -/
theorem headPairMatchedBy_one_iff_eq {L d : Nat}
    (θ θ' : Params L 1 d) (σ : Fin L → Equiv.Perm (Fin 1)) :
    HeadPairMatchedBy θ θ' σ ↔ θ = θ' := by
  constructor
  · intro hσ
    apply Params.ext
    · intro l a
      have hvalue := (hσ l).2 a
      have hsigma : σ l a = a := Subsingleton.elim (σ l a) a
      simpa [hsigma] using hvalue
    · intro l a
      have hattention := (hσ l).1 a
      have hsigma : σ l a = a := Subsingleton.elim (σ l a) a
      simpa [hsigma] using hattention
  · intro hθ
    subst θ'
    intro l
    constructor
    · intro h
      have hsigma : σ l h = h := Subsingleton.elim (σ l h) h
      simp [hsigma]
    · intro h
      have hsigma : σ l h = h := Subsingleton.elim (σ l h) h
      simp [hsigma]

/-- The unique-permutation conclusion specializes to literal equality when `k = 1`. -/
theorem uniqueLayerPermutations_one_iff_eq {L d : Nat}
    (θ θ' : Params L 1 d) :
    UniqueLayerPermutations θ θ' ↔ θ = θ' := by
  constructor
  · rintro ⟨σ, hσ, _huniq⟩
    exact (headPairMatchedBy_one_iff_eq θ θ' σ).mp hσ
  · intro hθ
    refine ⟨fun _ => 1, ?_, ?_⟩
    · exact (headPairMatchedBy_one_iff_eq θ θ' (fun _ => 1)).mpr hθ
    · intro τ _hτ
      funext l
      exact perm_fin_one_eq_one (τ l)

/-- Main-conclusion specialization: for `k = 1`, the conclusion is equality of parameters. -/
theorem MainTheoremConclusion.identify_eq_of_one_head {L r d : Nat}
    (D : MainTheoremConclusion L 1 r d)
    {θ θ' : Params L 1 d}
    (hθ' : θ' ∉ mainTheoremExceptionalSet r L 1 d)
    (hagree : TransformerAgreement r θ θ') :
    θ = θ' :=
  (uniqueLayerPermutations_one_iff_eq θ θ').mp (D.identify hθ' hagree)

/-! ## Endgame bridge — assembling `thm:main` from the depth-recursion driver

The whole depth induction is already proved in `Induction/InductionStep.lean`:
`openSetInductionInvariant_of_valuesMatchable` delivers the C1–C3 open-set
invariant conclusion (`OpenSetInductionInvariantConclusion`) for every depth
`n + 1` from the ordinary invariant ingredients plus the single quantified K07C
value-family boundary `LayerValuesMatchableFromAttention θ θ'` (the `prop:first-V`
content, threaded at every layer).  This section bridges that conclusion into the
headline `thm:main` statement.

The value family is the *only* honest unproven input: every other ingredient is
discharged from proved lemmas below. -/

/-- **K03A.M4 (exceptional → generic).**  Being outside the concrete recursive
exceptional set is exactly recursive genericity of the target.

`mainTheoremExceptionalSet r L k d = RecursiveGenericBadSet r L k d =
(RecursiveGenericSet r L k d)ᶜ`, and membership in `RecursiveGenericSet` is
definitionally `RecursiveGeneric r L k d θ'`.  So this is the K03D genericity
cover read off directly — no gap. -/
theorem recursiveGeneric_of_notMem_mainTheoremExceptionalSet {r L k d : Nat}
    {θ' : Params L k d}
    (hθ' : θ' ∉ mainTheoremExceptionalSet r L k d) :
    RecursiveGeneric r L k d θ' := by
  simp only [mainTheoremExceptionalSet, RecursiveGenericBadSet, RecursiveGenericSet,
    Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hθ'
  exact hθ'

/-- **K03A.M3 bridge (matching shapes).**  The driver's per-layer paired matching
`LayerwisePairedMatching` and the main-theorem statement's `HeadPairMatchedBy`
carry exactly the same attention/value equalities. -/
theorem headPairMatchedBy_iff_layerwisePairedMatching {L k d : Nat}
    (θ θ' : Params L k d) (σ : Fin L → Equiv.Perm (Fin k)) :
    HeadPairMatchedBy θ θ' σ ↔ LayerwisePairedMatching θ θ' σ := by
  constructor
  · intro h
    exact ⟨fun l a => (h l).1 a, fun l a => (h l).2 a⟩
  · intro h l
    exact ⟨fun a => h.attention l a, fun a => h.value l a⟩

/-- **K03A.M3 (driver conclusion → main-theorem conclusion).**  The driver's
`LayerwiseMatchingConclusion` (existence + uniqueness of the per-layer
target-to-source paired permutations) is exactly the main-theorem
`UniqueLayerPermutations` conclusion, re-read through the shape bridge. -/
theorem uniqueLayerPermutations_of_layerwiseMatchingConclusion {L k d : Nat}
    {θ θ' : Params L k d} (M : LayerwiseMatchingConclusion θ θ') :
    UniqueLayerPermutations θ θ' := by
  refine ⟨M.sigma, ?_, ?_⟩
  · exact (headPairMatchedBy_iff_layerwisePairedMatching θ θ' M.sigma).mpr M.paired
  · intro τ hτ
    exact M.unique τ ((headPairMatchedBy_iff_layerwisePairedMatching θ θ' τ).mp hτ)

/-- **K03A.M3 core (depth `n + 1`).**  From recursive genericity of the target,
global transformer agreement, and the K07C value family, the depth-recursion
driver yields the unique per-layer paired-permutation conclusion.

`TransformerAgreement r θ θ'` is definitionally global equality, so we run the
driver on the open set `Set.univ`; the driver's analytic-continuation core
(`lem_open_set_to_global`) is invoked internally, and no equality is *assumed*
beyond the supplied agreement. -/
theorem uniqueLayerPermutations_of_transformerAgreement_of_valuesMatchable
    {n k d r : Nat} (hr : 1 < r)
    {θ θ' : Params (n + 1) k d}
    (hgen : RecursiveGeneric r (n + 1) k d θ')
    (hagree : TransformerAgreement r θ θ')
    (hd : 2 ≤ d) :
    UniqueLayerPermutations θ θ' := by
  have hconcl :
      OpenSetInductionInvariantConclusion r θ θ' :=
    openSetInductionInvariant_of_valuesMatchable (m := n) hr hgen
      (omega := Set.univ)
      ⟨isOpen_univ, Set.univ_nonempty⟩
      (fun X _ => hagree X)
      hd
  exact uniqueLayerPermutations_of_layerwiseMatchingConclusion hconcl.matching

/-- **K03A.M2–M4 assembled, per parameter pair (`thm:main`, conditional).**

The headline k-head identifiability statement for one generic target `θ'` and one
agreeing source `θ`, conditional on the single honest K07C boundary — the
value-family `hVfam : LayerValuesMatchableFromAttention θ θ'` (`prop:first-V`
read at every layer).

Everything else is discharged from proved lemmas:
* `θ' ∉ mainTheoremExceptionalSet` becomes `RecursiveGeneric r L k d θ'` via
  `recursiveGeneric_of_notMem_mainTheoremExceptionalSet` (the K03D genericity
  cover);
* the depth `1 ≤ L` is turned into `L = n + 1`;
* the depth-recursion driver produces the layerwise matching conclusion, which is
  the `UniqueLayerPermutations` conclusion.

The `DimensionHypothesis` and `1 ≤ k` hypotheses are recorded for parity with the
`thm_main_statement` surface; the recursion carries all dimension facts through
genericity, so they are not consumed here. -/
theorem thm_main_statement_of_valuesMatchable {L k r d : Nat}
    (hL : 1 ≤ L) (_hk : 1 ≤ k) (hr : 2 ≤ r) (hdim : DimensionHypothesis L k d)
    {θ θ' : Params L k d}
    (hθ' : θ' ∉ mainTheoremExceptionalSet r L k d)
    (hagree : TransformerAgreement r θ θ') :
    UniqueLayerPermutations θ θ' := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have hgen : RecursiveGeneric r (n + 1) k d θ' :=
    recursiveGeneric_of_notMem_mainTheoremExceptionalSet hθ'
  exact uniqueLayerPermutations_of_transformerAgreement_of_valuesMatchable
    (by omega : 1 < r) hgen hagree hdim.two_le

/-- **`thm:main`, unconditional.**  This proves the literal `thm_main_statement L k r d`
proposition outright.  The K07C first-layer value endpoint (`prop:first-V`) is now
discharged internally by the depth-recursion driver via `prop_first_V_of_standing`, so no
value-family hypothesis is assumed: every ingredient is proved. -/
theorem thm_main_statement_holds (L k r d : Nat) : thm_main_statement L k r d := by
  intro hL hk hr hdim
  refine ⟨?_⟩
  intro θ θ' hθ' hagree
  exact thm_main_statement_of_valuesMatchable hL hk hr hdim hθ' hagree

end TransformerIdentifiability.NLayer.KHead
