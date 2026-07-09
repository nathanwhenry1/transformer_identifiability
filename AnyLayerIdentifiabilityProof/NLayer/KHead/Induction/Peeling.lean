import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.AnchorCertificate
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.Saturated
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.PoleTransfer
import AnyLayerIdentifiabilityProof.NLayer.KHead.Induction.Relabel
import AnyLayerIdentifiabilityProof.NLayer.KHead.DimensionThreshold

set_option autoImplicit false

open Matrix
open Filter
open scoped BigOperators Matrix.Norms.Frobenius

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K-head Step 3 peeling and induction API

This file is the K08 statement/API scaffold for
`tex_modular/sections/08-step3-peeling.tex`.  It records the first-layer
paired relabeling, the exact reduced-tail agreement package, and the
open-induction/main-theorem interfaces without asserting the hard analytic
peeling claims as theorems.
-/

noncomputable section

/-! ## Dimension threshold and transformer agreement -/

-- `dStar` and `two_le_dStar` now live once in
-- `AnyLayerIdentifiabilityProof.NLayer.KHead.DimensionThreshold` (imported above),
-- shared with `IdentifiabilityMain.lean` so that the peeling capstone can be
-- co-imported into the main-theorem bridge without a duplicate declaration.

theorem rows_le_dStar (m k : Nat) : k * m + 1 ≤ dStar m k :=
  le_max_right _ _

theorem two_le_of_dStar_le {m k d : Nat} (h : dStar m k ≤ d) : 2 ≤ d :=
  (two_le_dStar m k).trans h

/-- Pointwise equality of two transformer maps on a set of inputs. -/
def TransformerAgreementOn {L k d T : Nat}
    (theta theta' : Params L k d)
    (Omega : Set (Matrix (Fin d) (Fin T) ℝ)) : Prop :=
  ∀ X : Matrix (Fin d) (Fin T) ℝ, X ∈ Omega ->
    transformer theta X = transformer theta' X

/-- Global equality of two transformer maps. -/
def TransformerAgreementEverywhere {L k d T : Nat}
    (theta theta' : Params L k d) : Prop :=
  ∀ X : Matrix (Fin d) (Fin T) ℝ,
    transformer theta X = transformer theta' X

/-- Nonempty Euclidean-open agreement package carried by the invariant. -/
structure OpenTransformerAgreement {L k d : Nat} (r : Nat)
    (theta theta' : Params L k d)
    (Omega : Set (Matrix (Fin d) (Fin (seqLength r)) ℝ)) : Prop where
  isOpen : IsOpen Omega
  nonempty : Omega.Nonempty
  eq_on : TransformerAgreementOn theta theta' Omega

-- Note: the `lem-open-set-to-global.S` statement surface is not restated here.
-- The live version lives in `Induction/Invariant.lean` as
-- `TransformerIdentifiability.NLayer.KHead.lem_open_set_to_global_S`; the former
-- dead copy in this file collided with it under the same namespace and blocked
-- co-importing Peeling and Invariant, so it was removed.

/-! ## First-layer relabeling -/

/-- Tail parameters, deleting the current first layer. -/
abbrev tailParams {m k d : Nat} (theta : Params (m + 1) k d) :
    Params m k d :=
  Fin.tail theta

/-- TeX `\bar\vartheta_{\ge2}=\vartheta_{\ge2}`.

The canonical `relabelFirstLayer` and its `_zero`/`_succ` simp lemmas now live in
`Induction/Relabel.lean`; this is the `tailParams` (`= Fin.tail`) restatement of
the shared `relabelFirstLayer_tail`. -/
@[simp]
theorem tailParams_relabelFirstLayer {m k d : Nat}
    (theta : Params (m + 1) k d) (sigma : Equiv.Perm (Fin k)) :
    tailParams (relabelFirstLayer theta sigma) = tailParams theta :=
  relabelFirstLayer_tail theta sigma

/-- First-layer attention matching in target-to-source orientation. -/
def firstLayerAttentionsMatched {m k d : Nat}
    (theta theta' : Params (m + 1) k d)
    (sigma : Equiv.Perm (Fin k)) : Prop :=
  ∀ h : Fin k,
    attentionMatrix theta 0 (sigma h) = attentionMatrix theta' 0 h

/-- Paired first-layer matching: the same permutation matches attention and value. -/
def firstLayerHeadsMatched {m k d : Nat}
    (theta theta' : Params (m + 1) k d)
    (sigma : Equiv.Perm (Fin k)) : Prop :=
  ∀ h : Fin k,
    attentionMatrix theta 0 (sigma h) = attentionMatrix theta' 0 h ∧
      valueMatrix theta 0 (sigma h) = valueMatrix theta' 0 h

/-- First-layer value matching in the paired target-to-source orientation. -/
def firstLayerValuesMatchedForPeeling {m k d : Nat}
    (theta theta' : Params (m + 1) k d)
    (sigma : Equiv.Perm (Fin k)) : Prop :=
  ∀ h : Fin k,
    valueMatrix theta 0 (sigma h) = valueMatrix theta' 0 h

/-- The K07C first-value statement is definitionally the K08 peeling value
matching predicate when `L = m + 1` and the first layer is indexed by `0`. -/
theorem firstLayerValuesMatchedForPeeling_of_firstLayerValuesMatched {m k d : Nat}
    {theta theta' : Params (m + 1) k d} {sigma : Equiv.Perm (Fin k)}
    (hV : firstLayerValuesMatched (Nat.succ_pos m) theta theta' sigma) :
    firstLayerValuesMatchedForPeeling theta theta' sigma := by
  intro h
  simpa [firstLayerValuesMatched, firstLayerValuesMatchedForPeeling] using hV h

/-- Local Step 2 value-identification input consumed by this peeling scaffold.

`Step2/Saturated.lean` exposes the eventual `prop_first_V_S` API.  This local
bridge records only the value-matching payload needed by Step 3 until the
gated Step 2 value theorem is connected directly.
-/
structure FirstLayerValueMatchingData {m k d : Nat}
    (theta theta' : Params (m + 1) k d) where
  sigma : Equiv.Perm (Fin k)
  values_matched : firstLayerValuesMatchedForPeeling theta theta' sigma

/-- Step 1 plus Step 2 first-layer output consumed by peeling.

This packages `prop:first-A` and `prop:first-V`: `sigma` is uniquely extracted
from attention matrices, and the same `sigma` also matches the values.
-/
structure FirstLayerPeelingData {m k d : Nat}
    (theta theta' : Params (m + 1) k d) where
  sigma : Equiv.Perm (Fin k)
  attention_matched : firstLayerAttentionsMatched theta theta' sigma
  value_matched : firstLayerValuesMatchedForPeeling theta theta' sigma
  attention_unique :
    ∀ tau : Equiv.Perm (Fin k),
      firstLayerAttentionsMatched theta theta' tau -> tau = sigma

namespace FirstLayerPeelingData

variable {m k d : Nat}
variable {theta theta' : Params (m + 1) k d}

/-- The stored attention and value facts form paired first-layer matching. -/
theorem heads_matched (D : FirstLayerPeelingData theta theta') :
    firstLayerHeadsMatched theta theta' D.sigma := by
  intro h
  exact ⟨D.attention_matched h, D.value_matched h⟩

/-- After paired relabeling, each first-layer head pair equals the target head. -/
theorem relabeled_firstLayer_head_eq
    (D : FirstLayerPeelingData theta theta') (h : Fin k) :
    relabelFirstLayer theta D.sigma 0 h = theta' 0 h := by
  apply Prod.ext
  · simpa [valueMatrix] using D.value_matched h
  · simpa [attentionMatrix] using D.attention_matched h

/-- The first-layer relabeling does not alter the source tail. -/
theorem tail_relabel_eq (D : FirstLayerPeelingData theta theta') :
    tailParams (relabelFirstLayer theta D.sigma) = tailParams theta :=
  tailParams_relabelFirstLayer theta D.sigma

/-- Build the peeling data from the Step 2 value payload plus Step 1 attention data. -/
def of_firstLayerValueMatchingData (D : FirstLayerValueMatchingData theta theta')
    (hA : firstLayerAttentionsMatched theta theta' D.sigma)
    (hAuniq :
      ∀ tau : Equiv.Perm (Fin k),
        firstLayerAttentionsMatched theta theta' tau -> tau = D.sigma) :
    FirstLayerPeelingData theta theta' where
  sigma := D.sigma
  attention_matched := hA
  value_matched := D.values_matched
  attention_unique := hAuniq

end FirstLayerPeelingData

/-- **K08.M4 (conditional same-`σ` first-layer assembly).**

Builds the first-layer peeling package `FirstLayerPeelingData θ θ'` from
* the *proven* K06C common-first-gates export
  `Step1.step1CommonFirstGates hr H` (which supplies the canonical first-attention
  permutation together with its matching and uniqueness facts), and
* the single genuinely-unproven K07C value endpoint `hV`.

Here `σ₀ := (Step1.step1CommonFirstGates hr H).sigma` is the *canonical* K06C
first-attention permutation.  Both attention fields of the resulting package
(`attention_matched`, `attention_unique`) are discharged verbatim from the proven
gates (`attention_eq`, `attention_unique`).  The ONLY hypothesis here that is not
already proven upstream is `hV`, i.e. the K07C first-layer value matching for that
canonical `σ₀`; it is *not* a restatement of the conclusion (it fixes only the
value equalities for the single fixed permutation `σ₀`, whereas the conclusion also
carries the attention matching and its uniqueness). -/
noncomputable def firstLayerPeelingData_of_valuesMatched {m k d r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1.Step1StandingHypotheses r θ θ')
    (hV : firstLayerValuesMatchedForPeeling θ θ'
      (Step1.step1CommonFirstGates hr H).sigma) :
    FirstLayerPeelingData θ θ' :=
  FirstLayerPeelingData.of_firstLayerValueMatchingData
    (D := { sigma := (Step1.step1CommonFirstGates hr H).sigma, values_matched := hV })
    (Step1.step1CommonFirstGates hr H).attention_eq
    (Step1.step1CommonFirstGates hr H).attention_unique

/-- Assemble the K08 peeling package directly from the K07C `prop:first-V`
payload plus the proven K06C first-attention permutation. -/
noncomputable def firstLayerPeelingData_of_prop_first_V_S {m k d r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1.Step1StandingHypotheses r θ θ')
    (hV : prop_first_V_S (Nat.succ_pos m) θ θ')
    (hsigma : hV.sigma = (Step1.step1CommonFirstGates hr H).sigma) :
    FirstLayerPeelingData θ θ' :=
  firstLayerPeelingData_of_valuesMatched hr H <| by
    rw [← hsigma]
    exact firstLayerValuesMatchedForPeeling_of_firstLayerValuesMatched hV.values_matched

/-! ## Local openness and exact reduced-tail agreement -/

/-- First-layer instance of Definition `local-openness`. -/
def FirstLayerLocalOpenness {m k d : Nat} (r : Nat)
    (theta : Params (m + 1) k d) : Prop :=
  localOpennessDet r theta 0 ≠ 0

theorem firstLayerLocalOpenness_of_LocalOpenness {m k d r : Nat}
    {theta : Params (m + 1) k d} (hopen : LocalOpenness r theta) :
    FirstLayerLocalOpenness r theta :=
  hopen 0

/-- The project coordinate basis `matrixBasis` is mathlib's standard matrix
basis, with the same product index orientation. -/
theorem stdBasis_eq_matrixBasis {d T : Nat} (q : Fin d × Fin T) :
    (Matrix.stdBasis ℝ (Fin d) (Fin T)) q = matrixBasis q := by
  ext i j
  rcases q with ⟨qi, qj⟩
  simp [Matrix.stdBasis_eq_single, matrixBasis, Matrix.single, eq_comm]

/-- The flattened matrix used in `localOpennessDet` is the standard coordinate
matrix of the packaged linear derivative. -/
theorem localDerivative_toMatrix_eq_matrixOperatorMatrix {L k d r : Nat}
    (theta : Params L k d) (l : Fin L) :
    LinearMap.toMatrix (Matrix.stdBasis ℝ (Fin d) (Fin (seqLength r)))
      (Matrix.stdBasis ℝ (Fin d) (Fin (seqLength r)))
      (localDerivativeLinearMap r theta l) =
    matrixOperatorMatrix (localDerivative r theta l) := by
  ext p q
  rw [LinearMap.toMatrix_apply, stdBasis_eq_matrixBasis]
  simp [Matrix.stdBasis]

noncomputable def localDerivativeContinuousLinearMap {L k d : Nat} (r : Nat)
    (theta : Params L k d) (l : Fin L) :
    Matrix (Fin d) (Fin (seqLength r)) ℝ →L[ℝ]
      Matrix (Fin d) (Fin (seqLength r)) ℝ :=
  LinearMap.toContinuousLinearMap (localDerivativeLinearMap r theta l)

@[simp]
theorem localDerivativeContinuousLinearMap_apply {L k d r : Nat}
    (theta : Params L k d) (l : Fin L)
    (H : Matrix (Fin d) (Fin (seqLength r)) ℝ) :
    localDerivativeContinuousLinearMap r theta l H = localDerivative r theta l H := by
  simp [localDerivativeContinuousLinearMap]

/-- Determinant nonvanishing in Definition `local-openness` turns the declared
local derivative into a continuous linear equivalence. -/
noncomputable def localDerivativeContinuousLinearEquivOfDetNeZero
    {L k d r : Nat} (theta : Params L k d) (l : Fin L)
    (hdet : localOpennessDet r theta l ≠ 0) :
    Matrix (Fin d) (Fin (seqLength r)) ℝ ≃L[ℝ]
      Matrix (Fin d) (Fin (seqLength r)) ℝ := by
  let b := Matrix.stdBasis ℝ (Fin d) (Fin (seqLength r))
  have hunit :
      IsUnit (LinearMap.toMatrix b b (localDerivativeLinearMap r theta l)).det := by
    rw [localDerivative_toMatrix_eq_matrixOperatorMatrix]
    exact isUnit_iff_ne_zero.mpr hdet
  exact (LinearEquiv.ofIsUnitDet
    (f := localDerivativeLinearMap r theta l) (v := b) (v' := b) hunit).toContinuousLinearEquiv

@[simp]
theorem localDerivativeContinuousLinearEquivOfDetNeZero_apply
    {L k d r : Nat} (theta : Params L k d) (l : Fin L)
    (hdet : localOpennessDet r theta l ≠ 0)
    (H : Matrix (Fin d) (Fin (seqLength r)) ℝ) :
    localDerivativeContinuousLinearEquivOfDetNeZero theta l hdet H =
      localDerivative r theta l H := by
  simp [localDerivativeContinuousLinearEquivOfDetNeZero]

/-- Local-openness gives a continuous linear equivalence for every layer's
declared local derivative. -/
noncomputable def localDerivativeContinuousLinearEquivOfLocalOpenness
    {L k d r : Nat} (theta : Params L k d) (hopen : LocalOpenness r theta)
    (l : Fin L) :
    Matrix (Fin d) (Fin (seqLength r)) ℝ ≃L[ℝ]
      Matrix (Fin d) (Fin (seqLength r)) ℝ :=
  localDerivativeContinuousLinearEquivOfDetNeZero theta l (hopen l)

/-- First-layer local openness gives the continuous linear equivalence for the
first layer's declared local derivative. -/
noncomputable def firstLayerLocalDerivativeContinuousLinearEquiv
    {m k d r : Nat} (theta : Params (m + 1) k d)
    (hopen : FirstLayerLocalOpenness r theta) :
    Matrix (Fin d) (Fin (seqLength r)) ℝ ≃L[ℝ]
      Matrix (Fin d) (Fin (seqLength r)) ℝ :=
  localDerivativeContinuousLinearEquivOfDetNeZero theta 0 hopen

@[simp]
theorem firstLayerLocalDerivativeContinuousLinearEquiv_apply
    {m k d r : Nat} (theta : Params (m + 1) k d)
    (hopen : FirstLayerLocalOpenness r theta)
    (H : Matrix (Fin d) (Fin (seqLength r)) ℝ) :
    firstLayerLocalDerivativeContinuousLinearEquiv theta hopen H =
      localDerivative r theta 0 H := by
  simp [firstLayerLocalDerivativeContinuousLinearEquiv]

@[simp]
theorem layer_zero_input {L k d T : Nat} (theta : Params L k d) (l : Fin L) :
    layer theta l (0 : Matrix (Fin d) (Fin T) ℝ) = 0 := by
  simp [layer]

section FirstLayerAnalyticity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}

private theorem peeling_analyticOnNhd_matrix_coord {n m : Nat}
    {F : E → Matrix (Fin n) (Fin m) ℝ}
    (hF : AnalyticOnNhd ℝ F U) (i : Fin n) (j : Fin m) :
    AnalyticOnNhd ℝ (fun x : E => F x i j) U := by
  let Prow : Matrix (Fin n) (Fin m) ℝ →L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearMap.proj i
  let Pcoord : (Fin m → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj j
  simpa [Prow, Pcoord, Function.comp] using
    (Pcoord.comp Prow).comp_analyticOnNhd hF

private theorem peeling_analyticOnNhd_matrix_of_coords {n m : Nat}
    {F : E → Matrix (Fin n) (Fin m) ℝ}
    (hF : ∀ i : Fin n, ∀ j : Fin m,
      AnalyticOnNhd ℝ (fun x : E => F x i j) U) :
    AnalyticOnNhd ℝ F U := by
  let Mof : (Fin n → Fin m → ℝ) →L[ℝ] Matrix (Fin n) (Fin m) ℝ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.ofLinearEquiv ℝ : (Fin n → Fin m → ℝ) ≃ₗ[ℝ]
        Matrix (Fin n) (Fin m) ℝ).toLinearMap)
  have hPi :
      AnalyticOnNhd ℝ
        (fun x : E => fun i : Fin n => fun j : Fin m => F x i j) U := by
    apply AnalyticOnNhd.pi
    intro i
    apply AnalyticOnNhd.pi
    intro j
    exact hF i j
  simpa [Mof, Function.comp] using Mof.comp_analyticOnNhd hPi

private theorem peeling_analyticOnNhd_matrix_transpose_coord {n m : Nat}
    {F : E → Matrix (Fin n) (Fin m) ℝ}
    (hF : ∀ i : Fin n, ∀ j : Fin m,
      AnalyticOnNhd ℝ (fun x : E => F x i j) U)
    (i : Fin m) (j : Fin n) :
    AnalyticOnNhd ℝ (fun x : E => (F x)ᵀ i j) U := by
  simpa [Matrix.transpose_apply] using hF j i

private theorem peeling_analyticOnNhd_matrix_mul_coord {n m p : Nat}
    {F : E → Matrix (Fin n) (Fin m) ℝ}
    {G : E → Matrix (Fin m) (Fin p) ℝ}
    (hF : ∀ i : Fin n, ∀ j : Fin m,
      AnalyticOnNhd ℝ (fun x : E => F x i j) U)
    (hG : ∀ i : Fin m, ∀ j : Fin p,
      AnalyticOnNhd ℝ (fun x : E => G x i j) U)
    (i : Fin n) (k : Fin p) :
    AnalyticOnNhd ℝ (fun x : E => (F x * G x) i k) U := by
  simp only [Matrix.mul_apply]
  apply Finset.analyticOnNhd_fun_sum
  intro j _hj
  exact (hF i j).mul (hG j k)

private theorem peeling_softmaxColC_coord_analyticOnNhd {T : Nat}
    {F : E → Matrix (Fin T) (Fin T) ℝ}
    (hF : ∀ i : Fin T, ∀ j : Fin T,
      AnalyticOnNhd ℝ (fun x : E => F x i j) U)
    (i j : Fin T) :
    AnalyticOnNhd ℝ (fun x : E => softmaxColC (F x) i j) U := by
  by_cases hij : i ≤ j
  · have hnum :
        AnalyticOnNhd ℝ (fun x : E => Real.exp (F x i j)) U :=
      (hF i j).rexp
    have hden :
        AnalyticOnNhd ℝ
          (fun x : E => ∑ i' ∈ Finset.Iic j, Real.exp (F x i' j)) U := by
      apply Finset.analyticOnNhd_fun_sum
      intro i' _hi'
      exact (hF i' j).rexp
    have hden_ne :
        ∀ x ∈ U, (∑ i' ∈ Finset.Iic j, Real.exp (F x i' j)) ≠ 0 := by
      intro x _hx
      have hpos : 0 < ∑ i' ∈ Finset.Iic j, Real.exp (F x i' j) := by
        exact Finset.sum_pos
          (by
            intro i' _hi'
            exact Real.exp_pos (F x i' j))
          ⟨j, Finset.mem_Iic.2 le_rfl⟩
      exact ne_of_gt hpos
    simpa [softmaxColC, TransformerIdentifiability.NLayer.causalSoftmax, hij] using
      hnum.div hden hden_ne
  · simpa [softmaxColC, TransformerIdentifiability.NLayer.causalSoftmax, hij] using
      (analyticOnNhd_const (𝕜 := ℝ) (v := (0 : ℝ)) (s := U))

private theorem peeling_layer_coord_analyticOnNhd_id {m k d r : Nat}
    (theta : Params (m + 1) k d) (i : Fin d) (j : Fin (seqLength r)) :
    AnalyticOnNhd ℝ
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X i j)
      Set.univ := by
  have hId : AnalyticOnNhd ℝ
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => X) Set.univ :=
    (ContinuousLinearMap.id ℝ
      (Matrix (Fin d) (Fin (seqLength r)) ℝ)).analyticOnNhd Set.univ
  have hX : ∀ i : Fin d, ∀ j : Fin (seqLength r),
      AnalyticOnNhd ℝ
        (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => X i j) Set.univ := by
    intro i j
    exact peeling_analyticOnNhd_matrix_coord hId i j
  have hsum :
      AnalyticOnNhd ℝ
        (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
          (∑ a : Fin k,
            valueMatrix theta 0 a * X *
              softmaxColC (Xᵀ * attentionMatrix theta 0 a * X)) i j) Set.univ := by
    simpa [Matrix.sum_apply] using
      (Finset.analyticOnNhd_fun_sum (N := Finset.univ) (s := Set.univ)
        (f := fun a : Fin k => fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
          (valueMatrix theta 0 a * X *
            softmaxColC (Xᵀ * attentionMatrix theta 0 a * X)) i j)
        (by
          intro a _ha
          have hV :
              ∀ i' : Fin d, ∀ j' : Fin d,
                AnalyticOnNhd ℝ
                  (fun _X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
                    valueMatrix theta 0 a i' j') Set.univ := by
            intro i' j'
            exact analyticOnNhd_const (𝕜 := ℝ)
              (v := valueMatrix theta 0 a i' j') (s := Set.univ)
          have hA :
              ∀ i' : Fin d, ∀ j' : Fin d,
                AnalyticOnNhd ℝ
                  (fun _X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
                    attentionMatrix theta 0 a i' j') Set.univ := by
            intro i' j'
            exact analyticOnNhd_const (𝕜 := ℝ)
              (v := attentionMatrix theta 0 a i' j') (s := Set.univ)
          have hXT :
              ∀ i' : Fin (seqLength r), ∀ j' : Fin d,
                AnalyticOnNhd ℝ
                  (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
                    Xᵀ i' j') Set.univ := by
            intro i' j'
            exact peeling_analyticOnNhd_matrix_transpose_coord hX i' j'
          have hleft :
              ∀ i' : Fin (seqLength r), ∀ j' : Fin d,
                AnalyticOnNhd ℝ
                  (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
                    (Xᵀ * attentionMatrix theta 0 a) i' j') Set.univ := by
            intro i' j'
            exact peeling_analyticOnNhd_matrix_mul_coord hXT hA i' j'
          have hscore :
              ∀ i' : Fin (seqLength r), ∀ j' : Fin (seqLength r),
                AnalyticOnNhd ℝ
                  (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
                    (Xᵀ * attentionMatrix theta 0 a * X) i' j') Set.univ := by
            intro i' j'
            exact peeling_analyticOnNhd_matrix_mul_coord hleft hX i' j'
          have hsoft :
              ∀ i' : Fin (seqLength r), ∀ j' : Fin (seqLength r),
                AnalyticOnNhd ℝ
                  (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
                    softmaxColC (Xᵀ * attentionMatrix theta 0 a * X) i' j')
                  Set.univ := by
            intro i' j'
            exact peeling_softmaxColC_coord_analyticOnNhd hscore i' j'
          have hVX :
              ∀ i' : Fin d, ∀ j' : Fin (seqLength r),
                AnalyticOnNhd ℝ
                  (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
                    (valueMatrix theta 0 a * X) i' j') Set.univ := by
            intro i' j'
            exact peeling_analyticOnNhd_matrix_mul_coord hV hX i' j'
          exact peeling_analyticOnNhd_matrix_mul_coord hVX hsoft i j))
  refine AnalyticOnNhd.congr isOpen_univ ((hX i j).add hsum) ?_
  intro X _hX
  simp [layer, Matrix.add_apply]

theorem firstLayer_layer_analyticAt {m k d r : Nat}
    (theta : Params (m + 1) k d) :
    AnalyticAt ℝ
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X)
      0 := by
  have hOn : AnalyticOnNhd ℝ
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X)
      Set.univ := by
    apply peeling_analyticOnNhd_matrix_of_coords
    intro i j
    exact peeling_layer_coord_analyticOnNhd_id theta i j
  exact hOn 0 (Set.mem_univ _)

end FirstLayerAnalyticity

/-- The causal column-softmax is continuous as a matrix-valued map. -/
theorem continuous_softmaxColC {T : Nat} :
    Continuous (softmaxColC : Matrix (Fin T) (Fin T) ℝ →
      Matrix (Fin T) (Fin T) ℝ) := by
  refine continuous_matrix ?_
  intro i j
  by_cases hij : i ≤ j
  · have hnum :
        Continuous fun M : Matrix (Fin T) (Fin T) ℝ => Real.exp (M i j) :=
      Real.continuous_exp.comp ((continuous_id : Continuous
        (fun M : Matrix (Fin T) (Fin T) ℝ => M)).matrix_elem i j)
    have hden :
        Continuous fun M : Matrix (Fin T) (Fin T) ℝ =>
          ∑ i' ∈ Finset.Iic j, Real.exp (M i' j) := by
      apply continuous_finsetSum
      intro i' _hi'
      exact Real.continuous_exp.comp ((continuous_id : Continuous
        (fun M : Matrix (Fin T) (Fin T) ℝ => M)).matrix_elem i' j)
    have hden_ne :
        ∀ M : Matrix (Fin T) (Fin T) ℝ,
          (∑ i' ∈ Finset.Iic j, Real.exp (M i' j)) ≠ 0 := by
      intro M
      have hpos : 0 < ∑ i' ∈ Finset.Iic j, Real.exp (M i' j) := by
        exact Finset.sum_pos
          (by
            intro i' _hi'
            exact Real.exp_pos (M i' j))
          ⟨j, Finset.mem_Iic.2 le_rfl⟩
      exact ne_of_gt hpos
    simpa [softmaxColC, TransformerIdentifiability.NLayer.causalSoftmax, hij] using
      hnum.div hden hden_ne
  · simpa [softmaxColC, TransformerIdentifiability.NLayer.causalSoftmax, hij] using
      (continuous_const : Continuous fun _M : Matrix (Fin T) (Fin T) ℝ => (0 : ℝ))

/-- The quadratic attention-score map is continuous. -/
theorem continuous_quadraticScore {d T : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) :
    Continuous fun X : Matrix (Fin d) (Fin T) ℝ => Xᵀ * A * X := by
  exact Continuous.matrix_mul
    (Continuous.matrix_mul
      ((continuous_id : Continuous fun X : Matrix (Fin d) (Fin T) ℝ => X).matrix_transpose)
      continuous_const)
    continuous_id

/-- Along a quadratic score, the softmax remainder tends to zero at zero input. -/
theorem softmax_quadraticScore_sub_gammaZero_tendsto_zero {d r : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) :
    Tendsto
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
        softmaxColC (Xᵀ * A * X) - gammaZero r)
      (nhds 0) (nhds 0) := by
  have hsoft :
      Tendsto
        (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
          softmaxColC (Xᵀ * A * X))
        (nhds 0) (nhds (gammaZero r)) := by
    have hcont :
        Continuous fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
          softmaxColC (Xᵀ * A * X) :=
      continuous_softmaxColC.comp (continuous_quadraticScore A)
    have hcont0 :
        ContinuousAt
          (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
            softmaxColC (Xᵀ * A * X))
          0 :=
      hcont.continuousAt
    simpa [gammaZero] using hcont0.tendsto
  exact tendsto_sub_nhds_zero_iff.mpr hsoft

/-- If the right factor tends to zero, then `X * G X` is `o(X)` at zero.

This is the Frobenius-norm matrix-product estimate needed for the first-layer
softmax remainder. -/
theorem matrix_mul_tendsto_zero_right_isLittleO {d T : Nat}
    {G : Matrix (Fin d) (Fin T) ℝ → Matrix (Fin T) (Fin T) ℝ}
    (hG : Tendsto G (nhds (0 : Matrix (Fin d) (Fin T) ℝ))
      (nhds (0 : Matrix (Fin T) (Fin T) ℝ))) :
    (fun X : Matrix (Fin d) (Fin T) ℝ => X * G X)
      =o[nhds (0 : Matrix (Fin d) (Fin T) ℝ)]
        fun X : Matrix (Fin d) (Fin T) ℝ => X := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hnorm :
      Tendsto (fun X : Matrix (Fin d) (Fin T) ℝ => ‖G X‖)
        (nhds (0 : Matrix (Fin d) (Fin T) ℝ)) (nhds (0 : ℝ)) :=
    by simpa using hG.norm
  have hsmall : {y : ℝ | y < c} ∈ nhds (0 : ℝ) := Iio_mem_nhds hc
  filter_upwards [hnorm hsmall] with X hX
  calc
    ‖X * G X‖ ≤ ‖X‖ * ‖G X‖ := Matrix.frobenius_norm_mul X (G X)
    _ ≤ ‖X‖ * c := mul_le_mul_of_nonneg_left (le_of_lt hX) (norm_nonneg X)
    _ = c * ‖X‖ := mul_comm _ _

/-- A fixed left matrix does not change the `o(X)` estimate for `X * G X`. -/
theorem matrix_const_mul_mul_tendsto_zero_right_isLittleO {d T : Nat}
    (V : Matrix (Fin d) (Fin d) ℝ)
    {G : Matrix (Fin d) (Fin T) ℝ → Matrix (Fin T) (Fin T) ℝ}
    (hG : Tendsto G (nhds (0 : Matrix (Fin d) (Fin T) ℝ))
      (nhds (0 : Matrix (Fin T) (Fin T) ℝ))) :
    (fun X : Matrix (Fin d) (Fin T) ℝ => V * X * G X)
      =o[nhds (0 : Matrix (Fin d) (Fin T) ℝ)]
        fun X : Matrix (Fin d) (Fin T) ℝ => X := by
  have hleft :
      (fun X : Matrix (Fin d) (Fin T) ℝ => V * (X * G X))
        =O[nhds (0 : Matrix (Fin d) (Fin T) ℝ)]
          fun X : Matrix (Fin d) (Fin T) ℝ => X * G X := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨‖V‖, Eventually.of_forall ?_⟩
    intro X
    exact Matrix.frobenius_norm_mul V (X * G X)
  have hprod := matrix_mul_tendsto_zero_right_isLittleO (d := d) (T := T) hG
  simpa [Matrix.mul_assoc] using hleft.trans_isLittleO hprod

/-- Algebraic remainder after subtracting the first-layer declared derivative at zero. -/
theorem firstLayer_layer_sub_localDerivative_eq_softmax_remainder {m k d r : Nat}
    (theta : Params (m + 1) k d)
    (X : Matrix (Fin d) (Fin (seqLength r)) ℝ) :
    layer theta 0 X - localDerivative r theta 0 X =
      ∑ a : Fin k,
        valueMatrix theta 0 a * X *
          (softmaxColC (Xᵀ * attentionMatrix theta 0 a * X) - gammaZero r) := by
  simp only [layer, localDerivative]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← Matrix.mul_sub]

/-- The same remainder identity with the determinant-built first-layer equivalence.
This is the concrete linearization supplied by `firstLayerLocalDerivativeContinuousLinearEquiv`. -/
theorem firstLayer_layer_sub_localDerivativeEquiv_eq_softmax_remainder {m k d r : Nat}
    (theta : Params (m + 1) k d) (hopen : FirstLayerLocalOpenness r theta)
    (X : Matrix (Fin d) (Fin (seqLength r)) ℝ) :
    layer theta 0 X - firstLayerLocalDerivativeContinuousLinearEquiv theta hopen X =
      ∑ a : Fin k,
        valueMatrix theta 0 a * X *
          (softmaxColC (Xᵀ * attentionMatrix theta 0 a * X) - gammaZero r) := by
  rw [firstLayerLocalDerivativeContinuousLinearEquiv_apply,
    firstLayer_layer_sub_localDerivative_eq_softmax_remainder]

/-- One head's first-layer softmax remainder is `o(X)` at zero. -/
theorem firstLayer_one_head_softmax_remainder_isLittleO {m k d r : Nat}
    (theta : Params (m + 1) k d) (a : Fin k) :
    (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
      valueMatrix theta 0 a * X *
        (softmaxColC (Xᵀ * attentionMatrix theta 0 a * X) - gammaZero r))
      =o[nhds (0 : Matrix (Fin d) (Fin (seqLength r)) ℝ)]
        fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => X := by
  exact matrix_const_mul_mul_tendsto_zero_right_isLittleO
    (valueMatrix theta 0 a)
    (softmax_quadraticScore_sub_gammaZero_tendsto_zero
      (attentionMatrix theta 0 a))

/-- The complete first-layer softmax remainder sum is `o(X)` at zero. -/
theorem firstLayer_softmax_remainder_sum_isLittleO {m k d r : Nat}
    (theta : Params (m + 1) k d) :
    (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
      ∑ a : Fin k,
        valueMatrix theta 0 a * X *
          (softmaxColC (Xᵀ * attentionMatrix theta 0 a * X) - gammaZero r))
      =o[nhds (0 : Matrix (Fin d) (Fin (seqLength r)) ℝ)]
        fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => X := by
  simpa using
    (Asymptotics.IsLittleO.sum (s := Finset.univ)
      (A := fun a : Fin k => fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
        valueMatrix theta 0 a * X *
          (softmaxColC (Xᵀ * attentionMatrix theta 0 a * X) - gammaZero r))
      (g' := fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => X)
      (l := nhds (0 : Matrix (Fin d) (Fin (seqLength r)) ℝ))
      (by
        intro a _ha
        exact firstLayer_one_head_softmax_remainder_isLittleO theta a))

/-- The first-layer algebraic remainder after subtracting the declared local
derivative is `o(X)` at zero. -/
theorem firstLayer_layer_sub_localDerivative_isLittleO_at_zero {m k d r : Nat}
    (theta : Params (m + 1) k d) :
    (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
      layer theta 0 X - localDerivative r theta 0 X)
      =o[nhds (0 : Matrix (Fin d) (Fin (seqLength r)) ℝ)]
        fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => X := by
  exact (firstLayer_softmax_remainder_sum_isLittleO theta).congr_left
    fun X => (firstLayer_layer_sub_localDerivative_eq_softmax_remainder theta X).symm

theorem firstLayer_hasFDerivAt_localDerivativeContinuousLinearMap {m k d r : Nat}
    {theta : Params (m + 1) k d} :
    HasFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X)
      (localDerivativeContinuousLinearMap r theta 0)
      0 := by
  apply HasFDerivAt.of_isLittleO
  simpa [layer_zero_input] using
    firstLayer_layer_sub_localDerivative_isLittleO_at_zero (r := r) theta

/-- The one-point Frechet derivative at zero supplied by the softmax remainder
estimate.  The strict two-point derivative needed by the inverse-function theorem
is proved below from analyticity. -/
theorem firstLayer_hasFDerivAt_localDerivative {m k d r : Nat}
    {theta : Params (m + 1) k d}
    (hopen : FirstLayerLocalOpenness r theta) :
    HasFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X)
      (↑(firstLayerLocalDerivativeContinuousLinearEquiv theta hopen) :
        Matrix (Fin d) (Fin (seqLength r)) ℝ →L[ℝ]
          Matrix (Fin d) (Fin (seqLength r)) ℝ)
      0 := by
  apply HasFDerivAt.of_isLittleO
  simpa [layer_zero_input, firstLayerLocalDerivativeContinuousLinearEquiv_apply] using
    firstLayer_layer_sub_localDerivative_isLittleO_at_zero (r := r) theta

/-- Strict derivative endpoint reduced to the concrete two-point little-o remainder
for the declared local derivative.  The determinant bridge changes that declared
linear map into the continuous linear equivalence required by the inverse-function
step. -/
theorem firstLayer_hasStrictFDerivAt_of_localDerivative_strictRemainder
    {m k d r : Nat} {theta : Params (m + 1) k d}
    (hopen : FirstLayerLocalOpenness r theta)
    (hsmall :
      ((fun P : Matrix (Fin d) (Fin (seqLength r)) ℝ ×
          Matrix (Fin d) (Fin (seqLength r)) ℝ =>
          layer theta 0 P.1 - layer theta 0 P.2 -
            localDerivative r theta 0 (P.1 - P.2))
        =o[nhds ((0, 0) : Matrix (Fin d) (Fin (seqLength r)) ℝ ×
          Matrix (Fin d) (Fin (seqLength r)) ℝ)]
        fun P => P.1 - P.2)) :
    HasStrictFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X)
      (↑(firstLayerLocalDerivativeContinuousLinearEquiv theta hopen) :
        Matrix (Fin d) (Fin (seqLength r)) ℝ →L[ℝ]
          Matrix (Fin d) (Fin (seqLength r)) ℝ)
      0 := by
  apply HasStrictFDerivAt.of_isLittleO
  simpa only [firstLayerLocalDerivativeContinuousLinearEquiv_apply] using hsmall

theorem firstLayer_hasStrictFDerivAt_localDerivativeContinuousLinearMap {m k d r : Nat}
    {theta : Params (m + 1) k d} :
    HasStrictFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X)
      (localDerivativeContinuousLinearMap r theta 0)
      0 := by
  have hstrict := (firstLayer_layer_analyticAt (r := r) theta).hasStrictFDerivAt
  exact hstrict.congr_fderiv
    (firstLayer_hasFDerivAt_localDerivativeContinuousLinearMap
      (r := r) (theta := theta)).fderiv

theorem firstLayer_layer_sub_localDerivative_strictRemainder {m k d r : Nat}
    (theta : Params (m + 1) k d) :
    ((fun P : Matrix (Fin d) (Fin (seqLength r)) ℝ ×
        Matrix (Fin d) (Fin (seqLength r)) ℝ =>
        layer theta 0 P.1 - layer theta 0 P.2 -
          localDerivative r theta 0 (P.1 - P.2))
      =o[nhds ((0, 0) : Matrix (Fin d) (Fin (seqLength r)) ℝ ×
        Matrix (Fin d) (Fin (seqLength r)) ℝ)]
      fun P => P.1 - P.2) := by
  exact
    (firstLayer_hasStrictFDerivAt_localDerivativeContinuousLinearMap
      (r := r) (theta := theta)).isLittleO.congr_left
      (by
        intro P
        exact congrArg
          (fun Z : Matrix (Fin d) (Fin (seqLength r)) ℝ =>
            layer theta 0 P.1 - layer theta 0 P.2 - Z)
          (localDerivativeContinuousLinearMap_apply
            (r := r) theta (0 : Fin (m + 1)) (P.1 - P.2)))

theorem firstLayer_hasStrictFDerivAt_localDerivative {m k d r : Nat}
    {theta : Params (m + 1) k d}
    (hopen : FirstLayerLocalOpenness r theta) :
    HasStrictFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X)
      (↑(firstLayerLocalDerivativeContinuousLinearEquiv theta hopen) :
        Matrix (Fin d) (Fin (seqLength r)) ℝ →L[ℝ]
          Matrix (Fin d) (Fin (seqLength r)) ℝ)
      0 :=
  firstLayer_hasStrictFDerivAt_of_localDerivative_strictRemainder
    hopen (firstLayer_layer_sub_localDerivative_strictRemainder theta)

/-- Image package supplied by local openness of the common first layer. -/
structure LocalOpenLayerImage {m k d : Nat} (r : Nat)
    (theta : Params (m + 1) k d) where
  domain : Set (Matrix (Fin d) (Fin (seqLength r)) ℝ)
  imageSet : Set (Matrix (Fin d) (Fin (seqLength r)) ℝ)
  domain_open : IsOpen domain
  zero_mem_domain : (0 : Matrix (Fin d) (Fin (seqLength r)) ℝ) ∈ domain
  image_open : IsOpen imageSet
  image_nonempty : imageSet.Nonempty
  image_subset :
    imageSet ⊆
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X) '' domain

/-- `lem-local-open-layer.S`: local openness of a generic first layer. -/
def lem_local_open_layer_S {m k d : Nat} (r : Nat)
    (theta : Params (m + 1) k d) : Prop :=
  FirstLayerLocalOpenness r theta -> Nonempty (LocalOpenLayerImage r theta)

/-- The inverse-function-theorem core of `lem-local-open-layer.S`: once the
first layer has an invertible strict derivative at zero, its image contains a
nonempty open set.  The determinant-to-derivative endpoint is supplied
separately by the `LocalOpenness` API. -/
theorem localOpenLayerImage_of_hasStrictFDerivAt_equiv {m k d r : Nat}
    {theta : Params (m + 1) k d}
    (E : Matrix (Fin d) (Fin (seqLength r)) ℝ ≃L[ℝ]
      Matrix (Fin d) (Fin (seqLength r)) ℝ)
    (hderiv : HasStrictFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X)
      (↑E : Matrix (Fin d) (Fin (seqLength r)) ℝ →L[ℝ]
        Matrix (Fin d) (Fin (seqLength r)) ℝ)
      0) :
    Nonempty (LocalOpenLayerImage r theta) := by
  let f : Matrix (Fin d) (Fin (seqLength r)) ℝ →
      Matrix (Fin d) (Fin (seqLength r)) ℝ :=
    fun X => layer theta 0 X
  let inv : Matrix (Fin d) (Fin (seqLength r)) ℝ →
      Matrix (Fin d) (Fin (seqLength r)) ℝ :=
    hderiv.localInverse
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X) E 0
  have hright : ∀ᶠ Y in nhds (f 0), f (inv Y) = Y := by
    simpa [f, inv] using hderiv.eventually_right_inverse
  rw [Filter.eventually_iff, mem_nhds_iff] at hright
  obtain ⟨Omega, hOmega_subset, hOmega_open, hOmega_mem⟩ := hright
  refine ⟨{
    domain := Set.univ
    imageSet := Omega
    domain_open := isOpen_univ
    zero_mem_domain := Set.mem_univ _
    image_open := hOmega_open
    image_nonempty := ⟨f 0, hOmega_mem⟩
    image_subset := ?_
  }⟩
  intro Y hY
  exact ⟨inv Y, Set.mem_univ _, hOmega_subset hY⟩

/-- Once the first-layer derivative is identified with the local-openness
linear operator, the determinant bridge above supplies the inverse-function
theorem equivalence. -/
theorem localOpenLayerImage_of_firstLayerLocalOpenness_and_hasStrictFDerivAt_localDerivative
    {m k d r : Nat} {theta : Params (m + 1) k d}
    (hopen : FirstLayerLocalOpenness r theta)
    (hderiv : HasStrictFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X)
      (↑(firstLayerLocalDerivativeContinuousLinearEquiv theta hopen) :
        Matrix (Fin d) (Fin (seqLength r)) ℝ →L[ℝ]
          Matrix (Fin d) (Fin (seqLength r)) ℝ)
      0) :
    Nonempty (LocalOpenLayerImage r theta) :=
  localOpenLayerImage_of_hasStrictFDerivAt_equiv
    (firstLayerLocalDerivativeContinuousLinearEquiv theta hopen) hderiv

/-- Conditional proof of `lem-local-open-layer.S` from the remaining concrete
first-layer derivative computation. -/
theorem lem_local_open_layer_of_hasStrictFDerivAt_localDerivative {m k d r : Nat}
    {theta : Params (m + 1) k d}
    (hderiv :
      ∀ hopen : FirstLayerLocalOpenness r theta,
        HasStrictFDerivAt
          (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X)
          (↑(firstLayerLocalDerivativeContinuousLinearEquiv theta hopen) :
            Matrix (Fin d) (Fin (seqLength r)) ℝ →L[ℝ]
              Matrix (Fin d) (Fin (seqLength r)) ℝ)
          0) :
    lem_local_open_layer_S r theta := by
  intro hopen
  exact localOpenLayerImage_of_firstLayerLocalOpenness_and_hasStrictFDerivAt_localDerivative
    hopen (hderiv hopen)

theorem lem_local_open_layer {m k d r : Nat}
    {theta : Params (m + 1) k d} :
    lem_local_open_layer_S r theta :=
  lem_local_open_layer_of_hasStrictFDerivAt_localDerivative
    (fun hopen => firstLayer_hasStrictFDerivAt_localDerivative hopen)

/-- Conditional proof of `lem-local-open-layer.S` from the inverse-function
theorem endpoint for the first layer. -/
theorem lem_local_open_layer_of_hasStrictFDerivAt_equiv {m k d r : Nat}
    {theta : Params (m + 1) k d}
    (E : Matrix (Fin d) (Fin (seqLength r)) ℝ ≃L[ℝ]
      Matrix (Fin d) (Fin (seqLength r)) ℝ)
    (hderiv : HasStrictFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X)
      (↑E : Matrix (Fin d) (Fin (seqLength r)) ℝ →L[ℝ]
        Matrix (Fin d) (Fin (seqLength r)) ℝ)
      0) :
    lem_local_open_layer_S r theta := by
  intro _hopen
  exact localOpenLayerImage_of_hasStrictFDerivAt_equiv E hderiv

/-- Local-openness plus the strict-derivative endpoint gives the open first-layer
image package used by Step 3. -/
theorem localOpenLayerImage_of_LocalOpenness_and_hasStrictFDerivAt_equiv
    {m k d r : Nat} {theta : Params (m + 1) k d}
    (hopen : LocalOpenness r theta)
    (E : Matrix (Fin d) (Fin (seqLength r)) ℝ ≃L[ℝ]
      Matrix (Fin d) (Fin (seqLength r)) ℝ)
    (hderiv : HasStrictFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) ℝ => layer theta 0 X)
      (↑E : Matrix (Fin d) (Fin (seqLength r)) ℝ →L[ℝ]
        Matrix (Fin d) (Fin (seqLength r)) ℝ)
      0) :
    Nonempty (LocalOpenLayerImage r theta) :=
  (lem_local_open_layer_of_hasStrictFDerivAt_equiv E hderiv)
    (firstLayerLocalOpenness_of_LocalOpenness hopen)

/-- Exact reduced agreement after first-layer matching and local openness. -/
structure ReducedTailAgreementData {m k d : Nat} (r : Nat)
    (theta theta' : Params (m + 1) k d) where
  peeling : FirstLayerPeelingData theta theta'
  OmegaTail : Set (Matrix (Fin d) (Fin (seqLength r)) ℝ)
  omegaTail_open : IsOpen OmegaTail
  omegaTail_nonempty : OmegaTail.Nonempty
  tail_eq_on :
    TransformerAgreementOn
      (tailParams (relabelFirstLayer theta peeling.sigma))
      (tailParams theta') OmegaTail

namespace ReducedTailAgreementData

variable {m k d r : Nat}
variable {theta theta' : Params (m + 1) k d}

/-- The reduced comparison is equivalently between the unrelabelled source tail
and the target tail; no first-layer permutation acts on the target tail. -/
theorem tail_eq_on_unrelabelled
    (D : ReducedTailAgreementData r theta theta') :
    TransformerAgreementOn (tailParams theta) (tailParams theta') D.OmegaTail := by
  intro Y hY
  simpa [D.peeling.tail_relabel_eq] using D.tail_eq_on Y hY

/-- Package the exact reduced hypothesis as an open-set agreement for the tail. -/
def open_tail_agreement
    (D : ReducedTailAgreementData r theta theta') :
    OpenTransformerAgreement r (tailParams theta) (tailParams theta') D.OmegaTail where
  isOpen := D.omegaTail_open
  nonempty := D.omegaTail_nonempty
  eq_on := D.tail_eq_on_unrelabelled

end ReducedTailAgreementData

/-- A single peeling step returns the exact reduced-tail hypothesis and target-tail
genericity needed for the recursive call. -/
structure PeelingStepResult {m k d : Nat} (r : Nat)
    (theta theta' : Params (m + 1) k d) where
  reduced : ReducedTailAgreementData r theta theta'
  target_tail_generic : RecursiveGeneric r m k d (tailParams theta')

/-- Inputs used by the Step 3 peeling interface after Step 1 and Step 2 have run. -/
structure PeelingStepInputs {m k d : Nat} (r : Nat)
    (theta theta' : Params (m + 1) k d) where
  target_generic : RecursiveGeneric r (m + 1) k d theta'
  global_eq : TransformerAgreementEverywhere (T := seqLength r) theta theta'
  first_layer : FirstLayerPeelingData theta theta'
  local_open_layer : lem_local_open_layer_S r theta'

namespace PeelingStepInputs

variable {m k d r : Nat}
variable {theta theta' : Params (m + 1) k d}

/-- Recursive genericity supplies the target tail genericity used by peeling. -/
theorem target_tail_generic (I : PeelingStepInputs r theta theta') :
    RecursiveGeneric r m k d (tailParams theta') :=
  I.target_generic.1

/-- Recursive genericity also supplies the current first-layer generic clauses. -/
theorem current_generic (I : PeelingStepInputs r theta theta') :
    CurrentGenericClauses r theta' :=
  I.target_generic.2

/-- Current genericity supplies first-layer local openness. -/
theorem firstLayerLocalOpenness (I : PeelingStepInputs r theta theta') :
    FirstLayerLocalOpenness r theta' :=
  firstLayerLocalOpenness_of_LocalOpenness I.current_generic.2.1

/-- The local-open-layer lemma, together with recursive genericity, supplies the
nonempty open first-layer image package consumed by peeling. -/
theorem localOpenLayerImage (I : PeelingStepInputs r theta theta') :
    Nonempty (LocalOpenLayerImage r theta') :=
  I.local_open_layer I.firstLayerLocalOpenness

end PeelingStepInputs

/-- `C4`/Step 3 peeling statement, as a gated proposition interface. -/
def prop_peeling_step_S {m k d : Nat} (r : Nat)
    (theta theta' : Params (m + 1) k d) : Prop :=
  PeelingStepInputs r theta theta' ->
    Nonempty (PeelingStepResult r theta theta')

/-- Relabeling-invariance of the first layer under paired first-layer matching.

The first layer sums over *all* heads, so the paired matching `theta 0 (σ h) =
theta' 0 h` (permuting the source heads by `σ`) leaves the first-layer output
unchanged: reindexing the head sum by the permutation `σ` and substituting the
matched value and attention matrices turns the `theta` head sum into the `theta'`
head sum.  Hence the two first layers compute the *same* map. -/
theorem firstLayer_matched_layer_eq {m k d T : Nat}
    {theta theta' : Params (m + 1) k d}
    (D : FirstLayerPeelingData theta theta')
    (X : Matrix (Fin d) (Fin T) ℝ) :
    layer theta 0 X = layer theta' 0 X := by
  have hsum :
      (∑ a : Fin k, valueMatrix theta 0 a * X *
          softmaxColC (Xᵀ * attentionMatrix theta 0 a * X))
        = ∑ a : Fin k, valueMatrix theta' 0 a * X *
          softmaxColC (Xᵀ * attentionMatrix theta' 0 a * X) := by
    rw [← Equiv.sum_comp D.sigma
      (fun a => valueMatrix theta 0 a * X *
        softmaxColC (Xᵀ * attentionMatrix theta 0 a * X))]
    apply Finset.sum_congr rfl
    intro h _hh
    rw [D.value_matched h, D.attention_matched h]
  simp only [layer, hsum]

/-- **K08.M5 (`prop:peeling-step`, the real Step 3 peeling proof).**

Given `PeelingStepInputs`—which already carries the proven `FirstLayerPeelingData`
(Step 1 attention + Step 2 value matching) and the proven local-open-layer endpoint
`local_open_layer`—produce the exact reduced-tail agreement package.

The open tail image `OmegaTail` is the nonempty open first-layer image supplied by
`localOpenLayerImage` (from the target's local openness).  The reduced-tail equality
`tail_eq_on` is genuine transformer algebra:
* every `Y ∈ OmegaTail` is `Y = layer theta' 0 X` for some `X`;
* `firstLayer_matched_layer_eq` gives `layer theta 0 X = layer theta' 0 X`, so the
  two first layers agree at `X`;
* peeling `transformer` one layer (`transformer_succ`) and combining with the global
  equality `transformer theta X = transformer theta' X` yields
  `transformer (tailParams theta) Y = transformer (tailParams theta') Y`;
* `tailParams (relabelFirstLayer theta σ) = tailParams theta` (the relabeling never
  touches the source tail) rewrites this into the required reduced-tail statement. -/
theorem prop_peeling_step {m k d : Nat} (r : Nat)
    (theta theta' : Params (m + 1) k d) :
    prop_peeling_step_S r theta theta' := by
  intro I
  obtain ⟨img⟩ := I.localOpenLayerImage
  refine ⟨{
    reduced :=
      { peeling := I.first_layer
        OmegaTail := img.imageSet
        omegaTail_open := img.image_open
        omegaTail_nonempty := img.image_nonempty
        tail_eq_on := ?_ }
    target_tail_generic := I.target_tail_generic }⟩
  intro Y hY
  obtain ⟨X, _hXdom, rfl⟩ := img.image_subset hY
  rw [I.first_layer.tail_relabel_eq]
  have hkey : layer theta 0 X = layer theta' 0 X :=
    firstLayer_matched_layer_eq I.first_layer X
  have hglob : transformer theta X = transformer theta' X := I.global_eq X
  rw [transformer_succ, transformer_succ, hkey] at hglob
  exact hglob

/-! ## Layerwise paired conclusions and induction statements -/

/-- Paired layerwise target-to-source matching for all layers. -/
structure LayerwiseMatched {L k d : Nat}
    (theta theta' : Params L k d)
    (sigma : Fin L -> Equiv.Perm (Fin k)) : Prop where
  attention :
    ∀ l : Fin L, ∀ h : Fin k,
      attentionMatrix theta l ((sigma l) h) = attentionMatrix theta' l h
  value :
    ∀ l : Fin L, ∀ h : Fin k,
      valueMatrix theta l ((sigma l) h) = valueMatrix theta' l h

namespace LayerwiseMatched

variable {L k d : Nat}
variable {theta theta' : Params L k d}
variable {sigma : Fin L -> Equiv.Perm (Fin k)}

/-- Inverse/source-to-target convention for attention matrices. -/
theorem attention_source_index (M : LayerwiseMatched theta theta' sigma)
    (l : Fin L) (a : Fin k) :
    attentionMatrix theta l a =
      attentionMatrix theta' l ((sigma l).symm a) := by
  simpa using M.attention l ((sigma l).symm a)

/-- Inverse/source-to-target convention for value matrices. -/
theorem value_source_index (M : LayerwiseMatched theta theta' sigma)
    (l : Fin L) (a : Fin k) :
    valueMatrix theta l a =
      valueMatrix theta' l ((sigma l).symm a) := by
  simpa using M.value l ((sigma l).symm a)

/-- The paired permutation identifies complete head pairs. -/
theorem head_eq (M : LayerwiseMatched theta theta' sigma)
    (l : Fin L) (h : Fin k) :
    theta l ((sigma l) h) = theta' l h := by
  apply Prod.ext
  · exact M.value l h
  · exact M.attention l h

end LayerwiseMatched

-- `consLayerPerm` and its `_zero`/`_succ` simp lemmas now live in
-- `Induction/Relabel.lean` (imported above) so that this file and
-- `Induction/Invariant.lean` can be co-imported without a duplicate declaration.

/-- Assemble first-layer matching and tail matching into full layerwise matching. -/
theorem layerwiseMatched_cons {m k d : Nat}
    {theta theta' : Params (m + 1) k d}
    {sigma0 : Equiv.Perm (Fin k)}
    {tailSigma : Fin m -> Equiv.Perm (Fin k)}
    (hfirst : firstLayerHeadsMatched theta theta' sigma0)
    (htail : LayerwiseMatched (tailParams theta) (tailParams theta') tailSigma) :
    LayerwiseMatched theta theta' (consLayerPerm sigma0 tailSigma) := by
  refine ⟨?_, ?_⟩
  · intro l h
    cases l using Fin.cases with
    | zero =>
        exact (hfirst h).1
    | succ l =>
        simpa [tailParams] using htail.attention l h
  · intro l h
    cases l using Fin.cases with
    | zero =>
        exact (hfirst h).2
    | succ l =>
        simpa [tailParams] using htail.value l h

/-- Restrict a full layerwise matching tuple to the tail. -/
theorem LayerwiseMatched.tail {m k d : Nat}
    {theta theta' : Params (m + 1) k d}
    {sigma : Fin (m + 1) -> Equiv.Perm (Fin k)}
    (M : LayerwiseMatched theta theta' sigma) :
    LayerwiseMatched (tailParams theta) (tailParams theta')
      (fun l : Fin m => sigma l.succ) := by
  refine ⟨?_, ?_⟩
  · intro l h
    simpa [tailParams] using M.attention l.succ h
  · intro l h
    simpa [tailParams] using M.value l.succ h

/-- The first layer of a full matching is a paired first-layer match. -/
theorem LayerwiseMatched.first {m k d : Nat}
    {theta theta' : Params (m + 1) k d}
    {sigma : Fin (m + 1) -> Equiv.Perm (Fin k)}
    (M : LayerwiseMatched theta theta' sigma) :
    firstLayerHeadsMatched theta theta' (sigma 0) := by
  intro h
  exact ⟨M.attention 0 h, M.value 0 h⟩

/-- Result shape of Theorem `thm:open-induction-invariant`. -/
structure OpenInductionInvariantResult {m k d : Nat} (r : Nat)
    (theta theta' : Params (m + 1) k d) where
  global_eq : TransformerAgreementEverywhere (T := seqLength r) theta theta'
  sigma : Fin (m + 1) -> Equiv.Perm (Fin k)
  matched : LayerwiseMatched theta theta' sigma
  unique :
    ∀ tau : Fin (m + 1) -> Equiv.Perm (Fin k),
      LayerwiseMatched theta theta' tau -> tau = sigma
  reduced_tail :
    0 < m -> ReducedTailAgreementData r theta theta'
  reduced_tail_first_sigma :
    ∀ hm : 0 < m, (reduced_tail hm).peeling.sigma = sigma 0

/-- Hypothesis package of Theorem `thm:open-induction-invariant`. -/
structure OpenInductionInvariantInputs {m k d : Nat} (r : Nat)
    (theta theta' : Params (m + 1) k d)
    (Omega : Set (Matrix (Fin d) (Fin (seqLength r)) ℝ)) : Prop where
  k_pos : 0 < k
  r_ge_two : 2 ≤ r
  dimension_bound : dStar (m + 1) k ≤ d
  target_generic : RecursiveGeneric r (m + 1) k d theta'
  agreement : OpenTransformerAgreement r theta theta' Omega

-- Note: the `thm-open-induction-invariant.S` statement surface is not restated
-- here.  A same-named (differently-typed) statement surface already lives in
-- `Induction/Invariant.lean` as
-- `TransformerIdentifiability.NLayer.KHead.thm_open_induction_invariant_S`; this
-- file's copy collided with it under the same namespace and blocked co-importing
-- Peeling and Invariant, so it was removed.

/-! ## Main theorem interface -/

/-- Generic main-theorem hypothesis package, after the algebraic-exceptional-set
step has placed the target in `RecursiveGeneric`. -/
structure MainTheoremInputs {L k d : Nat} (r : Nat)
    (theta theta' : Params L k d) : Prop where
  L_pos : 0 < L
  k_pos : 0 < k
  r_ge_two : 2 ≤ r
  dimension_bound : dStar L k ≤ d
  target_generic : RecursiveGeneric r L k d theta'
  global_eq : TransformerAgreementEverywhere (T := seqLength r) theta theta'

/-- Conclusion of the generic matrix identifiability theorem.

Renamed from `MainTheoremConclusion` to `MainTheoremConclusionData` (this is a
data structure carrying the layerwise permutations) so that the canonical
`MainTheoremConclusion` Prop-interface in `IdentifiabilityMain.lean` can be
co-imported with the peeling capstone without a same-namespace duplicate
declaration.  This K08 scaffold is unused outside this file. -/
structure MainTheoremConclusionData {L k d : Nat}
    (theta theta' : Params L k d) where
  sigma : Fin L -> Equiv.Perm (Fin k)
  matched : LayerwiseMatched theta theta' sigma
  unique :
    ∀ tau : Fin L -> Equiv.Perm (Fin k),
      LayerwiseMatched theta theta' tau -> tau = sigma

/-- `thm-main.S`, generic-form statement interface for the headline theorem. -/
def thm_main_generic_S (r L k d : Nat) : Prop :=
  ∀ theta theta' : Params L k d,
    MainTheoremInputs r theta theta' ->
      Nonempty (MainTheoremConclusionData theta theta')

end

end TransformerIdentifiability.NLayer.KHead
