import AnyLayerIdentifiabilityProof.NLayer.KHead.BaseCase
import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.AnchorCertificate
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.PoleTransfer
import AnyLayerIdentifiabilityProof.NLayer.KHead.Induction.Relabel

set_option autoImplicit false

open Matrix
open Filter
open scoped Matrix.Norms.Frobenius
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

noncomputable section

/-!
# K-head induction invariant API

This file records the statement and data surfaces for
`tex_modular/sections/03c-induction-invariant.tex`.

The full induction theorem is kept as a statement interface.  The concrete facts
proved here are the analytic-continuation core from nonempty open equality plus
bookkeeping facts: probe equality from global transformer equality, accessors for
recursive genericity, layerwise paired matching projections, and the exact
first-layer relabeling/tail identities.
-/

/-! ## Basic gates and equality predicates -/

/-- A symbolic dimension-threshold function for the TeX bound `d_*(m,k)`. -/
abbrev DimensionThreshold : Type :=
  Nat -> Nat -> Nat

/-- The dimension gate `d_*(m,k) <= d`, parameterized by the threshold function. -/
def DimensionGate (dStar : DimensionThreshold) (m k d : Nat) : Prop :=
  dStar m k <= d

/-- Full matrix-input space for the sequence length `T = r + 1`. -/
abbrev NetworkInput (r d : Nat) : Type :=
  Matrix (Fin d) (Fin (seqLength r)) Real

/-- Nonempty Euclidean-open input set. -/
structure NonemptyOpenInputSet {r d : Nat} (omega : Set (NetworkInput r d)) : Prop where
  isOpen : IsOpen omega
  nonempty : omega.Nonempty

/-- Equality of two transformer maps on an input set. -/
def TransformerEqualOn {r m k d : Nat}
    (theta theta' : Params m k d) (omega : Set (NetworkInput r d)) : Prop :=
  forall X : NetworkInput r d, omega X -> transformer theta X = transformer theta' X

/-- Equality of two transformer maps on all inputs. -/
def TransformerEqualGlobally {r m k d : Nat}
    (theta theta' : Params m k d) : Prop :=
  forall X : NetworkInput r d, transformer theta X = transformer theta' X

/-- Equality of closed probe observables for all positive probe times. -/
def ProbeOutputEqual (r : Nat) {m k d : Nat}
    (theta theta' : Params m k d) : Prop :=
  forall w v : Vec d, forall tau : Real, 0 < tau ->
    probeOutput r theta w v tau = probeOutput r theta' w v tau

/-- Global transformer equality implies equality of the closed probe observables.

This is the non-analytic part of TeX `lem:open-set-to-global`: once global
matrix-map equality is available, the probe statement follows from
`prop-probe-recursion`. -/
theorem probeOutput_eq_of_transformerEqualGlobally {r m k d : Nat}
    (hr : 0 < r) {theta theta' : Params m k d}
    (hglobal : TransformerEqualGlobally (r := r) theta theta') :
    ProbeOutputEqual r theta theta' := by
  intro w v tau htau
  have htheta :=
    probeOutput_eq_inv_sqrt_transformer_last
      (r := r) (L := m) (k := k) (d := d) hr theta w v tau htau
  have htheta' :=
    probeOutput_eq_inv_sqrt_transformer_last
      (r := r) (L := m) (k := k) (d := d) hr theta' w v tau htau
  rw [htheta.symm, htheta'.symm, hglobal (probeMatrix r w v tau)]

/-- Conclusion package for TeX `lem:open-set-to-global`. -/
structure OpenSetToGlobalConclusion (r : Nat) {m k d : Nat}
    (theta theta' : Params m k d) : Prop where
  global_equal : TransformerEqualGlobally (r := r) theta theta'
  probe_equal : ProbeOutputEqual r theta theta'

namespace OpenSetToGlobalConclusion

/-- Constructor from already-global transformer equality. -/
def of_global {r m k d : Nat} (hr : 0 < r) {theta theta' : Params m k d}
    (hglobal : TransformerEqualGlobally (r := r) theta theta') :
    OpenSetToGlobalConclusion r theta theta' where
  global_equal := hglobal
  probe_equal := probeOutput_eq_of_transformerEqualGlobally hr hglobal

end OpenSetToGlobalConclusion

/-- The concrete analytic-continuation core of TeX `lem:open-set-to-global`.

If the two transformer maps are real analytic on the full input space, equality
on any nonempty open input set propagates to all matrix inputs.  The remaining
model-specific obligation is the independent analyticity of `transformer`. -/
theorem transformerEqualGlobally_of_equalOn_nonempty_open_of_analytic {r m k d : Nat}
    {theta theta' : Params m k d} {omega : Set (NetworkInput r d)}
    (hanalytic :
      AnalyticOnNhd Real (fun X : NetworkInput r d => transformer theta X) Set.univ)
    (hanalytic' :
      AnalyticOnNhd Real (fun X : NetworkInput r d => transformer theta' X) Set.univ)
    (hopen : IsOpen omega) (hnonempty : omega.Nonempty)
    (heq : TransformerEqualOn (r := r) theta theta' omega) :
    TransformerEqualGlobally (r := r) theta theta' := by
  rcases hnonempty with ⟨X₀, hX₀⟩
  have heventually :
      (fun X : NetworkInput r d => transformer theta X) =ᶠ[nhds X₀]
        (fun X : NetworkInput r d => transformer theta' X) :=
    Set.EqOn.eventuallyEq_of_mem
      (s := omega)
      (l := nhds X₀)
      heq
      (IsOpen.mem_nhds hopen hX₀)
  have hfun :
      (fun X : NetworkInput r d => transformer theta X) =
        (fun X : NetworkInput r d => transformer theta' X) :=
    AnalyticOnNhd.eq_of_eventuallyEq hanalytic hanalytic' heventually
  intro X
  exact congrFun hfun X

/-- Open-set-to-global conclusion from the analytic-continuation core. -/
theorem openSetToGlobalConclusion_of_equalOn_nonempty_open_of_analytic {r m k d : Nat}
    (hr : 0 < r) {theta theta' : Params m k d} {omega : Set (NetworkInput r d)}
    (hanalytic :
      AnalyticOnNhd Real (fun X : NetworkInput r d => transformer theta X) Set.univ)
    (hanalytic' :
      AnalyticOnNhd Real (fun X : NetworkInput r d => transformer theta' X) Set.univ)
    (hopen : IsOpen omega) (hnonempty : omega.Nonempty)
    (heq : TransformerEqualOn (r := r) theta theta' omega) :
    OpenSetToGlobalConclusion r theta theta' :=
  OpenSetToGlobalConclusion.of_global hr
    (transformerEqualGlobally_of_equalOn_nonempty_open_of_analytic
      hanalytic hanalytic' hopen hnonempty heq)

/-- `K03C.E.lem-open-set-to-global.S/P`: statement surface only. -/
def lem_open_set_to_global_S {r m k d : Nat}
    (theta theta' : Params m k d) (omega : Set (NetworkInput r d)) : Prop :=
  NonemptyOpenInputSet omega ->
    TransformerEqualOn (r := r) theta theta' omega ->
      OpenSetToGlobalConclusion r theta theta'

/-- Analytic implementation of `lem_open_set_to_global_S` for a fixed parameter
pair, once both transformer maps have been proved real analytic. -/
theorem lem_open_set_to_global_of_transformer_analytic {r m k d : Nat}
    (hr : 0 < r) {theta theta' : Params m k d} {omega : Set (NetworkInput r d)}
    (hanalytic :
      AnalyticOnNhd Real (fun X : NetworkInput r d => transformer theta X) Set.univ)
    (hanalytic' :
      AnalyticOnNhd Real (fun X : NetworkInput r d => transformer theta' X) Set.univ) :
    lem_open_set_to_global_S theta theta' omega := by
  intro homega heq
  exact openSetToGlobalConclusion_of_equalOn_nonempty_open_of_analytic hr
    hanalytic hanalytic' homega.isOpen homega.nonempty heq

/-! ## Concrete full-space analyticity of the transformer -/

section ConcreteTransformerAnalyticity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}

/-- Coordinate projections of an analytic matrix-valued map are analytic. -/
theorem analyticOnNhd_matrix_coord {n m : Nat}
    {F : E → Matrix (Fin n) (Fin m) ℝ}
    (hF : AnalyticOnNhd ℝ F U) (i : Fin n) (j : Fin m) :
    AnalyticOnNhd ℝ (fun x : E => F x i j) U := by
  let Prow : Matrix (Fin n) (Fin m) ℝ →L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearMap.proj i
  let Pcoord : (Fin m → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj j
  simpa [Prow, Pcoord, Function.comp] using
    (Pcoord.comp Prow).comp_analyticOnNhd hF

/-- A finite matrix-valued map is analytic when all of its coordinates are analytic.

This is the coordinate-to-Frobenius bridge for the current matrix normed-space
instance: matrices are finite Pi spaces, and `AnalyticOnNhd.pi` assembles the
coordinate power series. -/
theorem analyticOnNhd_matrix_of_coords {n m : Nat}
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

/-- Matrix addition preserves coordinatewise analyticity. -/
theorem analyticOnNhd_matrix_add_coord {n m : Nat}
    {F G : E → Matrix (Fin n) (Fin m) ℝ}
    (hF : ∀ i : Fin n, ∀ j : Fin m, AnalyticOnNhd ℝ (fun x : E => F x i j) U)
    (hG : ∀ i : Fin n, ∀ j : Fin m, AnalyticOnNhd ℝ (fun x : E => G x i j) U)
    (i : Fin n) (j : Fin m) :
    AnalyticOnNhd ℝ (fun x : E => (F x + G x) i j) U := by
  simpa using (hF i j).add (hG i j)

/-- Matrix transposition preserves coordinatewise analyticity. -/
theorem analyticOnNhd_matrix_transpose_coord {n m : Nat}
    {F : E → Matrix (Fin n) (Fin m) ℝ}
    (hF : ∀ i : Fin n, ∀ j : Fin m, AnalyticOnNhd ℝ (fun x : E => F x i j) U)
    (i : Fin m) (j : Fin n) :
    AnalyticOnNhd ℝ (fun x : E => (F x)ᵀ i j) U := by
  simpa [Matrix.transpose_apply] using hF j i

/-- Matrix multiplication preserves coordinatewise analyticity. -/
theorem analyticOnNhd_matrix_mul_coord {n m p : Nat}
    {F : E → Matrix (Fin n) (Fin m) ℝ}
    {G : E → Matrix (Fin m) (Fin p) ℝ}
    (hF : ∀ i : Fin n, ∀ j : Fin m, AnalyticOnNhd ℝ (fun x : E => F x i j) U)
    (hG : ∀ i : Fin m, ∀ j : Fin p, AnalyticOnNhd ℝ (fun x : E => G x i j) U)
    (i : Fin n) (k : Fin p) :
    AnalyticOnNhd ℝ (fun x : E => (F x * G x) i k) U := by
  simp only [Matrix.mul_apply]
  apply Finset.analyticOnNhd_fun_sum
  intro j _hj
  exact (hF i j).mul (hG j k)

/-- The causal column-softmax is analytic as a real map on all real matrices:
the denominator is a finite sum of positive exponentials. -/
theorem softmaxColC_coord_analyticOnNhd {T : Nat}
    {F : E → Matrix (Fin T) (Fin T) ℝ}
    (hF : ∀ i : Fin T, ∀ j : Fin T, AnalyticOnNhd ℝ (fun x : E => F x i j) U)
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

/-- A concrete k-head layer preserves coordinatewise analyticity. -/
theorem layer_coord_analyticOnNhd_comp {L k d T : Nat} (theta : Params L k d) (l : Fin L)
    {F : E → Matrix (Fin d) (Fin T) ℝ}
    (hF : ∀ i : Fin d, ∀ j : Fin T, AnalyticOnNhd ℝ (fun x : E => F x i j) U)
    (i : Fin d) (j : Fin T) :
    AnalyticOnNhd ℝ (fun x : E => layer theta l (F x) i j) U := by
  have hsum :
      AnalyticOnNhd ℝ
        (fun x : E =>
          ∑ a : Fin k,
            (valueMatrix theta l a * F x *
              softmaxColC ((F x)ᵀ * attentionMatrix theta l a * F x)) i j) U := by
    apply Finset.analyticOnNhd_fun_sum
    intro a _ha
    have hV :
        ∀ i' : Fin d, ∀ j' : Fin d,
          AnalyticOnNhd ℝ (fun _x : E => valueMatrix theta l a i' j') U := by
      intro i' j'
      exact analyticOnNhd_const (𝕜 := ℝ) (v := valueMatrix theta l a i' j') (s := U)
    have hA :
        ∀ i' : Fin d, ∀ j' : Fin d,
          AnalyticOnNhd ℝ (fun _x : E => attentionMatrix theta l a i' j') U := by
      intro i' j'
      exact analyticOnNhd_const (𝕜 := ℝ) (v := attentionMatrix theta l a i' j') (s := U)
    have hFT :
        ∀ i' : Fin T, ∀ j' : Fin d,
          AnalyticOnNhd ℝ (fun x : E => (F x)ᵀ i' j') U := by
      intro i' j'
      exact analyticOnNhd_matrix_transpose_coord hF i' j'
    have hleft :
        ∀ i' : Fin T, ∀ j' : Fin d,
          AnalyticOnNhd ℝ
            (fun x : E => ((F x)ᵀ * attentionMatrix theta l a) i' j') U := by
      intro i' j'
      exact analyticOnNhd_matrix_mul_coord hFT hA i' j'
    have hscore :
        ∀ i' : Fin T, ∀ j' : Fin T,
          AnalyticOnNhd ℝ
            (fun x : E => ((F x)ᵀ * attentionMatrix theta l a * F x) i' j') U := by
      intro i' j'
      exact analyticOnNhd_matrix_mul_coord hleft hF i' j'
    have hsoft :
        ∀ i' : Fin T, ∀ j' : Fin T,
          AnalyticOnNhd ℝ
            (fun x : E =>
              softmaxColC ((F x)ᵀ * attentionMatrix theta l a * F x) i' j') U := by
      intro i' j'
      exact softmaxColC_coord_analyticOnNhd hscore i' j'
    have hVF :
        ∀ i' : Fin d, ∀ j' : Fin T,
          AnalyticOnNhd ℝ (fun x : E => (valueMatrix theta l a * F x) i' j') U := by
      intro i' j'
      exact analyticOnNhd_matrix_mul_coord hV hF i' j'
    exact analyticOnNhd_matrix_mul_coord hVF hsoft i j
  intro x hx
  refine AnalyticAt.congr ((hF i j x hx).add (hsum x hx)) ?_
  filter_upwards with y
  simp [layer, Matrix.add_apply]
  exact
    (Matrix.sum_apply i j Finset.univ
      (fun a : Fin k =>
        valueMatrix theta l a * F y *
          softmaxColC ((F y)ᵀ * attentionMatrix theta l a * F y))).symm

/-- The concrete depth-`m` k-head transformer is analytic after any analytic
input map, coordinate by coordinate. -/
theorem transformer_coord_analyticOnNhd_comp {r m k d : Nat}
    (theta : Params m k d) {F : E → NetworkInput r d}
    (hF : ∀ i : Fin d, ∀ j : Fin (seqLength r),
      AnalyticOnNhd ℝ (fun x : E => F x i j) U) :
    ∀ i : Fin d, ∀ j : Fin (seqLength r),
      AnalyticOnNhd ℝ (fun x : E => transformer theta (F x) i j) U := by
  revert theta F hF
  induction m with
  | zero =>
      intro theta F hF i j
      simpa using hF i j
  | succ m ih =>
      intro theta F hF i j
      simpa [transformer] using
        ih (Fin.tail theta) (F := fun x : E => layer theta 0 (F x))
          (layer_coord_analyticOnNhd_comp theta 0 hF) i j

end ConcreteTransformerAnalyticity

/-- Input-coordinate projections are analytic on the full input space. -/
theorem networkInput_coord_analyticOnNhd_univ {r d : Nat}
    (i : Fin d) (j : Fin (seqLength r)) :
    AnalyticOnNhd ℝ (fun X : NetworkInput r d => X i j) Set.univ := by
  have hid :
      AnalyticOnNhd ℝ (fun X : NetworkInput r d => X) Set.univ := by
    simpa using
      (ContinuousLinearMap.id ℝ (NetworkInput r d)).analyticOnNhd Set.univ
  exact analyticOnNhd_matrix_coord hid i j

/-- Coordinatewise full-space real analyticity of the concrete k-head transformer map. -/
theorem transformer_coord_analyticOnNhd_univ {r m k d : Nat}
    (theta : Params m k d) (i : Fin d) (j : Fin (seqLength r)) :
    AnalyticOnNhd ℝ (fun X : NetworkInput r d => transformer theta X i j) Set.univ :=
  transformer_coord_analyticOnNhd_comp theta
    (fun i' j' => networkInput_coord_analyticOnNhd_univ i' j') i j

/-- Full-space real analyticity of the concrete k-head transformer map. -/
theorem transformer_analyticOnNhd_univ {r m k d : Nat}
    (theta : Params m k d) :
    AnalyticOnNhd ℝ (fun X : NetworkInput r d => transformer theta X) Set.univ :=
  analyticOnNhd_matrix_of_coords
    (fun i j => transformer_coord_analyticOnNhd_univ theta i j)

/-- Concrete open-set-to-global theorem for the k-head transformer. -/
theorem lem_open_set_to_global {r m k d : Nat}
    (hr : 0 < r) (theta theta' : Params m k d)
    (omega : Set (NetworkInput r d)) :
    lem_open_set_to_global_S theta theta' omega :=
  lem_open_set_to_global_of_transformer_analytic hr
    (transformer_analyticOnNhd_univ theta)
    (transformer_analyticOnNhd_univ theta')

/-! ## Recursive-generic assumption accessors -/

namespace CurrentGenericClauses

theorem regular {m k d r : Nat} {theta : Params (m + 1) k d}
    (h : CurrentGenericClauses r theta) :
    Regularity r theta :=
  h.1

theorem localOpenness {m k d r : Nat} {theta : Params (m + 1) k d}
    (h : CurrentGenericClauses r theta) :
    LocalOpenness r theta :=
  h.2.1

theorem cascade {m k d r : Nat} {theta : Params (m + 1) k d}
    (h : CurrentGenericClauses r theta) :
    CascadeCertificate theta :=
  h.2.2.1

theorem anchor {m k d r : Nat} {theta : Params (m + 1) k d}
    (h : CurrentGenericClauses r theta) :
    AnchorCertificate theta :=
  h.2.2.2

/-- Regularity inside the current generic package gives same-layer attention separation. -/
theorem attention_injective {m k d r : Nat} {theta : Params (m + 1) k d}
    (h : CurrentGenericClauses r theta) (l : Fin (m + 1)) :
    Function.Injective (fun a : Fin k => attentionMatrix theta l a) := by
  intro a b hab
  by_contra hne
  exact (h.regular.headAttention_ne l hne) hab

end CurrentGenericClauses

/-- Tail genericity supplied by `RecursiveGeneric` at positive depth. -/
theorem recursiveGeneric_tail {r m k d : Nat} {theta : Params (m + 1) k d}
    (h : RecursiveGeneric r (m + 1) k d theta) :
    RecursiveGeneric r m k d (Fin.tail theta) :=
  h.1

/-- Current-depth clauses supplied by `RecursiveGeneric` at positive depth. -/
theorem recursiveGeneric_current {r m k d : Nat} {theta : Params (m + 1) k d}
    (h : RecursiveGeneric r (m + 1) k d theta) :
    CurrentGenericClauses r theta :=
  h.2

/-! ## Layerwise paired matching -/

/-- One target-to-source head permutation for every layer. -/
abbrev LayerPermutations (m k : Nat) : Type :=
  Fin m -> Equiv.Perm (Fin k)

/-- Attention matrices matched layerwise by target-to-source permutations. -/
def LayerwiseAttentionMatched {m k d : Nat}
    (theta theta' : Params m k d) (sigma : LayerPermutations m k) : Prop :=
  forall l : Fin m, forall h : Fin k,
    attentionMatrix theta l ((sigma l) h) = attentionMatrix theta' l h

/-- Value matrices matched layerwise by the same target-to-source permutations. -/
def LayerwiseValueMatched {m k d : Nat}
    (theta theta' : Params m k d) (sigma : LayerPermutations m k) : Prop :=
  forall l : Fin m, forall h : Fin k,
    valueMatrix theta l ((sigma l) h) = valueMatrix theta' l h

/-- Paired layerwise matching: no separate value permutation is introduced. -/
structure LayerwisePairedMatching {m k d : Nat}
    (theta theta' : Params m k d) (sigma : LayerPermutations m k) : Prop where
  attention : LayerwiseAttentionMatched theta theta' sigma
  value : LayerwiseValueMatched theta theta' sigma

namespace LayerwisePairedMatching

theorem inverse_attention {m k d : Nat} {theta theta' : Params m k d}
    {sigma : LayerPermutations m k} (hmatch : LayerwisePairedMatching theta theta' sigma) :
    forall l : Fin m, forall a : Fin k,
      attentionMatrix theta l a = attentionMatrix theta' l ((sigma l).symm a) := by
  intro l a
  simpa using hmatch.attention l ((sigma l).symm a)

theorem inverse_value {m k d : Nat} {theta theta' : Params m k d}
    {sigma : LayerPermutations m k} (hmatch : LayerwisePairedMatching theta theta' sigma) :
    forall l : Fin m, forall a : Fin k,
      valueMatrix theta l a = valueMatrix theta' l ((sigma l).symm a) := by
  intro l a
  simpa using hmatch.value l ((sigma l).symm a)

end LayerwisePairedMatching

/-- Matching conclusion with the unique layerwise target-to-source permutations.

The selected permutations depend only on the two parameters, not on an input
open set. -/
structure LayerwiseMatchingConclusion {m k d : Nat}
    (theta theta' : Params m k d) where
  sigma : LayerPermutations m k
  paired : LayerwisePairedMatching theta theta' sigma
  unique :
    forall tau : LayerPermutations m k,
      LayerwisePairedMatching theta theta' tau -> tau = sigma

namespace LayerwiseMatchingConclusion

/-- Depth-one layerwise matching from the K05 base-case endpoint.  The single
layerwise permutation is the unique target-to-source head permutation returned
by `K05_prop_base_case`. -/
noncomputable def of_baseCaseData {k d r : Nat}
    {theta theta' : Params 1 k d} (D : BaseCaseData r theta theta') :
    LayerwiseMatchingConclusion theta theta' := by
  classical
  let sigma : Equiv.Perm (Fin k) := Classical.choose (K05_prop_base_case D)
  have hsigma :
      (∀ h : Fin k,
        baseAttention theta (sigma h) = baseAttention theta' h ∧
          baseValue theta (sigma h) = baseValue theta' h) ∧
        ∀ tau : Equiv.Perm (Fin k),
          (∀ h : Fin k,
            baseAttention theta (tau h) = baseAttention theta' h ∧
              baseValue theta (tau h) = baseValue theta' h) →
            tau = sigma :=
    Classical.choose_spec (K05_prop_base_case D)
  refine
    { sigma := fun _ => sigma
      paired := ?_
      unique := ?_ }
  · refine ⟨?_, ?_⟩
    · intro l h
      have hl : l = 0 := Subsingleton.elim l 0
      subst l
      simpa [baseAttention] using (hsigma.1 h).1
    · intro l h
      have hl : l = 0 := Subsingleton.elim l 0
      subst l
      simpa [baseValue] using (hsigma.1 h).2
  · intro tau htau
    have htau_zero : tau 0 = sigma := by
      apply hsigma.2 (tau 0)
      intro h
      exact
        ⟨by simpa [baseAttention] using htau.attention 0 h,
          by simpa [baseValue] using htau.value 0 h⟩
    funext l
    have hl : l = 0 := Subsingleton.elim l 0
    subst l
    exact htau_zero

end LayerwiseMatchingConclusion

/-! ## Cons/tail projections for layerwise permutation tuples

These are the `LayerPermutations`/`LayerwisePairedMatching` counterparts of the
`consLayerPerm`/`layerwiseMatched_cons` API in `Induction/Peeling.lean`.  They are
re-declared here (rather than imported) because `Invariant.lean` must not import
`Peeling.lean` — that would create an import cycle. -/

-- `consLayerPerm` and its `_zero`/`_succ` simp lemmas now live in
-- `Induction/Relabel.lean` (imported above), shared with `Induction/Peeling.lean`
-- so that both files can be co-imported.  The tail-tuple argument there uses the
-- raw type `Fin m → Equiv.Perm (Fin k)`, definitionally `LayerPermutations m k`.

namespace LayerwisePairedMatching

/-- Assemble first-layer paired matching (attention and value at layer `0`) and a
tail paired matching into a full paired matching indexed by `consLayerPerm σ τ`. -/
theorem cons {m k d : Nat} {θ θ' : Params (m + 1) k d}
    {σ : Equiv.Perm (Fin k)} {τ : LayerPermutations m k}
    (hattn0 : ∀ h, attentionMatrix θ 0 (σ h) = attentionMatrix θ' 0 h)
    (hval0 : ∀ h, valueMatrix θ 0 (σ h) = valueMatrix θ' 0 h)
    (htail : LayerwisePairedMatching (Fin.tail θ) (Fin.tail θ') τ) :
    LayerwisePairedMatching θ θ' (consLayerPerm σ τ) := by
  refine ⟨?_, ?_⟩
  · intro l h
    cases l using Fin.cases with
    | zero => simpa using hattn0 h
    | succ l => simpa [Fin.tail] using htail.attention l h
  · intro l h
    cases l using Fin.cases with
    | zero => simpa using hval0 h
    | succ l => simpa [Fin.tail] using htail.value l h

/-- Restrict a full paired matching to the tail layers. -/
theorem tail {m k d : Nat} {θ θ' : Params (m + 1) k d}
    {sigma : LayerPermutations (m + 1) k}
    (M : LayerwisePairedMatching θ θ' sigma) :
    LayerwisePairedMatching (Fin.tail θ) (Fin.tail θ')
      (fun l : Fin m => sigma l.succ) := by
  refine ⟨?_, ?_⟩
  · intro l h
    simpa [Fin.tail] using M.attention l.succ h
  · intro l h
    simpa [Fin.tail] using M.value l.succ h

/-- The first layer of a full paired matching is a first-layer paired match. -/
theorem first {m k d : Nat} {θ θ' : Params (m + 1) k d}
    {sigma : LayerPermutations (m + 1) k}
    (M : LayerwisePairedMatching θ θ' sigma) :
    (∀ h, attentionMatrix θ 0 ((sigma 0) h) = attentionMatrix θ' 0 h) ∧
      (∀ h, valueMatrix θ 0 ((sigma 0) h) = valueMatrix θ' 0 h) :=
  ⟨fun h => M.attention 0 h, fun h => M.value 0 h⟩

end LayerwisePairedMatching

/-! ## First-layer paired relabeling and the exact tail -/

-- The canonical `relabelFirstLayer` and its `_zero`/`_succ`/`_tail` simp lemmas
-- now live in `Induction/Relabel.lean` and are imported above, so that this file
-- and `Induction/Peeling.lean` can be co-imported without a duplicate declaration.

/-- If the first layer is paired by the selected permutation, the relabeled first
layer is exactly the target first layer. -/
theorem relabelFirstLayer_first_eq_of_layerwisePairedMatching {L k d : Nat}
    {theta theta' : Params (L + 1) k d} {sigma : LayerPermutations (L + 1) k}
    (hmatch : LayerwisePairedMatching theta theta' sigma) :
    forall h : Fin k, relabelFirstLayer theta (sigma 0) 0 h = theta' 0 h := by
  intro h
  apply Params.head_eq_of_valueMatrix_attentionMatrix_eq
  · simpa [relabelFirstLayer] using hmatch.value 0 h
  · simpa [relabelFirstLayer] using hmatch.attention 0 h

/-- C4 tail-reduction data for a depth at least two parameter pair. -/
structure FirstLayerTailReductionData {m k d : Nat} (r : Nat)
    (theta theta' : Params (m + 2) k d)
    (sigma : Equiv.Perm (Fin k)) where
  omega_tail : Set (NetworkInput r d)
  omega_tail_open : IsOpen omega_tail
  omega_tail_nonempty : omega_tail.Nonempty
  target_tail_generic : RecursiveGeneric r (m + 1) k d (Fin.tail theta')
  source_tail_unchanged : Fin.tail (relabelFirstLayer theta sigma) = Fin.tail theta
  first_layer_equal : forall h : Fin k, relabelFirstLayer theta sigma 0 h = theta' 0 h
  tail_equal_on :
    TransformerEqualOn (r := r) (Fin.tail (relabelFirstLayer theta sigma))
      (Fin.tail theta') omega_tail

namespace FirstLayerTailReductionData

/-- The reduced hypothesis compares the unchanged source tail with the target tail. -/
theorem tail_equal_on_source_tail {m k d r : Nat}
    {theta theta' : Params (m + 2) k d} {sigma : Equiv.Perm (Fin k)}
    (D : FirstLayerTailReductionData r theta theta' sigma) :
    TransformerEqualOn (r := r) (Fin.tail theta) (Fin.tail theta') D.omega_tail := by
  intro X hX
  have h := D.tail_equal_on X hX
  simpa [D.source_tail_unchanged] using h

/-- Constructor when the exact reduced tail equality is already stated for the
unchanged source tail. -/
def of_source_tail_equal_on {m k d r : Nat}
    {theta theta' : Params (m + 2) k d} {sigma : Equiv.Perm (Fin k)}
    {omega_tail : Set (NetworkInput r d)}
    (hopen : IsOpen omega_tail) (hnonempty : omega_tail.Nonempty)
    (htarget : RecursiveGeneric r (m + 1) k d (Fin.tail theta'))
    (hfirst : forall h : Fin k, relabelFirstLayer theta sigma 0 h = theta' 0 h)
    (htail :
      TransformerEqualOn (r := r) (Fin.tail theta) (Fin.tail theta') omega_tail) :
    FirstLayerTailReductionData r theta theta' sigma where
  omega_tail := omega_tail
  omega_tail_open := hopen
  omega_tail_nonempty := hnonempty
  target_tail_generic := htarget
  source_tail_unchanged := relabelFirstLayer_tail theta sigma
  first_layer_equal := hfirst
  tail_equal_on := by
    intro X hX
    simpa [relabelFirstLayer_tail theta sigma] using htail X hX

end FirstLayerTailReductionData

/-! ## Unconditional depth-one base case -/

/-- Depth-one conversion adapter: a Step-1 first-layer separated probe for the
target `theta'` is a K05 `BaseSeparatedProbe`.

At depth one (`Params 1 k d`, i.e. `m = 0`) the two probe-separation notions
coincide.  The slope fields are definitionally identical (`baseSlope` and
`Step1.firstLayerSlope` both evaluate `matrixBilin (attentionMatrix theta' 0 h)`),
and the coefficient nonvanishing `baseValue theta' h *ᵥ p.1 ≠ 0` is exactly the
Step-1 cascade residue-vector nonvanishing, since for `m = 0` the cascade final
product `cascadeFinalProduct theta' h χ = cascadeProduct theta' h χ 0` reduces to
`valueMatrix theta' 0 h = baseValue theta' h`. -/
theorem baseSeparatedProbe_of_firstLayerSeparatedProbe {k d r : Nat}
    {theta' : Params 1 k d} {chains : Step1.Step1ChainChoices theta'}
    {p : ProbePoint d}
    (hp : Step1.FirstLayerSeparatedProbe r theta' chains p) :
    BaseSeparatedProbe theta' p.1 p.2 := by
  obtain ⟨hslope, hcasc, _hcorner⟩ := hp
  refine ⟨fun h => ?_, ?_, fun h => ?_⟩
  · exact hslope.1 h
  · exact hslope.2
  · have hEq : Step1.cascadeResidueVector (chains h) p = baseValue theta' h *ᵥ p.1 := rfl
    rw [← hEq]
    exact (hcasc h).1

/-- **K03C.M4 core:** construct the depth-one K05 `BaseCaseData` from genuine
hypotheses, with no `BaseCaseData` assumption.

Given `1 < r`, recursive genericity of the target `theta'`, and closed
probe-output equality of the two depth-one parameters, take the target's Step-1
first-layer separated set `U = Omega = Step1.firstLayerSeparatedSet` (open, dense,
Zariski-dense, and consisting of `BaseSeparatedProbe`s by regularity and the
cascade certificate) and feed it to
`BaseCaseData.of_positive_real_probeOutput_equality_open_probe_set`. -/
noncomputable def baseCaseData_of_recursiveGeneric_of_probeOutputEqual
    {r k d : Nat} (hr : 1 < r) {theta theta' : Params 1 k d}
    (hgen : RecursiveGeneric r 1 k d theta')
    (hprobe : ProbeOutputEqual r theta theta') :
    BaseCaseData r theta theta' := by
  classical
  have hclauses := recursiveGeneric_current hgen
  have hθ' : Regularity r theta' := hclauses.regular
  have chains : Step1.Step1ChainChoices theta' :=
    Step1.step1ChainChoicesOfCascadeCertificate hclauses.cascade
  have hprops := Step1.firstLayerSeparatedSetProperties_of_regular hθ' chains
  refine BaseCaseData.of_positive_real_probeOutput_equality_open_probe_set hr hθ'
    { U := Step1.firstLayerSeparatedSet r theta' chains
      zariski_dense :=
        Step1.probeZariskiDense_of_zariskiDenseProbeSet hprops.zariski_dense
      target_separated := fun _x hx => baseSeparatedProbe_of_firstLayerSeparatedProbe hx
      positive_real_probeOutput_eq_on := fun x _hx τ hτ => hprobe x.1 x.2 τ hτ }
    hprops.isOpen hprops.nonempty subset_rfl

/-! ## Open-set induction invariant statement surfaces -/

/-- Hypothesis package for TeX `thm:open-induction-invariant`. -/
structure OpenSetInductionInvariantHypotheses (dStar : DimensionThreshold)
    (r : Nat) {m k d : Nat} (theta theta' : Params m k d)
    (omega : Set (NetworkInput r d)) : Prop where
  depth_pos : 1 <= m
  heads_pos : 1 <= k
  rate_ge_two : 2 <= r
  dimension_gate : DimensionGate dStar m k d
  target_generic : RecursiveGeneric r m k d theta'
  omega_open : IsOpen omega
  omega_nonempty : omega.Nonempty
  equal_on : TransformerEqualOn (r := r) theta theta' omega

namespace OpenSetInductionInvariantHypotheses

theorem rate_pos {dStar : DimensionThreshold} {r m k d : Nat}
    {theta theta' : Params m k d} {omega : Set (NetworkInput r d)}
    (H : OpenSetInductionInvariantHypotheses dStar r theta theta' omega) :
    0 < r := by
  exact lt_of_lt_of_le (by norm_num : 0 < 2) H.rate_ge_two

theorem nonemptyOpen {dStar : DimensionThreshold} {r m k d : Nat}
    {theta theta' : Params m k d} {omega : Set (NetworkInput r d)}
    (H : OpenSetInductionInvariantHypotheses dStar r theta theta' omega) :
    NonemptyOpenInputSet omega where
  isOpen := H.omega_open
  nonempty := H.omega_nonempty

end OpenSetInductionInvariantHypotheses

/-- The C1-C3 conclusion package of the open-set invariant. -/
structure OpenSetInductionInvariantConclusion (r : Nat) {m k d : Nat}
    (theta theta' : Params m k d) where
  global_equal : TransformerEqualGlobally (r := r) theta theta'
  probe_equal : ProbeOutputEqual r theta theta'
  matching : LayerwiseMatchingConclusion theta theta'

namespace OpenSetInductionInvariantConclusion

/-- Constructor from global equality and layerwise matching data. -/
def of_global_and_matching {r m k d : Nat} (hr : 0 < r)
    {theta theta' : Params m k d}
    (hglobal : TransformerEqualGlobally (r := r) theta theta')
    (matching : LayerwiseMatchingConclusion theta theta') :
    OpenSetInductionInvariantConclusion r theta theta' where
  global_equal := hglobal
  probe_equal := probeOutput_eq_of_transformerEqualGlobally hr hglobal
  matching := matching

/-- Constructor from the open-set-to-global conclusion and K05 depth-one
base-case data. -/
noncomputable def of_openSetToGlobal_and_baseCaseData {r k d : Nat}
    {theta theta' : Params 1 k d}
    (hglobal : OpenSetToGlobalConclusion r theta theta')
    (D : BaseCaseData r theta theta') :
    OpenSetInductionInvariantConclusion r theta theta' where
  global_equal := hglobal.global_equal
  probe_equal := hglobal.probe_equal
  matching := LayerwiseMatchingConclusion.of_baseCaseData D

/-- Conditional K03C.M4a depth-one adapter: K05 base-case data plus nonempty
open-set transformer equality gives the C1-C3 invariant conclusion for
`Params 1 k d`.  This does not supply the upstream construction of
`BaseCaseData`; that is the remaining unconditional base-case gate. -/
noncomputable def depth_one_of_baseCaseData {r k d : Nat} (hr : 0 < r)
    {theta theta' : Params 1 k d} {omega : Set (NetworkInput r d)}
    (D : BaseCaseData r theta theta')
    (homega : NonemptyOpenInputSet omega)
    (heq : TransformerEqualOn (r := r) theta theta' omega) :
    OpenSetInductionInvariantConclusion r theta theta' :=
  of_openSetToGlobal_and_baseCaseData
    ((lem_open_set_to_global hr theta theta' omega) homega heq) D

/-- **K03C.M4 (unconditional depth-one base case).**  For `Params 1 k d`, the
C1-C3 open-set invariant conclusion holds with no `BaseCaseData` assumption: it is
constructed from `1 < r`, recursive genericity of the target `theta'`, a nonempty
open input set `omega`, and open-set transformer equality.

The `BaseCaseData` is produced by
`baseCaseData_of_recursiveGeneric_of_probeOutputEqual` (using the target's Step-1
separated set), and the result is threaded through the existing
`depth_one_of_baseCaseData` adapter. -/
noncomputable def depth_one {r k d : Nat} (hr : 1 < r)
    {theta theta' : Params 1 k d}
    (hgen : RecursiveGeneric r 1 k d theta')
    {omega : Set (NetworkInput r d)}
    (homega : NonemptyOpenInputSet omega)
    (heq : TransformerEqualOn (r := r) theta theta' omega) :
    OpenSetInductionInvariantConclusion r theta theta' := by
  have hr0 : 0 < r := by omega
  have hprobe : ProbeOutputEqual r theta theta' :=
    (lem_open_set_to_global hr0 theta theta' omega homega heq).probe_equal
  exact depth_one_of_baseCaseData hr0
    (baseCaseData_of_recursiveGeneric_of_probeOutputEqual hr hgen hprobe)
    homega heq

end OpenSetInductionInvariantConclusion

/-- C1-C4 conclusion package specialized to depth at least two. -/
structure OpenSetInductionInvariantTailConclusion (r : Nat) {m k d : Nat}
    (theta theta' : Params (m + 2) k d) where
  base : OpenSetInductionInvariantConclusion r theta theta'
  tail_reduction :
    FirstLayerTailReductionData r theta theta' (base.matching.sigma 0)

/-- **K03C.M5 core assembly (single induction step).**  Given, at depth `m + 2`:

* global transformer equality `hglobal` (the open-set-to-global output),
* the first-layer tail-reduction data `D` produced by the Step-3 peeling adapter,
  whose selected first-layer permutation is `sigma`,
* the first-layer attention uniqueness gun `huniq0` (from peeling), and
* the tail induction hypothesis `tailMatching` — a full `LayerwiseMatchingConclusion`
  for the reduced tail pair `(Fin.tail θ, Fin.tail θ')`,

assemble the C1–C4 tail conclusion.  The `σ`-seam between the first-layer
permutation carried by `D` and the layer-`0` component of the assembled matching
permutation dissolves *by construction*: the matching permutation is
`consLayerPerm sigma tailMatching.sigma`, whose layer-`0` value is `sigma` by
`rfl` (`consLayerPerm_zero`), so `D` typechecks as the `tail_reduction` field.

This is a genuine conditional reduction: `tailMatching` is the honest tail IH, not
a restatement of the goal, and no value-permutation wiring (`hV`) is needed in the
core — first-layer values come directly from `D.first_layer_equal`. -/
def openSetInductionInvariantTailConclusion_of_data {m k d r : Nat} (hr : 0 < r)
    {θ θ' : Params (m + 2) k d} {sigma : Equiv.Perm (Fin k)}
    (hglobal : TransformerEqualGlobally (r := r) θ θ')
    (D : FirstLayerTailReductionData r θ θ' sigma)
    (huniq0 : ∀ ρ : Equiv.Perm (Fin k),
      (∀ h, attentionMatrix θ 0 (ρ h) = attentionMatrix θ' 0 h) → ρ = sigma)
    (tailMatching : LayerwiseMatchingConclusion (Fin.tail θ) (Fin.tail θ')) :
    OpenSetInductionInvariantTailConclusion r θ θ' := by
  -- First-layer head equality from `D`, split into attention and value equalities.
  have hfirst : ∀ h, θ 0 (sigma h) = θ' 0 h := by
    intro h
    have h1 := D.first_layer_equal h
    rwa [relabelFirstLayer_zero] at h1
  have hattn0 : ∀ h, attentionMatrix θ 0 (sigma h) = attentionMatrix θ' 0 h :=
    fun h => congrArg Prod.snd (hfirst h)
  have hval0 : ∀ h, valueMatrix θ 0 (sigma h) = valueMatrix θ' 0 h :=
    fun h => congrArg Prod.fst (hfirst h)
  -- The assembled layerwise matching, with layer-`0` permutation equal to `sigma`.
  let matching : LayerwiseMatchingConclusion θ θ' :=
    { sigma := consLayerPerm sigma tailMatching.sigma
      paired := LayerwisePairedMatching.cons hattn0 hval0 tailMatching.paired
      unique := by
        intro tau htau
        have htau0 : tau 0 = sigma :=
          huniq0 (tau 0) (fun h => htau.attention 0 h)
        have htail_eq : (fun l : Fin (m + 1) => tau l.succ) = tailMatching.sigma :=
          tailMatching.unique (fun l => tau l.succ) htau.tail
        funext l
        cases l using Fin.cases with
        | zero => simpa using htau0
        | succ l => simpa using congrFun htail_eq l }
  refine
    { base := OpenSetInductionInvariantConclusion.of_global_and_matching hr hglobal matching
      tail_reduction := ?_ }
  -- `base.matching.sigma 0` reduces to `sigma` (`consLayerPerm_zero` is `rfl`).
  exact D

/-- `K03C.E.thm-open-induction-invariant.S/P`: C1-C3 statement surface. -/
abbrev thm_open_induction_invariant_S (dStar : DimensionThreshold)
    {r m k d : Nat} (theta theta' : Params m k d)
    (omega : Set (NetworkInput r d)) : Type :=
  OpenSetInductionInvariantHypotheses dStar r theta theta' omega ->
    OpenSetInductionInvariantConclusion r theta theta'

/-- C4 statement surface for depths `m + 2`, i.e. TeX depths at least two. -/
abbrev thm_open_induction_invariant_tail_S (dStar : DimensionThreshold)
    {r m k d : Nat} (theta theta' : Params (m + 2) k d)
    (omega : Set (NetworkInput r d)) : Type :=
  OpenSetInductionInvariantHypotheses dStar r theta theta' omega ->
    OpenSetInductionInvariantTailConclusion r theta theta'

/-- `K03C.E.rem-invariant-assumptions.S/P`: the carried assumptions exposed as
an API payload. -/
def rem_invariant_assumptions_S (dStar : DimensionThreshold)
    {r m k d : Nat} (theta theta' : Params m k d)
    (omega : Set (NetworkInput r d)) : Prop :=
  OpenSetInductionInvariantHypotheses dStar r theta theta' omega ->
    RecursiveGeneric r m k d theta' /\ NonemptyOpenInputSet omega

/-- The assumptions payload is just a projection of the theorem hypotheses. -/
theorem rem_invariant_assumptions_of_hypotheses {dStar : DimensionThreshold}
    {r m k d : Nat} {theta theta' : Params m k d}
    {omega : Set (NetworkInput r d)}
    (H : OpenSetInductionInvariantHypotheses dStar r theta theta' omega) :
    RecursiveGeneric r m k d theta' /\ NonemptyOpenInputSet omega := by
  exact ⟨H.target_generic, H.nonemptyOpen⟩

end

end TransformerIdentifiability.NLayer.KHead
