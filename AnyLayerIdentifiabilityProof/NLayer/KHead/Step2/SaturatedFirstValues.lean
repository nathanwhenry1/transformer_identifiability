import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.TrichotomyInstance
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.Saturated
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.PoleTransfer
import AnyLayerIdentifiabilityProof.NLayer.KHead.Induction.Peeling

set_option autoImplicit false

open Matrix Filter Topology
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K07C.M7 residual + M9 (`prop:first-V`)

This file is placed *downstream* of both `Step2/Saturated.lean` (M7/M8 API,
`SaturatedKCancellationData`) and `Step2/TrichotomyInstance.lean` (K07B trichotomy +
`tendsto_satZetaActualProbePoint`).  This is the only placement at which the θ-side
(unprimed) observable convergence needed to discharge the M7 residual `hUnprimed` can be
proved, since `tendsto_satZetaActualProbePoint` lives in `TrichotomyInstance`, which is
downstream of `Saturated`.

* **SUB-GOAL A** — `saturatedLimit_pointwise_eq_of_signRegionData`: discharge `hUnprimed`
  from the concrete K07B region and produce the unconditional pointwise saturated-limit
  equality on the trichotomy region `Ustar`.
* **SUB-GOAL B** — `firstValue_eq_of_...` + `prop_first_V_S_of_...` + `prop_first_V`:
  coefficient extraction (isolated residual) → `SaturatedKCancellationData` → `V = V'` →
  peeling value matching.
-/

/-! ## First-layer head relabeling is transformer/probe invariant

The head sum inside a single layer is symmetric, so relabeling the first-layer heads by a
permutation leaves the transformer — and hence the probe observable — unchanged.  This is
the bridge used to move the standing probe-output equality `probeOutput θ = θ'` onto the
K06C-relabeled source `relabelFirstLayer θ σ`. -/

/-- Relabeling the first-layer heads by a permutation does not change the first layer map,
since the head sum is symmetric. -/
theorem layer_relabelFirstLayer_zero {m k d T : Nat} (θ : Params (m + 1) k d)
    (σ : Equiv.Perm (Fin k)) (X : Matrix (Fin d) (Fin T) ℝ) :
    layer (relabelFirstLayer θ σ) 0 X = layer θ 0 X := by
  classical
  simp only [layer]
  congr 1
  simpa [relabelFirstLayer, valueMatrix, attentionMatrix] using
    (Equiv.sum_comp σ fun a : Fin k =>
      valueMatrix θ 0 a * X * softmaxColC (Xᵀ * attentionMatrix θ 0 a * X))

/-- Relabeling the first-layer heads by a permutation leaves the whole transformer
unchanged. -/
theorem transformer_relabelFirstLayer {m k d T : Nat} (θ : Params (m + 1) k d)
    (σ : Equiv.Perm (Fin k)) (X : Matrix (Fin d) (Fin T) ℝ) :
    transformer (relabelFirstLayer θ σ) X = transformer θ X := by
  show transformer (Fin.tail (relabelFirstLayer θ σ)) (layer (relabelFirstLayer θ σ) 0 X)
      = transformer (Fin.tail θ) (layer θ 0 X)
  rw [relabelFirstLayer_tail, layer_relabelFirstLayer_zero]

/-- The relabeled source satisfies the global transformer equality against the source. -/
theorem probeOutputEquality_relabelFirstLayer {r m k d : Nat} (hr : 0 < r)
    (θ : Params (m + 1) k d) (σ : Equiv.Perm (Fin k)) :
    Step1.ProbeOutputEquality r (relabelFirstLayer θ σ) θ :=
  Step1.probeOutputEquality_of_global hr (fun X => transformer_relabelFirstLayer θ σ X)

/-! ## SUB-GOAL A — completing the M7 residual `hUnprimed`

`lem_saturated_limit_S_of_primed_convergence` (M7, in `Saturated.lean`) proves the pointwise
saturated-limit equality from honest hypotheses plus one threaded residual `hUnprimed` (the
θ-side observable converging to the unprimed saturated limit vector).  We discharge
`hUnprimed` here: for the concrete K07B trichotomy result `R`, the ζ-frozen convergence
`TrichotomyResult.tendsto_satZetaActualProbePoint_of_alpha_estimate` gives the layer-`(m+1)`
actual probe point limit `satZetaPoint θ h ζ p t (m+1)`, whose second coordinate is (by
`satZetaPoint_snd` + `unprimedSaturatedLimitVector_eq_mulVec`) exactly the unprimed limit
vector.  Passing through `actualProbePoint_snd_eq_probeOutput` re-expresses the actual
probe point's second coordinate as `probeOutput`, matching `hUnprimed`. -/

/-- **SUB-GOAL A (the unconditional saturated-limit equality).**  From the concrete K07B
trichotomy result `R` for the (relabeled) source `θ`, together with the standing genericity
witness `D`, first-layer separation `hsep`, the common first-attention/probe agreement
(`hAttn`, `hAgree`) against the primed target `θ'`, and the primed deeper-slope positivity
`hposθ'`, we obtain the pointwise equality of the unprimed and primed saturated limit
vectors on the trichotomy region `R.Ustar`.

The θ-side residual `hUnprimed` is discharged internally via the ζ-side saturation
`tendsto_satZetaActualProbePoint_of_alpha_estimate`; the primed side, telescoping data
(`M' = collapsePrefix θ' (m+1)`, `C1' = I`), and value `Vh' = valueMatrix θ' 0 h` are fixed
by the recipe. -/
theorem saturatedLimit_pointwise_eq
    {m k d r : Nat} (θ θ' : Params (m + 1) k d) (h : Fin k)
    (D : SignRegionData θ h)
    (R : TrichotomyResult (dialPredicatesWithEstimate r θ h) (dialFormalData r θ h)
      D.region (deeperHeadOrder (m + 1) k))
    (hsep : ∀ x ∈ D.region, ∀ b : Fin k, b ≠ h →
      0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2)
    (hAttn : attentionMatrix θ 0 = attentionMatrix θ' 0)
    (hAgree : ∀ (w v : Vec d) (τ : ℝ), 0 < τ →
      probeOutput r θ w v τ = probeOutput r θ' w v τ)
    (hposθ' : ∀ x ∈ D.region, ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ a : Fin k,
      0 < matrixBilin (attentionMatrix θ' ⟨n, hn⟩ a)
        (dialSatPoint θ' h x.1 x.2 n).1 (dialSatPoint θ' h x.1 x.2 n).2) :
    lem_saturated_limit_S R.Ustar
      (fun x => unprimedSaturatedLimitVector
        (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
        (saturatedE (saturatedC (deeperValueStream θ))
          (saturatedTailD (deeperValueStream θ)
            (trichotomyToSaturatedLabels r (m + 1) k R.labels))
          (saturatedKLayer (deeperValueStream θ)
            (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1))
        (saturatedTailK
          (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
          (saturatedE (saturatedC (deeperValueStream θ))
            (saturatedTailD (deeperValueStream θ)
              (trichotomyToSaturatedLabels r (m + 1) k R.labels))
            (saturatedKLayer (deeperValueStream θ)
              (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1)))
        (firstLayerOtherValueSum θ h) (valueMatrix θ 0 h) (collapseMatrix θ 0) x.2 x.1)
      (fun x => primedSaturatedLimitVector (collapsePrefix θ' (m + 1)) 1
        (valueMatrix θ' 0 h) x.2 x.1) := by
  have hsub : R.Ustar ⊆ D.region := R.region_subset_base
  have Sif : SignRegionInterface (attentionMatrix θ 0) (valueMatrix θ 0) h D.region :=
    signRegionData_signRegionInterface D
  -- The θ-side (unprimed) observable convergence residual `hUnprimed`.
  have hUnprimed : ∀ x ∈ R.Ustar,
      Tendsto (fun τ => probeOutput r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2 τ)
        atTop (𝓝 (unprimedSaturatedLimitVector
          (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
          (saturatedE (saturatedC (deeperValueStream θ))
            (saturatedTailD (deeperValueStream θ)
              (trichotomyToSaturatedLabels r (m + 1) k R.labels))
            (saturatedKLayer (deeperValueStream θ)
              (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1))
          (saturatedTailK
            (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
            (saturatedE (saturatedC (deeperValueStream θ))
              (saturatedTailD (deeperValueStream θ)
                (trichotomyToSaturatedLabels r (m + 1) k R.labels))
              (saturatedKLayer (deeperValueStream θ)
                (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1)))
          (firstLayerOtherValueSum θ h) (valueMatrix θ 0 h) (collapseMatrix θ 0)
          x.2 x.1)) := by
    intro x hx
    -- α-branch slope estimate for the *final* trichotomy result.
    have halpha : ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ (a : Fin k),
        R.toDialPredicates.labels { layer := n + 1, head := (a : Nat) + 1 } =
            TrichotomyLabel.alpha →
          Tendsto (fun τ => τ * actualProbeSlope r θ
            (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
            (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2
            τ ⟨n, hn⟩ a) atTop (𝓝 0) := by
      intro n hnpos hn a hlabel
      have hz : zeroDialForm (phiHeadOfDeeperHead r θ h
          ({ layer := n + 1, head := (a : Nat) + 1 } : DeeperHead) R.labels) :=
        R.toDialPredicates.zeroDialForm_of_label_alpha
          (succ_head_mem_deeperHeadOrder hnpos hn a) hlabel
      have hsep_pt : ∀ b : Fin k, b ≠ h →
          0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2 :=
        fun b hb => hsep x (hsub hx) b hb
      have hprior : ∀ (q : Nat), 1 ≤ q → q < n → (hq' : q < m + 1) → ∀ (b : Fin k),
          EventuallyExpClose (fun τ => actualProbeGate r θ
            (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
            (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2 τ ⟨q, hq'⟩ b)
            (trichotomyToSaturatedLabels r (m + 1) k R.labels (q + 1) b) := by
        intro q hqpos _hqn hq' b
        have hmemq : ({ layer := q + 1, head := (b : Nat) + 1 } : DeeperHead) ∈
            processedPrefix (deeperHeadOrder (m + 1) k)
              ((deeperHeadOrder (m + 1) k).length) := by
          rw [processedPrefix, List.take_length]
          exact succ_head_mem_deeperHeadOrder hqpos hq' b
        exact eventuallyExpClose_of_expCloseTo
          (R.estimate.gate hqpos hq' b hmemq x hx)
      exact tendsto_tau_mul_actualProbeSlope_zero_of_zeroDialForm_sep
        θ h R.labels x.1 x.2 n hnpos hn a hz hsep_pt hprior
    have hpt := R.toDialPredicates.tendsto_satZetaActualProbePoint_of_alpha_estimate
      (p := x.1) (t := x.2) hx halpha
      (Sif.t_pos x (hsub hx)) (Sif.t_lt_one x (hsub hx))
      (Sif.point_on_quadric x (hsub hx)) (Sif.pi_ne_zero x (hsub hx))
      (fun a ha => hsep x (hsub hx) a ha) (m + 1) le_rfl
    simp only [TrichotomyResult.toDialPredicates_labels] at hpt
    have hsnd := (continuous_snd.tendsto
      (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k R.labels)
        x.1 x.2 (m + 1))).comp hpt
    have hval : (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k R.labels)
        x.1 x.2 (m + 1)).2 = unprimedSaturatedLimitVector
          (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
          (saturatedE (saturatedC (deeperValueStream θ))
            (saturatedTailD (deeperValueStream θ)
              (trichotomyToSaturatedLabels r (m + 1) k R.labels))
            (saturatedKLayer (deeperValueStream θ)
              (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1))
          (saturatedTailK
            (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
            (saturatedE (saturatedC (deeperValueStream θ))
              (saturatedTailD (deeperValueStream θ)
                (trichotomyToSaturatedLabels r (m + 1) k R.labels))
              (saturatedKLayer (deeperValueStream θ)
                (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1)))
          (firstLayerOtherValueSum θ h) (valueMatrix θ 0 h) (collapseMatrix θ 0)
          x.2 x.1 := by
      rw [satZetaPoint_snd θ h (trichotomyToSaturatedLabels r (m + 1) k R.labels)
        x.1 x.2 (m + 1) (Nat.le_add_left 1 m) le_rfl]
      simp only [firstLayerUnsatB]
      rw [← unprimedSaturatedLimitVector_eq_mulVec
        (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
        (saturatedE (saturatedC (deeperValueStream θ))
          (saturatedTailD (deeperValueStream θ)
            (trichotomyToSaturatedLabels r (m + 1) k R.labels))
          (saturatedKLayer (deeperValueStream θ)
            (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1))
        (firstLayerOtherValueSum θ h) (valueMatrix θ 0 h) (collapseMatrix θ 0)
        x.2 x.1.1 x.1.2]
    rw [hval] at hsnd
    refine hsnd.congr (fun τ => ?_)
    simp only [Function.comp_apply]
    exact actualProbePoint_snd_eq_probeOutput r θ
      (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2 τ
  -- Assemble via the M7 packaged theorem.
  exact lem_saturated_limit_S_of_primed_convergence r θ θ' h R.Ustar
    (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
    (saturatedE (saturatedC (deeperValueStream θ))
      (saturatedTailD (deeperValueStream θ)
        (trichotomyToSaturatedLabels r (m + 1) k R.labels))
      (saturatedKLayer (deeperValueStream θ)
        (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1))
    (firstLayerOtherValueSum θ h) (valueMatrix θ 0 h) (collapseMatrix θ 0)
    (collapsePrefix θ' (m + 1)) 1 (valueMatrix θ' 0 h)
    rfl (by rw [mul_one]) hAttn hAgree
    (fun x hx => Sif.t_pos x (hsub hx))
    (fun x hx => Sif.t_lt_one x (hsub hx))
    (fun x hx => Sif.point_on_quadric x (hsub hx))
    (fun x hx => Sif.pi_ne_zero x (hsub hx))
    (fun x hx a ha => hsep x (hsub hx) a ha)
    (fun x hx => hposθ' x (hsub hx))
    hUnprimed

/-! ## SUB-GOAL B — coefficient extraction, cancellation, and first-value identification

From the saturated-limit equality (SUB-GOAL A), the affine-in-`t` coefficient matrices of the
two saturated limit vectors are extracted (TeX `07c3-slices-first-values`,
`eq:v-coeff`/`eq:w-coeff`); the resulting `K = I` cancellation
(`SaturatedKCancellationData.value_eq`) identifies the selected first-layer value matrices.

The geometric coefficient extraction (M8 slices + probe freedom) is isolated as the
`IsSaturatedCoeffExtraction` residual; everything else here is discharged with real proofs. -/

/-- The affine-`t` coefficient matrix identities of the two saturated limit vectors,
`eq:v-coeff` and `eq:w-coeff`, packaged so the final `K = I` cancellation can be assembled.

`v_coeff` matches the `v`-coefficients (`M·C₁ = C'_{L:1}`); `w_coeff_linear` matches the
`t`-linear `w`-coefficients (`K·V = V'`); `w_coeff_const` matches the constant `w`-coefficients
(`M·S + E·(I+V) = C'_{L:1} - I - V'`). -/
structure SaturatedCoeffIdentities {m k d : Nat} (θ θ' : Params (m + 1) k d) (h : Fin k)
    (M E : Matrix (Fin d) (Fin d) ℝ) : Prop where
  v_coeff : M * collapseMatrix θ 0 = collapsePrefix θ' (m + 1)
  w_coeff_linear : saturatedTailK M E * valueMatrix θ 0 h = valueMatrix θ' 0 h
  w_coeff_const : M * firstLayerOtherValueSum θ h + E * (1 + valueMatrix θ 0 h)
    = collapsePrefix θ' (m + 1) - 1 - valueMatrix θ' 0 h

/-- **The `K = I` cancellation endpoint (TeX Step 6→7).**  The three affine-coefficient
identities force `V = V'`: assembling `K = M - E`, `V = V_h`, `V' = V'_h`, `B = I + V_h`,
`B' = I + V'_h` into `SaturatedKCancellationData` and applying `value_eq`. -/
theorem firstValue_eq_of_coeffIdentities {m k d : Nat} (θ θ' : Params (m + 1) k d)
    (h : Fin k) (M E : Matrix (Fin d) (Fin d) ℝ)
    (hc : SaturatedCoeffIdentities θ θ' h M E) :
    valueMatrix θ 0 h = valueMatrix θ' 0 h := by
  have hmaps_skip :
      saturatedTailK M E * (1 + valueMatrix θ 0 h) = 1 + valueMatrix θ' 0 h := by
    have hC1 : collapseMatrix θ 0
        = (1 + valueMatrix θ 0 h) + firstLayerOtherValueSum θ h := by
      rw [collapseMatrix_zero_eq_B_add_S θ h]; simp only [firstLayerUnsatB]
    have ha' : M * (1 + valueMatrix θ 0 h) + M * firstLayerOtherValueSum θ h
        = collapsePrefix θ' (m + 1) := by
      rw [← mul_add, ← hC1, hc.v_coeff]
    unfold saturatedTailK
    rw [sub_mul]
    calc M * (1 + valueMatrix θ 0 h) - E * (1 + valueMatrix θ 0 h)
        = (M * (1 + valueMatrix θ 0 h) + M * firstLayerOtherValueSum θ h)
          - (M * firstLayerOtherValueSum θ h + E * (1 + valueMatrix θ 0 h)) := by abel
      _ = collapsePrefix θ' (m + 1)
          - (collapsePrefix θ' (m + 1) - 1 - valueMatrix θ' 0 h) := by
            rw [ha', hc.w_coeff_const]
      _ = 1 + valueMatrix θ' 0 h := by abel
  have hcancel : SaturatedKCancellationData (saturatedTailK M E)
      (valueMatrix θ 0 h) (valueMatrix θ' 0 h)
      (1 + valueMatrix θ 0 h) (1 + valueMatrix θ' 0 h) :=
    { skip_unprimed := by abel
      skip_primed := by abel
      maps_value := hc.w_coeff_linear
      maps_skip := hmaps_skip }
  exact hcancel.value_eq

/-- **The isolated M9 coefficient-extraction residual.**  From the saturated-limit equality
on the trichotomy region `Ustar`, the M8 slice topology `lem_slices_S`, and the paper
nonvanishing hypothesis `hyp_w_nonzero_S`, the affine-in-`t` coefficient matrices coincide.
This is the sole geometric step of M9 not discharged in this file (TeX
`07c3-slices-first-values`); it is a general statement about the affine coefficients and is
strictly weaker than `prop:first-V`. -/
def IsSaturatedCoeffExtraction {m k d : Nat} (θ θ' : Params (m + 1) k d) (h : Fin k)
    (Ustar : Set (ProbePoint d × ℝ)) (M E : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  lem_saturated_limit_S Ustar
      (fun x => unprimedSaturatedLimitVector M E (saturatedTailK M E)
        (firstLayerOtherValueSum θ h) (valueMatrix θ 0 h) (collapseMatrix θ 0) x.2 x.1)
      (fun x => primedSaturatedLimitVector (collapsePrefix θ' (m + 1)) 1
        (valueMatrix θ' 0 h) x.2 x.1) →
    lem_slices_S (attentionMatrix θ 0 h) Ustar →
    hyp_w_nonzero_S Ustar (valueMatrix θ' 0 h) →
    SaturatedCoeffIdentities θ θ' h M E

/-- **K07C.M9 coefficient extraction discharged from `det (A_h) ≠ 0` (quadric rigidity).**

The isolated residual `IsSaturatedCoeffExtraction` is proved for *arbitrary* affine coefficient
matrices `M E`, using only the honest genericity inputs `2 ≤ d` and `det (attentionMatrix θ 0 h) ≠ 0`.

The saturated-limit equality says the affine-in-`t` difference vector
`δ_t(w,v) = unprimed − primed` vanishes on `Ustar`.  On each fixed-`t` slice
`Ustar(t) = W ∩ {wᵀ A_h v = 0}` (M8 `slice_relatively_open`) the difference is a degree-1 form
in `(w,v)` vanishing on a relatively-open subset of the nondegenerate quadric
(`det A_h ≠ 0`); `lem_linear_quadric_rigidity` (K04F) forces its `v`-coefficient matrix
`M·C₁ − C'_{L:1}` and its `w`-coefficient matrix to vanish.  Evaluating the `w`-coefficient at
the two distinct parameters `t₁ ≠ t₂` (M8 `two_parameters`) and subtracting separates the
`t`-linear part (`K·V = V'`, `eq:w-coeff` linear) from the constant part (`eq:w-coeff` const);
the `v`-coefficient gives `eq:v-coeff`.  The nonvanishing of `w` on slices (`nonzero_on_slices`
from `hyp_w_nonzero_S`) supplies the quadric base point `w₀ ≠ 0`. -/
theorem isSaturatedCoeffExtraction_of_det_ne_zero {m k d : Nat}
    (θ θ' : Params (m + 1) k d) (h : Fin k) (Ustar : Set (ProbePoint d × ℝ))
    (M E : Matrix (Fin d) (Fin d) ℝ) (hd : 2 ≤ d)
    (hdet : (attentionMatrix θ 0 h).det ≠ 0) :
    IsSaturatedCoeffExtraction θ θ' h Ustar M E := by
  intro heq hslices hwnz
  set A := attentionMatrix θ 0 h with hAdef
  set Vh := valueMatrix θ 0 h with hVhdef
  set Vh' := valueMatrix θ' 0 h with hVh'def
  set Sh := firstLayerOtherValueSum θ h with hShdef
  set C1 := collapseMatrix θ 0 with hC1def
  set Mp := collapsePrefix θ' (m + 1) with hMpdef
  set K := saturatedTailK M E with hKdef
  -- **Per-parameter quadric rigidity.**  For every admissible slice time `t`, the `v`-coefficient
  -- matrix and the (t-dependent) `w`-coefficient matrix of the saturated-limit difference vanish.
  have rigidity : ∀ t : ℝ, t ∈ saturatedParameterSet Ustar →
      (M * C1 - Mp = 0) ∧
      ((M * Sh + E * (1 + Vh) + t • (K * Vh)) - (Mp - 1 - Vh' + t • Vh') = 0) := by
    intro t htparam
    obtain ⟨ht0, ht1, hslice_ne⟩ := id htparam
    obtain ⟨p0, hp0⟩ := hslice_ne
    obtain ⟨W, hWopen, hWeq⟩ := hslices.slice_relatively_open t ht0 ht1
    have hp0' : p0 ∈ W ∩ saturatedFirstHeadQuadric A := hWeq ▸ hp0
    have hw0 : p0.1 ≠ 0 := hslices.nonzero_on_slices Vh' hwnz t htparam p0 hp0
    have hquad0 : matrixBilin A p0.1 p0.2 = 0 := hp0'.2
    have hvanish : ∀ p : ProbePoint d, p ∈ W → matrixBilin A p.1 p.2 = 0 →
        (M * C1 - Mp) *ᵥ p.2
          + ((M * Sh + E * (1 + Vh) + t • (K * Vh)) - (Mp - 1 - Vh' + t • Vh')) *ᵥ p.1 = 0 := by
      intro p hpW hpQ
      have hmem : (p, t) ∈ Ustar := by
        have hps : p ∈ saturatedSlice Ustar t := by rw [hWeq]; exact ⟨hpW, hpQ⟩
        exact hps
      have heqpt : unprimedSaturatedLimitVector M E K Sh Vh C1 t p
          = primedSaturatedLimitVector Mp 1 Vh' t p := heq (p, t) hmem
      have key : (M * C1 - Mp) *ᵥ p.2
            + ((M * Sh + E * (1 + Vh) + t • (K * Vh)) - (Mp - 1 - Vh' + t • Vh')) *ᵥ p.1
          = unprimedSaturatedLimitVector M E K Sh Vh C1 t p
            - primedSaturatedLimitVector Mp 1 Vh' t p := by
        simp only [unprimedSaturatedLimitVector, primedSaturatedLimitVector, mul_one,
          Matrix.add_mulVec, Matrix.sub_mulVec]
        abel
      rw [key, heqpt, sub_self]
    exact lem_linear_quadric_rigidity hd A (M * C1 - Mp)
      ((M * Sh + E * (1 + Vh) + t • (K * Vh)) - (Mp - 1 - Vh' + t • Vh'))
      p0.1 p0.2 W hdet hw0 hquad0 hWopen hp0'.1 hvanish
  -- **Two-parameter separation.**  Use two distinct admissible times to split the affine
  -- `w`-coefficient into its linear and constant parts.
  obtain ⟨t1, t2, ht1, ht2, hne⟩ := hslices.two_parameters
  obtain ⟨hCv, hE1⟩ := rigidity t1 ht1
  obtain ⟨_, hE2⟩ := rigidity t2 ht2
  have hdiff : (t1 - t2) • (K * Vh - Vh')
      = ((M * Sh + E * (1 + Vh) + t1 • (K * Vh)) - (Mp - 1 - Vh' + t1 • Vh'))
        - ((M * Sh + E * (1 + Vh) + t2 • (K * Vh)) - (Mp - 1 - Vh' + t2 • Vh')) := by
    match_scalars <;> ring
  have hQscaled : (t1 - t2) • (K * Vh - Vh') = 0 := by rw [hdiff, hE1, hE2, sub_self]
  have hne' : t1 - t2 ≠ 0 := sub_ne_zero.mpr hne
  have hQ0 : K * Vh - Vh' = 0 := by
    have h2 : (t1 - t2)⁻¹ • ((t1 - t2) • (K * Vh - Vh')) = 0 := by rw [hQscaled, smul_zero]
    rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at h2
  have wlin : K * Vh = Vh' := sub_eq_zero.mp hQ0
  -- The constant part, after substituting the linear identity `K·V = V'`.
  have hE1' := hE1
  rw [wlin] at hE1'
  have wconst : M * Sh + E * (1 + Vh) = Mp - 1 - Vh' := by
    have hkey : M * Sh + E * (1 + Vh) - (Mp - 1 - Vh')
        = (M * Sh + E * (1 + Vh) + t1 • Vh') - (Mp - 1 - Vh' + t1 • Vh') := by abel
    exact sub_eq_zero.mp (by rw [hkey]; exact hE1')
  exact ⟨sub_eq_zero.mp hCv, wlin, wconst⟩

/-- First-layer head relabeling reads off the source attention at the permuted head. -/
@[simp] theorem attentionMatrix_relabelFirstLayer_zero {m k d : Nat}
    (θ : Params (m + 1) k d) (σ : Equiv.Perm (Fin k)) (h : Fin k) :
    attentionMatrix (relabelFirstLayer θ σ) 0 h = attentionMatrix θ 0 (σ h) := by
  simp only [Params.attentionMatrix_apply, relabelFirstLayer_zero]

/-- First-layer head relabeling reads off the source value at the permuted head. -/
@[simp] theorem valueMatrix_relabelFirstLayer_zero {m k d : Nat}
    (θ : Params (m + 1) k d) (σ : Equiv.Perm (Fin k)) (h : Fin k) :
    valueMatrix (relabelFirstLayer θ σ) 0 h = valueMatrix θ 0 (σ h) := by
  simp only [Params.valueMatrix_apply, relabelFirstLayer_zero]

/-- **M9 for a single (relabeled) head.**  Combines SUB-GOAL A (the saturated-limit
equality), the M8 slice topology restricted to the trichotomy region, the paper nonvanishing
hypothesis, and the isolated coefficient-extraction residual `hextract` to identify the
selected first-layer value matrix `V_h = V'_h`. -/
theorem firstValue_matched_of_witnesses
    {m k d r : Nat} (θ θ' : Params (m + 1) k d) (h : Fin k)
    (D : SignRegionData θ h)
    (R : TrichotomyResult (dialPredicatesWithEstimate r θ h) (dialFormalData r θ h)
      D.region (deeperHeadOrder (m + 1) k))
    (hsep : ∀ x ∈ D.region, ∀ b : Fin k, b ≠ h →
      0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2)
    (hAttn : attentionMatrix θ 0 = attentionMatrix θ' 0)
    (hAgree : ∀ (w v : Vec d) (τ : ℝ), 0 < τ →
      probeOutput r θ w v τ = probeOutput r θ' w v τ)
    (hposθ' : ∀ x ∈ D.region, ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ a : Fin k,
      0 < matrixBilin (attentionMatrix θ' ⟨n, hn⟩ a)
        (dialSatPoint θ' h x.1 x.2 n).1 (dialSatPoint θ' h x.1 x.2 n).2)
    (hwnz : hyp_w_nonzero_S R.Ustar (valueMatrix θ' 0 h))
    (hextract : IsSaturatedCoeffExtraction θ θ' h R.Ustar
      (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
      (saturatedE (saturatedC (deeperValueStream θ))
        (saturatedTailD (deeperValueStream θ)
          (trichotomyToSaturatedLabels r (m + 1) k R.labels))
        (saturatedKLayer (deeperValueStream θ)
          (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1))) :
    valueMatrix θ 0 h = valueMatrix θ' 0 h := by
  have heq := saturatedLimit_pointwise_eq θ θ' h D R hsep hAttn hAgree hposθ'
  have htop : SignRegionTopologyStatement (attentionMatrix θ 0) (valueMatrix θ 0) h R.Ustar :=
    SignRegionTopologyStatement.restrict (signRegionData_signRegionTopologyStatement D)
      R.region_subset_base R.region_nonempty R.region_connected R.region_relativelyOpen
  have hslices : lem_slices_S (attentionMatrix θ 0 h) R.Ustar :=
    lem_slices_S_of_signRegionTopology htop
  exact firstValue_eq_of_coeffIdentities θ θ' h _ _ (hextract heq hslices hwnz)

/-- Bundled per-target-head honest inputs for `prop:first-V`, phrased for the K06C-relabeled
source `relabelFirstLayer θ σ`.  Each field is one of the "allowed honest inputs": the
genericity sign-region witness (`data`), the K07B trichotomy result (`trich`), first-layer
separation (`sep`), primed deeper-slope saturation (`pos`), the paper nonvanishing hypothesis
(`wnz`), and the isolated coefficient-extraction residual (`extract`). -/
structure FirstValueData {m k d r : Nat} (θ θ' : Params (m + 1) k d)
    (σ : Equiv.Perm (Fin k)) where
  data : ∀ h : Fin k, SignRegionData (relabelFirstLayer θ σ) h
  trich : ∀ h : Fin k,
    TrichotomyResult (dialPredicatesWithEstimate r (relabelFirstLayer θ σ) h)
      (dialFormalData r (relabelFirstLayer θ σ) h) (data h).region
      (deeperHeadOrder (m + 1) k)
  sep : ∀ h : Fin k, ∀ x ∈ (data h).region, ∀ b : Fin k, b ≠ h →
    0 < matrixBilin (attentionMatrix (relabelFirstLayer θ σ) 0 b) x.1.1 x.1.2
  pos : ∀ h : Fin k, ∀ x ∈ (data h).region, ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) →
    ∀ a : Fin k, 0 < matrixBilin (attentionMatrix θ' ⟨n, hn⟩ a)
      (dialSatPoint θ' h x.1 x.2 n).1 (dialSatPoint θ' h x.1 x.2 n).2
  wnz : ∀ h : Fin k, hyp_w_nonzero_S (trich h).Ustar (valueMatrix θ' 0 h)
  extract : ∀ h : Fin k, IsSaturatedCoeffExtraction (relabelFirstLayer θ σ) θ' h
    (trich h).Ustar
    (layerProduct (saturatedC (deeperValueStream (relabelFirstLayer θ σ))) (m + 1) 2)
    (saturatedE (saturatedC (deeperValueStream (relabelFirstLayer θ σ)))
      (saturatedTailD (deeperValueStream (relabelFirstLayer θ σ))
        (trichotomyToSaturatedLabels r (m + 1) k (trich h).labels))
      (saturatedKLayer (deeperValueStream (relabelFirstLayer θ σ))
        (trichotomyToSaturatedLabels r (m + 1) k (trich h).labels)) (m + 1))

/-- **Determinant-genericity builder for `FirstValueData`.**  The isolated coefficient-extraction
field `extract` is no longer an independent honest input: it is discharged for every head by
`isSaturatedCoeffExtraction_of_det_ne_zero` (quadric rigidity) from `2 ≤ d` and the honest
first-layer nonsingularity genericity fact `det (attentionMatrix θ 0 a) ≠ 0` for all heads `a`
(the relabeled first-head attention is `attentionMatrix θ 0 (σ h)`, so ranging over all heads
covers the permuted selection).  No other field is weakened. -/
noncomputable def firstValueData_of_det {m k d r : Nat} (θ θ' : Params (m + 1) k d)
    (σ : Equiv.Perm (Fin k)) (hd : 2 ≤ d)
    (hdet : ∀ a : Fin k, (attentionMatrix θ 0 a).det ≠ 0)
    (data : ∀ h : Fin k, SignRegionData (relabelFirstLayer θ σ) h)
    (trich : ∀ h : Fin k,
      TrichotomyResult (dialPredicatesWithEstimate r (relabelFirstLayer θ σ) h)
        (dialFormalData r (relabelFirstLayer θ σ) h) (data h).region
        (deeperHeadOrder (m + 1) k))
    (sep : ∀ h : Fin k, ∀ x ∈ (data h).region, ∀ b : Fin k, b ≠ h →
      0 < matrixBilin (attentionMatrix (relabelFirstLayer θ σ) 0 b) x.1.1 x.1.2)
    (pos : ∀ h : Fin k, ∀ x ∈ (data h).region, ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) →
      ∀ a : Fin k, 0 < matrixBilin (attentionMatrix θ' ⟨n, hn⟩ a)
        (dialSatPoint θ' h x.1 x.2 n).1 (dialSatPoint θ' h x.1 x.2 n).2)
    (wnz : ∀ h : Fin k, hyp_w_nonzero_S (trich h).Ustar (valueMatrix θ' 0 h)) :
    FirstValueData (r := r) θ θ' σ where
  data := data
  trich := trich
  sep := sep
  pos := pos
  wnz := wnz
  extract := fun h =>
    isSaturatedCoeffExtraction_of_det_ne_zero (relabelFirstLayer θ σ) θ' h (trich h).Ustar _ _ hd
      (by rw [attentionMatrix_relabelFirstLayer_zero]; exact hdet (σ h))

/-- **K07C.M9 core (`eq:first-V`).**  The first-layer value matching, in target-to-source
orientation, for the canonical K06C first-attention permutation
`σ = (step1CommonFirstGates hr H).sigma`, from the standing hypotheses `H`, `hr` and the
bundled per-head honest witnesses `W`.  The common first-attention `hAttn` and probe-output
agreement `hAgree` for the relabeled source are discharged internally from `H`. -/
theorem firstLayerValuesMatched_of_firstValueData {m k d r : Nat}
    {θ θ' : Params (m + 1) k d}
    (hr : 1 < r) (H : Step1.Step1StandingHypotheses r θ θ')
    (W : FirstValueData (r := r) θ θ' (Step1.step1CommonFirstGates hr H).sigma) :
    firstLayerValuesMatched (Nat.succ_pos m) θ θ'
      (Step1.step1CommonFirstGates hr H).sigma := by
  intro h
  set σ := (Step1.step1CommonFirstGates hr H).sigma with hσ
  have hAttn : attentionMatrix (relabelFirstLayer θ σ) 0 = attentionMatrix θ' 0 := by
    funext hh
    rw [attentionMatrix_relabelFirstLayer_zero]
    exact (Step1.step1CommonFirstGates hr H).attention_eq hh
  have hAgree : ∀ (w v : Vec d) (τ : ℝ), 0 < τ →
      probeOutput r (relabelFirstLayer θ σ) w v τ = probeOutput r θ' w v τ := by
    intro w v τ hτ
    exact (probeOutputEquality_relabelFirstLayer H.seq_pos θ σ (w, v) τ hτ).trans
      (H.probeOutputEquality (w, v) τ hτ)
  have hval : valueMatrix (relabelFirstLayer θ σ) 0 h = valueMatrix θ' 0 h :=
    firstValue_matched_of_witnesses (relabelFirstLayer θ σ) θ' h (W.data h) (W.trich h)
      (W.sep h) hAttn hAgree (W.pos h) (W.wnz h) (W.extract h)
  rw [valueMatrix_relabelFirstLayer_zero] at hval
  exact hval

/-- **K07C.M9 (`prop:first-V.S`).**  Assembles the first-layer value identification structure
`prop_first_V_S`, reusing the K06C attention permutation `σ` (no independent value
permutation is introduced). -/
noncomputable def prop_first_V_S_of_firstValueData {m k d r : Nat}
    {θ θ' : Params (m + 1) k d}
    (hr : 1 < r) (H : Step1.Step1StandingHypotheses r θ θ')
    (W : FirstValueData (r := r) θ θ' (Step1.step1CommonFirstGates hr H).sigma) :
    prop_first_V_S (Nat.succ_pos m) θ θ' where
  sigma := (Step1.step1CommonFirstGates hr H).sigma
  values_matched := firstLayerValuesMatched_of_firstValueData hr H W

/-- **The K07C→K08 endgame adapter.**  Exposes the peeling value-matching predicate
`firstLayerValuesMatchedForPeeling θ θ' σ` for the canonical K06C first-attention permutation
`σ = (step1CommonFirstGates hr H).sigma`, consuming the same bundled witnesses.  This is the
object fed to `firstLayerPeelingData_of_valuesMatched` in the L8 rewire. -/
theorem prop_first_V {m k d r : Nat} {θ θ' : Params (m + 1) k d}
    (hr : 1 < r) (H : Step1.Step1StandingHypotheses r θ θ')
    (W : FirstValueData (r := r) θ θ' (Step1.step1CommonFirstGates hr H).sigma) :
    firstLayerValuesMatchedForPeeling θ θ' (Step1.step1CommonFirstGates hr H).sigma :=
  firstLayerValuesMatchedForPeeling_of_firstLayerValuesMatched
    (firstLayerValuesMatched_of_firstValueData hr H W)

/-! ## Path-T: BUNDLE-FREE `prop:first-V` from TARGET genericity via transport

All the honest per-target-head inputs of `FirstValueData` are reconstructed from a *target*
sign-region witness `D' : SignRegionData θ' h` (obtained from `θ'` genericity) transported
onto the K06C-relabeled source `relabelFirstLayer θ σ` across the common first-layer
attention equality `hAttn : attentionMatrix (relabelFirstLayer θ σ) 0 = attentionMatrix θ' 0`.
The value-matrix parameter `V'` of `SignRegionInterface`/`SignRegionTopologyStatement` is never
consumed, so the target witness is reused verbatim; only the selected-head attention is
transported.  This collapses the sign-region/trichotomy/separation/nonvanishing data to "reuse
`D'`", and lets `prop_first_V_of_standing` be derived from the standing hypotheses alone. -/

/-! ### Lanes B/D — interface/topology consumer variants over a free value-matrix `V'` -/

/-- **SUB-GOAL A over a free value-matrix parameter.**  Same as `saturatedLimit_pointwise_eq`
but consuming an abstract region `U` together with a `SignRegionInterface` carrying a *free*
value-matrix family `V'` (rather than a full `SignRegionData θ h`).  The `V'` parameter is
never read, so this is a verbatim generalization. -/
theorem saturatedLimit_pointwise_eq'
    {m k d r : Nat} (θ θ' : Params (m + 1) k d) (h : Fin k)
    {V' : Fin k → Matrix (Fin d) (Fin d) ℝ}
    (U : Set (ProbePair d × ℝ))
    (Sif : SignRegionInterface (attentionMatrix θ 0) V' h U)
    (R : TrichotomyResult (dialPredicatesWithEstimate r θ h) (dialFormalData r θ h)
      U (deeperHeadOrder (m + 1) k))
    (hsep : ∀ x ∈ U, ∀ b : Fin k, b ≠ h →
      0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2)
    (hAttn : attentionMatrix θ 0 = attentionMatrix θ' 0)
    (hAgree : ∀ (w v : Vec d) (τ : ℝ), 0 < τ →
      probeOutput r θ w v τ = probeOutput r θ' w v τ)
    (hposθ' : ∀ x ∈ U, ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ a : Fin k,
      0 < matrixBilin (attentionMatrix θ' ⟨n, hn⟩ a)
        (dialSatPoint θ' h x.1 x.2 n).1 (dialSatPoint θ' h x.1 x.2 n).2) :
    lem_saturated_limit_S R.Ustar
      (fun x => unprimedSaturatedLimitVector
        (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
        (saturatedE (saturatedC (deeperValueStream θ))
          (saturatedTailD (deeperValueStream θ)
            (trichotomyToSaturatedLabels r (m + 1) k R.labels))
          (saturatedKLayer (deeperValueStream θ)
            (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1))
        (saturatedTailK
          (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
          (saturatedE (saturatedC (deeperValueStream θ))
            (saturatedTailD (deeperValueStream θ)
              (trichotomyToSaturatedLabels r (m + 1) k R.labels))
            (saturatedKLayer (deeperValueStream θ)
              (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1)))
        (firstLayerOtherValueSum θ h) (valueMatrix θ 0 h) (collapseMatrix θ 0) x.2 x.1)
      (fun x => primedSaturatedLimitVector (collapsePrefix θ' (m + 1)) 1
        (valueMatrix θ' 0 h) x.2 x.1) := by
  have hsub : R.Ustar ⊆ U := R.region_subset_base
  -- The θ-side (unprimed) observable convergence residual `hUnprimed`.
  have hUnprimed : ∀ x ∈ R.Ustar,
      Tendsto (fun τ => probeOutput r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2 τ)
        atTop (𝓝 (unprimedSaturatedLimitVector
          (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
          (saturatedE (saturatedC (deeperValueStream θ))
            (saturatedTailD (deeperValueStream θ)
              (trichotomyToSaturatedLabels r (m + 1) k R.labels))
            (saturatedKLayer (deeperValueStream θ)
              (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1))
          (saturatedTailK
            (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
            (saturatedE (saturatedC (deeperValueStream θ))
              (saturatedTailD (deeperValueStream θ)
                (trichotomyToSaturatedLabels r (m + 1) k R.labels))
              (saturatedKLayer (deeperValueStream θ)
                (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1)))
          (firstLayerOtherValueSum θ h) (valueMatrix θ 0 h) (collapseMatrix θ 0)
          x.2 x.1)) := by
    intro x hx
    -- α-branch slope estimate for the *final* trichotomy result.
    have halpha : ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ (a : Fin k),
        R.toDialPredicates.labels { layer := n + 1, head := (a : Nat) + 1 } =
            TrichotomyLabel.alpha →
          Tendsto (fun τ => τ * actualProbeSlope r θ
            (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
            (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2
            τ ⟨n, hn⟩ a) atTop (𝓝 0) := by
      intro n hnpos hn a hlabel
      have hz : zeroDialForm (phiHeadOfDeeperHead r θ h
          ({ layer := n + 1, head := (a : Nat) + 1 } : DeeperHead) R.labels) :=
        R.toDialPredicates.zeroDialForm_of_label_alpha
          (succ_head_mem_deeperHeadOrder hnpos hn a) hlabel
      have hsep_pt : ∀ b : Fin k, b ≠ h →
          0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2 :=
        fun b hb => hsep x (hsub hx) b hb
      have hprior : ∀ (q : Nat), 1 ≤ q → q < n → (hq' : q < m + 1) → ∀ (b : Fin k),
          EventuallyExpClose (fun τ => actualProbeGate r θ
            (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
            (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2 τ ⟨q, hq'⟩ b)
            (trichotomyToSaturatedLabels r (m + 1) k R.labels (q + 1) b) := by
        intro q hqpos _hqn hq' b
        have hmemq : ({ layer := q + 1, head := (b : Nat) + 1 } : DeeperHead) ∈
            processedPrefix (deeperHeadOrder (m + 1) k)
              ((deeperHeadOrder (m + 1) k).length) := by
          rw [processedPrefix, List.take_length]
          exact succ_head_mem_deeperHeadOrder hqpos hq' b
        exact eventuallyExpClose_of_expCloseTo
          (R.estimate.gate hqpos hq' b hmemq x hx)
      exact tendsto_tau_mul_actualProbeSlope_zero_of_zeroDialForm_sep
        θ h R.labels x.1 x.2 n hnpos hn a hz hsep_pt hprior
    have hpt := R.toDialPredicates.tendsto_satZetaActualProbePoint_of_alpha_estimate
      (p := x.1) (t := x.2) hx halpha
      (Sif.t_pos x (hsub hx)) (Sif.t_lt_one x (hsub hx))
      (Sif.point_on_quadric x (hsub hx)) (Sif.pi_ne_zero x (hsub hx))
      (fun a ha => hsep x (hsub hx) a ha) (m + 1) le_rfl
    simp only [TrichotomyResult.toDialPredicates_labels] at hpt
    have hsnd := (continuous_snd.tendsto
      (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k R.labels)
        x.1 x.2 (m + 1))).comp hpt
    have hval : (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k R.labels)
        x.1 x.2 (m + 1)).2 = unprimedSaturatedLimitVector
          (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
          (saturatedE (saturatedC (deeperValueStream θ))
            (saturatedTailD (deeperValueStream θ)
              (trichotomyToSaturatedLabels r (m + 1) k R.labels))
            (saturatedKLayer (deeperValueStream θ)
              (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1))
          (saturatedTailK
            (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
            (saturatedE (saturatedC (deeperValueStream θ))
              (saturatedTailD (deeperValueStream θ)
                (trichotomyToSaturatedLabels r (m + 1) k R.labels))
              (saturatedKLayer (deeperValueStream θ)
                (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1)))
          (firstLayerOtherValueSum θ h) (valueMatrix θ 0 h) (collapseMatrix θ 0)
          x.2 x.1 := by
      rw [satZetaPoint_snd θ h (trichotomyToSaturatedLabels r (m + 1) k R.labels)
        x.1 x.2 (m + 1) (Nat.le_add_left 1 m) le_rfl]
      simp only [firstLayerUnsatB]
      rw [← unprimedSaturatedLimitVector_eq_mulVec
        (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
        (saturatedE (saturatedC (deeperValueStream θ))
          (saturatedTailD (deeperValueStream θ)
            (trichotomyToSaturatedLabels r (m + 1) k R.labels))
          (saturatedKLayer (deeperValueStream θ)
            (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1))
        (firstLayerOtherValueSum θ h) (valueMatrix θ 0 h) (collapseMatrix θ 0)
        x.2 x.1.1 x.1.2]
    rw [hval] at hsnd
    refine hsnd.congr (fun τ => ?_)
    simp only [Function.comp_apply]
    exact actualProbePoint_snd_eq_probeOutput r θ
      (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2 τ
  -- Assemble via the M7 packaged theorem.
  exact lem_saturated_limit_S_of_primed_convergence r θ θ' h R.Ustar
    (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
    (saturatedE (saturatedC (deeperValueStream θ))
      (saturatedTailD (deeperValueStream θ)
        (trichotomyToSaturatedLabels r (m + 1) k R.labels))
      (saturatedKLayer (deeperValueStream θ)
        (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1))
    (firstLayerOtherValueSum θ h) (valueMatrix θ 0 h) (collapseMatrix θ 0)
    (collapsePrefix θ' (m + 1)) 1 (valueMatrix θ' 0 h)
    rfl (by rw [mul_one]) hAttn hAgree
    (fun x hx => Sif.t_pos x (hsub hx))
    (fun x hx => Sif.t_lt_one x (hsub hx))
    (fun x hx => Sif.point_on_quadric x (hsub hx))
    (fun x hx => Sif.pi_ne_zero x (hsub hx))
    (fun x hx a ha => hsep x (hsub hx) a ha)
    (fun x hx => hposθ' x (hsub hx))
    hUnprimed

/-- **M9 for a single head over a free value-matrix parameter.**  Same as
`firstValue_matched_of_witnesses` but consuming an abstract region `U` and a
`SignRegionTopologyStatement` carrying a *free* value-matrix family `V'`. -/
theorem firstValue_matched_of_witnesses'
    {m k d r : Nat} (θ θ' : Params (m + 1) k d) (h : Fin k)
    {V' : Fin k → Matrix (Fin d) (Fin d) ℝ}
    (U : Set (ProbePair d × ℝ))
    (htop : SignRegionTopologyStatement (attentionMatrix θ 0) V' h U)
    (R : TrichotomyResult (dialPredicatesWithEstimate r θ h) (dialFormalData r θ h)
      U (deeperHeadOrder (m + 1) k))
    (hsep : ∀ x ∈ U, ∀ b : Fin k, b ≠ h →
      0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2)
    (hAttn : attentionMatrix θ 0 = attentionMatrix θ' 0)
    (hAgree : ∀ (w v : Vec d) (τ : ℝ), 0 < τ →
      probeOutput r θ w v τ = probeOutput r θ' w v τ)
    (hposθ' : ∀ x ∈ U, ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ a : Fin k,
      0 < matrixBilin (attentionMatrix θ' ⟨n, hn⟩ a)
        (dialSatPoint θ' h x.1 x.2 n).1 (dialSatPoint θ' h x.1 x.2 n).2)
    (hwnz : hyp_w_nonzero_S R.Ustar (valueMatrix θ' 0 h))
    (hextract : IsSaturatedCoeffExtraction θ θ' h R.Ustar
      (layerProduct (saturatedC (deeperValueStream θ)) (m + 1) 2)
      (saturatedE (saturatedC (deeperValueStream θ))
        (saturatedTailD (deeperValueStream θ)
          (trichotomyToSaturatedLabels r (m + 1) k R.labels))
        (saturatedKLayer (deeperValueStream θ)
          (trichotomyToSaturatedLabels r (m + 1) k R.labels)) (m + 1))) :
    valueMatrix θ 0 h = valueMatrix θ' 0 h := by
  have heq := saturatedLimit_pointwise_eq' θ θ' h U htop.interface R hsep hAttn hAgree hposθ'
  have htopUstar : SignRegionTopologyStatement (attentionMatrix θ 0) V' h R.Ustar :=
    htop.restrict R.region_subset_base R.region_nonempty R.region_connected
      R.region_relativelyOpen
  have hslices : lem_slices_S (attentionMatrix θ 0 h) R.Ustar :=
    lem_slices_S_of_signRegionTopology htopUstar
  exact firstValue_eq_of_coeffIdentities θ θ' h _ _ (hextract heq hslices hwnz)

/-! ### Lane B — source witness builders from a target `SignRegionData θ' h` -/

/-- Transport a target sign-region interface onto the relabeled source across the common
first-layer attention equality, keeping the target value-matrix family free. -/
theorem sourceFirstSignRegionInterface {m k d : Nat} (θ : Params (m + 1) k d)
    (σ : Equiv.Perm (Fin k)) (θ' : Params (m + 1) k d) (h : Fin k)
    (D' : SignRegionData θ' h)
    (hAttn : attentionMatrix (relabelFirstLayer θ σ) 0 = attentionMatrix θ' 0) :
    SignRegionInterface (attentionMatrix (relabelFirstLayer θ σ) 0) (valueMatrix θ' 0) h
      D'.region :=
  SignRegionInterface.congr_attention (congrFun hAttn h)
    (signRegionData_signRegionInterface D')

/-- Transport a target sign-region topology statement onto the relabeled source across the
common first-layer attention equality, keeping the target value-matrix family free. -/
theorem sourceFirstSignRegionTopology {m k d : Nat} (θ : Params (m + 1) k d)
    (σ : Equiv.Perm (Fin k)) (θ' : Params (m + 1) k d) (h : Fin k)
    (D' : SignRegionData θ' h)
    (hAttn : attentionMatrix (relabelFirstLayer θ σ) 0 = attentionMatrix θ' 0) :
    SignRegionTopologyStatement (attentionMatrix (relabelFirstLayer θ σ) 0) (valueMatrix θ' 0)
      h D'.region :=
  SignRegionTopologyStatement.congr_attention (congrFun hAttn h)
    (signRegionData_signRegionTopologyStatement D')

/-- The relabeled source satisfies the three first-head rigidity facts: `det`/`sym`
nonvanishing come from target `Regularity` transported across `hAttn`; `value_ne` comes from
the K06C matched-activity `σ h ∈ activeHeads θ 0` read through the head relabeling. -/
theorem sourceFirstHeadRigidityFacts {m k d r : Nat} (θ : Params (m + 1) k d)
    (σ : Equiv.Perm (Fin k)) (θ' : Params (m + 1) k d) (h : Fin k)
    (hAttn : attentionMatrix (relabelFirstLayer θ σ) 0 = attentionMatrix θ' 0)
    (hreg : Regularity r θ') (hact : σ h ∈ activeHeads θ (0 : Fin (m + 1))) :
    FirstHeadRigidityFacts (relabelFirstLayer θ σ) h where
  det_ne := by rw [congrFun hAttn h]; exact hreg.det_attention_ne_zero 0 h
  sym_ne := by rw [congrFun hAttn h]; exact Regularity.symAttentionMatrix_ne_zero hreg 0 h
  value_ne := by
    rw [valueMatrix_relabelFirstLayer_zero]
    exact (mem_activeHeads_iff_valueMatrix_ne_zero θ 0 (σ h)).mp hact

/-- **The `pos` discharge (deeper-slope saturation from `level_positive`).**  For a
`SignRegionData θ h`, on any base point of its region every deeper layer-`≥ 1` saturated-point
slope is strictly positive, identified with the genericity deeper-level margin
`signRegionLevelValue` via GAP3 (`matrixBilin_dialSatPoint_eq_levelValue`).  This is exactly
the per-point content extracted inside `deeperSlopeMargins_of_signRegionData`. -/
theorem levelSlope_pos_of_signRegionData {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (D : SignRegionData θ h) {x : SignRegionPoint d} (hx : x ∈ D.region)
    (n : Nat) (hn1 : 1 ≤ n) (hn : n < m + 1) (a : Fin k) :
    0 < matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
      (dialSatPoint θ h x.1 x.2 n).1 (dialSatPoint θ h x.1 x.2 n).2 := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
  have hjm : q < m := Nat.lt_of_succ_lt_succ hn
  have hlayereq : (⟨q + 1, hn⟩ : Fin (m + 1)) = laterLayer ⟨q, hjm⟩ := by
    apply Fin.ext; simp [laterLayer]
  rw [hlayereq, matrixBilin_dialSatPoint_eq_levelValue]
  exact D.level_positive x hx ⟨q, hjm⟩ a

/-- Choose a target sign-region witness for every first-layer head from the target's
`AnchorCertificate` (extracted from `RecursiveGeneric`), via `lem_sign_region_statement_proof`. -/
noncomputable def standingFirstSignRegionData {m k d r : Nat} {θ' : Params (m + 1) k d}
    (hgen : RecursiveGeneric r (m + 1) k d θ') (h : Fin k) : SignRegionData θ' h :=
  Classical.choice
    (lem_sign_region_statement_proof θ' h ((hgen.2 : CurrentGenericClauses r θ').2.2.2 h))

/-! ### Lane D/E — the bundle-free per-head data and its standing-hypotheses builder -/

/-- **Bundle-free per-target-head honest inputs for `prop:first-V`.**  Unlike `FirstValueData`,
every field is phrased with the *target* value-matrix family `valueMatrix θ' 0` carried free in
the `SignRegionTopologyStatement`, so all witnesses can be produced from a single target
sign-region witness `D' : SignRegionData θ' h` transported onto the relabeled source.  The
separation (`sep`) and nonvanishing (`wnz`) inputs are *derived*, not stored. -/
structure FirstValueDataT {m k d r : Nat} (θ θ' : Params (m + 1) k d)
    (σ : Equiv.Perm (Fin k)) where
  region : Fin k → Set (ProbePair d × ℝ)
  topology : ∀ h : Fin k,
    SignRegionTopologyStatement (attentionMatrix (relabelFirstLayer θ σ) 0)
      (valueMatrix θ' 0) h (region h)
  trich : ∀ h : Fin k,
    TrichotomyResult (dialPredicatesWithEstimate r (relabelFirstLayer θ σ) h)
      (dialFormalData r (relabelFirstLayer θ σ) h) (region h)
      (deeperHeadOrder (m + 1) k)
  pos : ∀ h : Fin k, ∀ x ∈ region h, ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) →
    ∀ a : Fin k, 0 < matrixBilin (attentionMatrix θ' ⟨n, hn⟩ a)
      (dialSatPoint θ' h x.1 x.2 n).1 (dialSatPoint θ' h x.1 x.2 n).2
  extract : ∀ h : Fin k, IsSaturatedCoeffExtraction (relabelFirstLayer θ σ) θ' h
    (trich h).Ustar
    (layerProduct (saturatedC (deeperValueStream (relabelFirstLayer θ σ))) (m + 1) 2)
    (saturatedE (saturatedC (deeperValueStream (relabelFirstLayer θ σ)))
      (saturatedTailD (deeperValueStream (relabelFirstLayer θ σ))
        (trichotomyToSaturatedLabels r (m + 1) k (trich h).labels))
      (saturatedKLayer (deeperValueStream (relabelFirstLayer θ σ))
        (trichotomyToSaturatedLabels r (m + 1) k (trich h).labels)) (m + 1))

/-- **Bundle-free builder of `FirstValueDataT` from the standing hypotheses.**  For each head,
the target sign-region witness `D'` (from `hgen`'s `AnchorCertificate`) supplies the region;
the topology is transported across the common first-attention equality `hAttn`; the trichotomy
result is produced by the `_of_topology` variant driven by `sourceFirstHeadRigidityFacts`
(`det`/`sym` from `H.target_regular`, `value` from K06C matched activity) and the separation
transported from `D'.separation_positive`; `pos` is discharged from `D'.level_positive`; and
`extract` from `det (A_h) ≠ 0` (quadric rigidity).  No honest input is assumed. -/
noncomputable def firstValueData_of_standingHypotheses {m k d r : Nat}
    {θ θ' : Params (m + 1) k d}
    (hr : 1 < r) (H : Step1.Step1StandingHypotheses r θ θ')
    (hgen : RecursiveGeneric r (m + 1) k d θ') (hd : 2 ≤ d) :
    FirstValueDataT (r := r) θ θ' (Step1.step1CommonFirstGates hr H).sigma := by
  set σ := (Step1.step1CommonFirstGates hr H).sigma with hσ
  have hAttn : attentionMatrix (relabelFirstLayer θ σ) 0 = attentionMatrix θ' 0 := by
    funext hh
    rw [attentionMatrix_relabelFirstLayer_zero]
    exact (Step1.step1CommonFirstGates hr H).attention_eq hh
  have hact : ∀ h : Fin k, σ h ∈ activeHeads θ (0 : Fin (m + 1)) := fun h =>
    (Step1.step1CommonFirstGates hr H).matched_active h
  have hsep : ∀ h : Fin k, ∀ x ∈ (standingFirstSignRegionData hgen h).region,
      ∀ b : Fin k, b ≠ h →
      0 < matrixBilin (attentionMatrix (relabelFirstLayer θ σ) 0 b) x.1.1 x.1.2 := by
    intro h x hx b hb
    have hpp := (standingFirstSignRegionData hgen h).separation_positive x hx ⟨b, hb⟩
    rw [signRegionSeparationValue_eq_matrixBilin] at hpp
    rw [congrFun hAttn b]
    exact hpp
  exact
    { region := fun h => (standingFirstSignRegionData hgen h).region
      topology := fun h => sourceFirstSignRegionTopology θ σ θ' h
        (standingFirstSignRegionData hgen h) hAttn
      trich := fun h => trichotomyResult_dialWithEstimate_of_topology _
        (sourceFirstSignRegionTopology θ σ θ' h (standingFirstSignRegionData hgen h) hAttn)
        (sourceFirstHeadRigidityFacts θ σ θ' h hAttn H.target_regular (hact h))
        hd (hsep h)
      pos := fun h x hx n hn1 hn a =>
        levelSlope_pos_of_signRegionData (standingFirstSignRegionData hgen h) hx n hn1 hn a
      extract := fun h => isSaturatedCoeffExtraction_of_det_ne_zero
        (relabelFirstLayer θ σ) θ' h _ _ _ hd
        (sourceFirstHeadRigidityFacts θ σ θ' h hAttn H.target_regular (hact h)).det_ne }

/-- **K07C.M9 core (`eq:first-V`), bundle-free.**  The first-layer value matching, in
target-to-source orientation, for the canonical K06C first-attention permutation, derived from
the standing hypotheses alone: the `FirstValueDataT` witnesses are constructed from target
genericity, and the derived separation/nonvanishing inputs are transported from the same target
sign-region witnesses. -/
theorem firstLayerValuesMatched_of_standing {m k d r : Nat}
    {θ θ' : Params (m + 1) k d}
    (hr : 1 < r) (H : Step1.Step1StandingHypotheses r θ θ')
    (hgen : RecursiveGeneric r (m + 1) k d θ') (hd : 2 ≤ d) :
    firstLayerValuesMatched (Nat.succ_pos m) θ θ'
      (Step1.step1CommonFirstGates hr H).sigma := by
  intro h
  set σ := (Step1.step1CommonFirstGates hr H).sigma with hσ
  let W := firstValueData_of_standingHypotheses hr H hgen hd
  have hAttn : attentionMatrix (relabelFirstLayer θ σ) 0 = attentionMatrix θ' 0 := by
    funext hh
    rw [attentionMatrix_relabelFirstLayer_zero]
    exact (Step1.step1CommonFirstGates hr H).attention_eq hh
  have hAgree : ∀ (w v : Vec d) (τ : ℝ), 0 < τ →
      probeOutput r (relabelFirstLayer θ σ) w v τ = probeOutput r θ' w v τ := by
    intro w v τ hτ
    exact (probeOutputEquality_relabelFirstLayer H.seq_pos θ σ (w, v) τ hτ).trans
      (H.probeOutputEquality (w, v) τ hτ)
  -- Separation transported from the (same) target sign-region witness.
  have hsep : ∀ x ∈ W.region h, ∀ b : Fin k, b ≠ h →
      0 < matrixBilin (attentionMatrix (relabelFirstLayer θ σ) 0 b) x.1.1 x.1.2 := by
    intro x hx b hb
    have hpp := (standingFirstSignRegionData hgen h).separation_positive x hx ⟨b, hb⟩
    rw [signRegionSeparationValue_eq_matrixBilin] at hpp
    rw [congrFun hAttn b]
    exact hpp
  -- Nonvanishing derived from the transported interface (target value + `w`).
  have hwnz : hyp_w_nonzero_S (W.trich h).Ustar (valueMatrix θ' 0 h) := by
    intro x hx
    have hxr : x ∈ W.region h := (W.trich h).region_subset_base hx
    exact ⟨(W.topology h).interface.target_value_ne_zero x hxr,
      (W.topology h).interface.w_ne_zero x hxr⟩
  have hval : valueMatrix (relabelFirstLayer θ σ) 0 h = valueMatrix θ' 0 h :=
    firstValue_matched_of_witnesses' (relabelFirstLayer θ σ) θ' h
      (W.region h) (W.topology h) (W.trich h) hsep hAttn hAgree (W.pos h) hwnz (W.extract h)
  rw [valueMatrix_relabelFirstLayer_zero] at hval
  exact hval

/-- **The K07C→K08 endgame adapter, BUNDLE-FREE.**  Exposes the peeling value-matching
predicate `firstLayerValuesMatchedForPeeling θ θ' σ` for the canonical K06C first-attention
permutation `σ = (step1CommonFirstGates hr H).sigma`, constructed purely from the standing
hypotheses `H`, `hr`, target recursive genericity `hgen`, and `2 ≤ d` — no bundled honest
witnesses.  This is the object fed to `firstLayerPeelingData_of_valuesMatched` in the L8
rewire. -/
theorem prop_first_V_of_standing {m k d r : Nat} {θ θ' : Params (m + 1) k d}
    (hr : 1 < r) (H : Step1.Step1StandingHypotheses r θ θ')
    (hgen : RecursiveGeneric r (m + 1) k d θ') (hd : 2 ≤ d) :
    firstLayerValuesMatchedForPeeling θ θ' (Step1.step1CommonFirstGates hr H).sigma :=
  firstLayerValuesMatchedForPeeling_of_firstLayerValuesMatched
    (firstLayerValuesMatched_of_standing hr H hgen hd)

end TransformerIdentifiability.NLayer.KHead
