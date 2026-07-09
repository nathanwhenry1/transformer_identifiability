import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.TierCascade
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SigmoidLaurent

set_option autoImplicit false

open Filter

namespace TransformerIdentifiability.NLayer.KHead.Step1

/-!
# K-head Step 1 tier-local gate analysis (`lem:tier-local`(i), gate half)

This file carries the three tier-local *gate-analysis* lemmas of milestone
M4.b, at a tier point `τ ∈ (step1TierCascadeData hr H).T p h j`:

* `step1SelectedGate_normalForm_of_tier` — the selected layer-`j` gate/level has
  an exact Laurent normal form: `csig ∘ level` has a pole of exact order `κ` with
  leading coefficient `cκ⁻¹`, tied to the level's exact vanishing order `κ` at `τ`
  (leading coefficient `cκ`).
* `step1NonselectedGate_tendsto_of_tier` — every nonselected layer-`j` gate tends
  to its `csig ∘ level` value on `puncturedNhds τ`.
* `step1LowerGate_analyticAt_of_tier` — every gate of a lower layer `i < j` is
  `AnalyticAt ℂ` at `τ`.

The heavier successor-pole and sibling-bridge theorems that also live in
`lem:tier-local` depend on other lanes (C3 dominance family, C5 arc data) and are
not developed here.
-/

/-- First-layer selected/nonselected level in affine form: at tier index `0`
(`Ω₀ = ℂ`), the layer-`0` level of any head `a` is the affine sigmoid argument
`τ · q'_{1a} + log r`. -/
theorem step1FirstLayerLevel_formula {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (a : Fin k) (hj0 : 0 < m + 1) (τ : ℂ) :
    (step1ActiveStratificationData hr H p).level (⟨0, hj0⟩, a) τ
      = τ * (firstLayerSlope θ' a p.1 : ℂ) + (logScale r : ℂ) := by
  have hD := step1ActiveStratificationData_spec hr H p
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  have aactive : a ∈ activeHeads θ' ⟨0, hj0⟩ :=
    (mem_activeHeads θ' ⟨0, hj0⟩ a).2 (hactiveAll ⟨0, hj0⟩ a)
  have hΩ0 : τ ∈ (step1ActiveStratificationData hr H p).Omega 0 := by
    rw [hD.omega_zero]; exact Set.mem_univ τ
  have hEq : (step1ActiveStratificationData hr H p).level (⟨0, hj0⟩, a) τ
      = τ * evalFormalPolyComplex
          (activeComplexGateAssignment θ' (step1ActiveStratificationData hr H p) τ)
          (formalSlope θ' p.1.1 p.1.2 ⟨0, hj0⟩ a) + (logScale r : ℂ) :=
    hD.level_formula ⟨0, hj0⟩ a aactive hΩ0
  rw [hEq, evalFormalPolyComplex_formalSlope_first θ' p.1.1 p.1.2 hj0 a
    (activeComplexGateAssignment θ' (step1ActiveStratificationData hr H p) τ)]
  simp [firstLayerSlope]

/-- At a tier point `τ ∈ T p h j`, every nonselected layer-`j` level omits `Π`
(the tier-`j` selected-only-collision condition (T1) for successor tiers, and
first-layer slope separation for the base tier). -/
theorem step1NonselectedLevel_notMem_Pi_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} (p : Step1SeparatedProbe H) (h : Fin k)
    {j : Nat} (hj : j < m + 1) {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j)
    (c : Fin k) (hc : c ≠ step1SelectedHead H.chains h j) :
    (step1ActiveStratificationData hr H p).level (⟨j, hj⟩, c) τ ∉ Pi := by
  cases j with
  | succ j =>
      have hmem := ((step1TierCascadeData hr H).mem_T_succ p h j (τ := τ)).mp hτ
      have hcoll : step1SelectedOnlyCollision hr H p h (j + 1) τ := by
        simpa [step1TierCascadeData] using hmem.2.1
      unfold step1SelectedOnlyCollision at hcoll
      rw [dif_pos hj] at hcoll
      exact hcoll.2 c hc
  | zero =>
      rw [step1SelectedHead_zero] at hc
      intro hcPi
      have hτ0 : τ ∈ firstLayerPoleProgression r θ' p.1 h := by
        simpa [step1TierCascadeData] using hτ
      have hqh : firstLayerSlope θ' h p.1 ≠ 0 := p.2.1.1 h
      have hb : (0 : ℝ) < logScale r := logScale_pos_of_one_lt hr
      have hb_ne : logScale r ≠ 0 := ne_of_gt hb
      -- selected head hits Π ⇒ its affine argument has real part label `-b/q'_{1h}`
      have hhPi : ((firstLayerSlope θ' h p.1 : ℂ) * τ + (logScale r : ℂ)) ∈ Pi :=
        (firstLayerPoleProgression_hits_Pi hqh τ).1 hτ0
      have hh_re : firstLayerSlope θ' h p.1 * τ.re + logScale r = 0 := by
        have hzero := Pi_re_eq_zero hhPi
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          sub_zero, zero_mul] at hzero
        linarith [hzero]
      -- nonselected head `c ≠ h` would give the same real-part label
      have hlevc :
          (step1ActiveStratificationData hr H p).level (⟨0, hj⟩, c) τ
            = τ * (firstLayerSlope θ' c p.1 : ℂ) + (logScale r : ℂ) :=
        step1FirstLayerLevel_formula hr H p c hj τ
      have hcmem : (τ * (firstLayerSlope θ' c p.1 : ℂ) + (logScale r : ℂ)) ∈ Pi :=
        hlevc ▸ hcPi
      have hc_re : τ.re * firstLayerSlope θ' c p.1 + logScale r = 0 := by
        have hzero := Pi_re_eq_zero hcmem
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero] at hzero
        linarith [hzero]
      -- real part is nonzero (else `b = 0`), so the slopes must coincide
      have hτre_ne : τ.re ≠ 0 := by
        intro h0
        rw [h0, mul_zero, zero_add] at hh_re
        exact hb_ne hh_re
      have e1 : τ.re * firstLayerSlope θ' h p.1 = -logScale r := by
        rw [mul_comm]; linarith [hh_re]
      have e2 : τ.re * firstLayerSlope θ' c p.1 = -logScale r := by
        linarith [hc_re]
      have key : τ.re * firstLayerSlope θ' h p.1 = τ.re * firstLayerSlope θ' c p.1 := by
        rw [e1, e2]
      have hslopes : firstLayerSlope θ' h p.1 = firstLayerSlope θ' c p.1 :=
        mul_left_cancel₀ hτre_ne key
      have hhc : h = c := p.2.1.2 hslopes
      exact hc hhc.symm

/-- **M4.b, lemma (i) — selected gate normal form.**  At a tier point
`τ ∈ (step1TierCascadeData hr H).T p h j` the selected layer-`j` level vanishes
to a finite exact order `κ ≥ 1` at `τ` (leading Taylor coefficient `cκ`), so by
`csig_comp_normalForm` the selected gate `csig ∘ level` has a pole of exact order
`κ` with leading Laurent coefficient `cκ⁻¹`. -/
theorem step1SelectedGate_normalForm_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} (p : Step1SeparatedProbe H) (h : Fin k)
    {j : Nat} (hj : j < m + 1) {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j) :
    ∃ (κ : ℕ) (cκ : ℂ), 1 ≤ κ ∧
      LaurentNormalFormAt (fun z => csig
        ((step1ActiveStratificationData hr H p).level
          (⟨j, hj⟩, step1SelectedHead H.chains h j) z)) τ (κ : ℤ) cκ⁻¹ ∧
      LaurentNormalFormAt (fun z =>
          (step1ActiveStratificationData hr H p).level
            (⟨j, hj⟩, step1SelectedHead H.chains h j) z
          - (step1ActiveStratificationData hr H p).level
              (⟨j, hj⟩, step1SelectedHead H.chains h j) τ) τ (-(κ : ℤ)) cκ := by
  set sel := step1SelectedHead H.chains h j with hsel
  have hD := step1ActiveStratificationData_spec hr H p
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  have selactive : sel ∈ activeHeads θ' ⟨j, hj⟩ :=
    (mem_activeHeads θ' ⟨j, hj⟩ sel).2 (hactiveAll ⟨j, hj⟩ sel)
  -- `τ` lies in stratum `j`, hence in `Ω_j`, where the selected level is analytic
  have hstratum : τ ∈ step1ActiveStratum hr H p h j := by
    have hmem := (step1TierCascadeData hr H).tier_in_stratum hτ
    simpa [step1TierCascadeData] using hmem
  have hτS : τ ∈ (step1ActiveStratificationData hr H p).stratum j := by
    simpa [step1ActiveStratum, hj] using hstratum
  have hτΩ : τ ∈ (step1ActiveStratificationData hr H p).Omega j :=
    (hD.stratum_closedDiscrete ⟨j, hj⟩).subset hτS
  have hLan : AnalyticAt ℂ ((step1ActiveStratificationData hr H p).level (⟨j, hj⟩, sel)) τ :=
    hD.level_holomorphic ⟨j, hj⟩ sel selactive τ hτΩ
  -- the selected level hits `Π` at `τ`
  have hLτ : (step1ActiveStratificationData hr H p).level (⟨j, hj⟩, sel) τ ∈ Pi := by
    have hpole := step1TierCascadeData_selectedGatePole (hr := hr) (H := H)
      (p := p) (h := h) (j := j) (τ := τ) hτ
    simp only [step1TierCascadeData] at hpole
    simpa [step1SelectedLevelPole, hj, hsel] using hpole
  -- the selected level is not locally constant near `τ` (identity theorem)
  have hnot : ¬ ((step1ActiveStratificationData hr H p).level (⟨j, hj⟩, sel)
      =ᶠ[nhds τ] fun _ => (step1ActiveStratificationData hr H p).level (⟨j, hj⟩, sel) τ) := by
    intro heq
    have hpre : IsPreconnected ((step1ActiveStratificationData hr H p).Omega j) :=
      (hD.domain j (le_of_lt hj)).isPreconnected
    have hLon : AnalyticOnNhd ℂ ((step1ActiveStratificationData hr H p).level (⟨j, hj⟩, sel))
        ((step1ActiveStratificationData hr H p).Omega j) :=
      hD.level_holomorphic ⟨j, hj⟩ sel selactive
    have hconst : AnalyticOnNhd ℂ
        (fun _ : ℂ => (step1ActiveStratificationData hr H p).level (⟨j, hj⟩, sel) τ)
        ((step1ActiveStratificationData hr H p).Omega j) := fun z _ => analyticAt_const
    have hEqOn := hLon.eqOn_of_preconnected_of_eventuallyEq hconst hpre hτΩ heq
    exact hD.level_not_constant_pole ⟨j, hj⟩ sel selactive
      ((step1ActiveStratificationData hr H p).level (⟨j, hj⟩, sel) τ) hLτ hEqOn
  obtain ⟨κ, hκ, coeff, hcoeff_ne, hNF⟩ :=
    LaurentNormalFormAt.analyticAt_normalForm_of_not_eventually_eq hLan hnot
  refine ⟨κ, coeff, hκ, ?_, hNF⟩
  exact csig_comp_normalForm hLτ hLan rfl hκ hNF

/-- **M4.b, lemma (i) — nonselected gate limit.**  At a tier point `τ`, every
nonselected layer-`j` gate is analytic where its level omits `Π` and hence tends
to its `csig ∘ level` value along `puncturedNhds τ` (the gate agrees with
`csig ∘ level` on the punctured stratification domain `Ω_{j+1}`). -/
theorem step1NonselectedGate_tendsto_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} (p : Step1SeparatedProbe H) (h : Fin k)
    {j : Nat} (hj : j < m + 1) {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j)
    (c : Fin k) (hc : c ≠ step1SelectedHead H.chains h j) :
    Tendsto ((step1ActiveStratificationData hr H p).gate (⟨j, hj⟩, c))
      (puncturedNhds τ)
      (nhds (csig ((step1ActiveStratificationData hr H p).level (⟨j, hj⟩, c) τ))) := by
  have hD := step1ActiveStratificationData_spec hr H p
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  have cactive : c ∈ activeHeads θ' ⟨j, hj⟩ :=
    (mem_activeHeads θ' ⟨j, hj⟩ c).2 (hactiveAll ⟨j, hj⟩ c)
  have hstratum : τ ∈ step1ActiveStratum hr H p h j := by
    have hmem := (step1TierCascadeData hr H).tier_in_stratum hτ
    simpa [step1TierCascadeData] using hmem
  have hτS : τ ∈ (step1ActiveStratificationData hr H p).stratum j := by
    simpa [step1ActiveStratum, hj] using hstratum
  have hτΩ : τ ∈ (step1ActiveStratificationData hr H p).Omega j :=
    (hD.stratum_closedDiscrete ⟨j, hj⟩).subset hτS
  have hcnotPi : (step1ActiveStratificationData hr H p).level (⟨j, hj⟩, c) τ ∉ Pi :=
    step1NonselectedLevel_notMem_Pi_of_tier (hr := hr) (H := H) p h hj hτ c hc
  have hlevAn : AnalyticAt ℂ ((step1ActiveStratificationData hr H p).level (⟨j, hj⟩, c)) τ :=
    hD.level_holomorphic ⟨j, hj⟩ c cactive τ hτΩ
  have hcompAn : AnalyticAt ℂ
      (fun z => csig ((step1ActiveStratificationData hr H p).level (⟨j, hj⟩, c) z)) τ := by
    have hcomp := (csig_analyticAt_of_notMem_Pi hcnotPi).comp hlevAn
    simpa [Function.comp] using hcomp
  have htend : Tendsto (fun z => csig ((step1ActiveStratificationData hr H p).level (⟨j, hj⟩, c) z))
      (puncturedNhds τ)
      (nhds (csig ((step1ActiveStratificationData hr H p).level (⟨j, hj⟩, c) τ))) :=
    hcompAn.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hΩsucc : ∀ᶠ z in puncturedNhds τ,
      z ∈ (step1ActiveStratificationData hr H p).Omega (j + 1) :=
    step1ActiveStratum_punctured_omega_succ (hr := hr) (H := H) (p := p) (h := h) hj hstratum
  have hgate_eq : (step1ActiveStratificationData hr H p).gate (⟨j, hj⟩, c)
      =ᶠ[puncturedNhds τ]
      (fun z => csig ((step1ActiveStratificationData hr H p).level (⟨j, hj⟩, c) z)) := by
    filter_upwards [hΩsucc] with z hz
    exact hD.gate_formula ⟨j, hj⟩ c cactive hz
  exact Tendsto.congr' hgate_eq.symm htend

/-- **M4.b, lemma (i) — lower-layer gates.**  At a tier point `τ`, every gate of a
strictly lower layer `i < j` is analytic at `τ`, since `τ ∈ Ω_j ⊆ Ω_{i+1}` and the
layer-`i` gate is holomorphic on `Ω_{i+1}`. -/
theorem step1LowerGate_analyticAt_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} (p : Step1SeparatedProbe H) (h : Fin k)
    {j : Nat} (hj : j < m + 1) {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j)
    {i : Nat} (hij : i < j) (a : Fin k) :
    AnalyticAt ℂ
      ((step1ActiveStratificationData hr H p).gate (⟨i, lt_trans hij hj⟩, a)) τ := by
  have hD := step1ActiveStratificationData_spec hr H p
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  have aactive : a ∈ activeHeads θ' ⟨i, lt_trans hij hj⟩ :=
    (mem_activeHeads θ' ⟨i, lt_trans hij hj⟩ a).2 (hactiveAll ⟨i, lt_trans hij hj⟩ a)
  have hstratum : τ ∈ step1ActiveStratum hr H p h j := by
    have hmem := (step1TierCascadeData hr H).tier_in_stratum hτ
    simpa [step1TierCascadeData] using hmem
  have hτS : τ ∈ (step1ActiveStratificationData hr H p).stratum j := by
    simpa [step1ActiveStratum, hj] using hstratum
  have hτΩj : τ ∈ (step1ActiveStratificationData hr H p).Omega j :=
    (hD.stratum_closedDiscrete ⟨j, hj⟩).subset hτS
  have hsub : (step1ActiveStratificationData hr H p).Omega j
      ⊆ (step1ActiveStratificationData hr H p).Omega (i + 1) :=
    omega_subset_of_le_of_omega_succ (step1ActiveStratificationData hr H p) hD.omega_succ
      (show i + 1 ≤ j by omega) (show j ≤ m + 1 by omega)
  have hτΩi : τ ∈ (step1ActiveStratificationData hr H p).Omega (i + 1) := hsub hτΩj
  exact hD.gate_holomorphic ⟨i, lt_trans hij hj⟩ a aactive τ hτΩi

/-! ## M3.d — dominance persistence (`lem:dominance-persistence`)

The remaining tier-local worker: on a small punctured disc around a current tier
point every point satisfies the *successor* tier's strict finite-family
dominance condition.  The proof is the four-step TeX argument: the dominance
thresholds are continuous in the gate assignment; every gate a threshold reads
is continuous at `τ` (lower layers analytic, nonselected layer-`j` gates tend to
their `csig∘level` values) while the blowing-up selected layer-`j` gate is never
read (the member's `lowerCoeff` support fact); the finitely many strict
inequalities inherited from the current tier persist by continuity; and the new
top threshold is cleared because its selected gate blows up while the threshold
itself stays bounded. -/

/-- Evaluation of a formal polynomial only depends on the assignment restricted
to the polynomial's variables. -/
theorem evalFormalPolyComplex_congr_on_vars {L kk : Nat} (f : FormalPoly L kk)
    {z₁ z₂ : FormalVar L kk -> ℂ} (hagree : ∀ v ∈ f.vars, z₁ v = z₂ v) :
    evalFormalPolyComplex z₁ f = evalFormalPolyComplex z₂ f := by
  unfold evalFormalPolyComplex
  apply MvPolynomial.eval₂_congr
  intro v c hv hc
  exact hagree v ((MvPolynomial.mem_vars_iff_mem_support v).2
    ⟨c, MvPolynomial.mem_support_iff.mpr hc, hv⟩)

/-- A variable in a polynomial supported in layers `≤ n` lives in a layer `≤ n`. -/
theorem mem_vars_layer_le_of_polynomialInLayersLE {L kk n : Nat} {f : FormalPoly L kk}
    (hf : PolynomialInLayersLE n f) {v : FormalVar L kk} (hv : v ∈ f.vars) :
    v.1.1 ≤ n := by
  rw [MvPolynomial.mem_vars_iff_mem_support] at hv
  obtain ⟨mono, hmono, hvmono⟩ := hv
  by_contra hcon
  push_neg at hcon
  exact (Finsupp.mem_support_iff.mp hvmono) (hf mono hmono v hcon)

/-- Two assignments that agree on the (lower) coefficients and prior selected
variables read by tower stage `i` produce the same largeness threshold. -/
theorem dominanceTowerThreshold_congr_of_agree {L kk pp : Nat} {c : HeadChain L kk pp}
    {f : FormalPoly L kk} (data : DominanceTowerData c f) (i : Fin pp)
    {z₁ z₂ : FormalVar L kk -> ℂ}
    (hlow : ∀ s : Fin (data.degree i),
      evalFormalPolyComplex z₁ (data.lowerCoeff i s)
        = evalFormalPolyComplex z₂ (data.lowerCoeff i s))
    (hprior : ∀ jj : Fin pp, jj.1 < i.1 → z₁ (c.selectedVar jj) = z₂ (c.selectedVar jj)) :
    dominanceTowerThreshold data i z₁ = dominanceTowerThreshold data i z₂ := by
  have hsum : towerLowerNormSum data i z₁ = towerLowerNormSum data i z₂ := by
    unfold towerLowerNormSum
    exact Finset.sum_congr rfl fun s _ => by rw [hlow s]
  have hprod : towerPriorNormProduct c data.degree i.1 z₁
      = towerPriorNormProduct c data.degree i.1 z₂ := by
    unfold towerPriorNormProduct
    refine Finset.prod_congr rfl fun jj hjj => ?_
    rw [hprior jj (Finset.mem_filter.mp hjj).2]
  unfold dominanceTowerThreshold
  rw [hsum, hprod]

/-- The tier-`j` dominance condition holds at any tier-`j` point.  For `j = 0`
it is vacuous (no staged selected layer is below `0`); for a successor tier it is
part of the tier membership. -/
theorem step1TowerDominance_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j) :
    step1TowerDominance hr H p h j τ := by
  cases j with
  | zero =>
      unfold step1TowerDominance
      rw [dif_pos (Nat.zero_le (m + 1))]
      intro ix i hi
      exact absurd hi (Nat.not_lt_zero i.1)
  | succ j' =>
      have hmem := ((step1TierCascadeData hr H).mem_T_succ p h j' (τ := τ)).mp hτ
      simpa [step1TierCascadeData] using hmem.2.2.2

/-- **M3.d — `lem:dominance-persistence`.**  On a small punctured disc around a
current tier point `τ ∈ T p h j`, every point satisfies the successor tier's
strict finite-family dominance condition. -/
noncomputable def step1DominancePersistence_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ}
    (hj : j < (step1TierCascadeData hr H).depth)
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j)
    (hsucc : j + 1 < (step1TierCascadeData hr H).depth) :
    Step1DominancePersistenceAtTier hr H p h j τ := by
  classical
  have hdepth : (step1TierCascadeData hr H).depth = m + 1 := step1TierCascadeData_depth hr H
  have hj' : j < m + 1 := by omega
  have hD := step1ActiveStratificationData_spec hr H p
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  -- basic stratification facts at `τ`
  have hstratum : τ ∈ step1ActiveStratum hr H p h j := by
    have hmem := (step1TierCascadeData hr H).tier_in_stratum hτ
    simpa [step1TierCascadeData] using hmem
  have hτS : τ ∈ (step1ActiveStratificationData hr H p).stratum j := by
    simpa [step1ActiveStratum, hj'] using hstratum
  have hτΩ : τ ∈ (step1ActiveStratificationData hr H p).Omega j :=
    (hD.stratum_closedDiscrete ⟨j, hj'⟩).subset hτS
  -- the gate assignment coincides with the concrete gate at every (active) variable
  have hg : ∀ (z : ℂ) (v : FormalVar (m + 1) k),
      step1GateAssignment hr H p z v = (step1ActiveStratificationData hr H p).gate v z :=
    fun z v => step1GateAssignment_eq_gate H p z v.1 v.2
  -- the blowing-up selected layer-`j` variable
  set vbad : FormalVar (m + 1) k :=
    ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) with hvbad_def
  have hvbad_layer : vbad.1.1 = j := by rw [hvbad_def]
  have selactive : step1SelectedHead H.chains h j ∈ activeHeads θ' ⟨j, hj'⟩ :=
    (mem_activeHeads θ' ⟨j, hj'⟩ (step1SelectedHead H.chains h j)).2
      (hactiveAll ⟨j, hj'⟩ (step1SelectedHead H.chains h j))
  -- lower-layer gates equal `csig ∘ level` at `τ` itself
  have hgateτ : ∀ v : FormalVar (m + 1) k, v.1.1 < j ->
      (step1ActiveStratificationData hr H p).gate v τ
        = csig ((step1ActiveStratificationData hr H p).level v τ) := by
    intro v hvlt
    have hact : v.2 ∈ activeHeads θ' v.1 :=
      (mem_activeHeads θ' v.1 v.2).2 (hactiveAll v.1 v.2)
    have hsub : (step1ActiveStratificationData hr H p).Omega j
        ⊆ (step1ActiveStratificationData hr H p).Omega (v.1.1 + 1) :=
      omega_subset_of_le_of_omega_succ (step1ActiveStratificationData hr H p) hD.omega_succ
        (show v.1.1 + 1 ≤ j by omega) (show j ≤ m + 1 by omega)
    exact (hD.gate_formula v.1 v.2 hact) (hsub hτΩ)
  -- every gate a threshold reads tends to its `csig ∘ level` value near `τ`
  have hgate_tendsto_good : ∀ v : FormalVar (m + 1) k, (v.1.1 ≤ j ∧ v ≠ vbad) ->
      Tendsto (fun z => step1GateAssignment hr H p z v) (puncturedNhds τ)
        (nhds (csig ((step1ActiveStratificationData hr H p).level v τ))) := by
    rintro v ⟨hvle, hvne⟩
    have hgfun : (fun z => step1GateAssignment hr H p z v)
        = (fun z => (step1ActiveStratificationData hr H p).gate v z) := by
      funext z; exact hg z v
    rw [hgfun]
    rcases lt_or_eq_of_le hvle with hlt | heq
    · have hana : AnalyticAt ℂ ((step1ActiveStratificationData hr H p).gate v) τ :=
        step1LowerGate_analyticAt_of_tier p h hj' hτ hlt v.2
      have htend : Tendsto (fun z => (step1ActiveStratificationData hr H p).gate v z)
          (puncturedNhds τ) (nhds ((step1ActiveStratificationData hr H p).gate v τ)) :=
        hana.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      rw [hgateτ v hlt] at htend
      exact htend
    · have hv2 : v.2 ≠ step1SelectedHead H.chains h j := by
        intro hv2eq
        apply hvne
        rw [hvbad_def]
        have hv1 : v.1 = (⟨j, hj'⟩ : Fin (m + 1)) := Fin.ext heq
        calc v = (v.1, v.2) := rfl
          _ = ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) := by rw [hv1, hv2eq]
      have htend := step1NonselectedGate_tendsto_of_tier p h hj' hτ v.2 hv2
      have hv1 : v.1 = (⟨j, hj'⟩ : Fin (m + 1)) := Fin.ext heq
      have hvpair : ((⟨j, hj'⟩ : Fin (m + 1)), v.2) = v := by rw [← hv1]
      rw [hvpair] at htend
      exact htend
  -- the modified, coordinatewise-convergent gate assignment and its limit
  set A' : ℂ -> FormalVar (m + 1) k -> ℂ :=
    fun z v => if (v.1.1 ≤ j ∧ v ≠ vbad) then step1GateAssignment hr H p z v else 0 with hA'
  set A'τ : FormalVar (m + 1) k -> ℂ :=
    fun v => if (v.1.1 ≤ j ∧ v ≠ vbad)
      then csig ((step1ActiveStratificationData hr H p).level v τ) else 0 with hA'τ
  have hA'tendsto : Tendsto A' (puncturedNhds τ) (nhds A'τ) := by
    rw [tendsto_pi_nhds]
    intro v
    by_cases hgv : (v.1.1 ≤ j ∧ v ≠ vbad)
    · have hL : (fun z => A' z v) = (fun z => step1GateAssignment hr H p z v) := by
        funext z; simp only [hA']; rw [if_pos hgv]
      have hRlim : A'τ v = csig ((step1ActiveStratificationData hr H p).level v τ) := by
        simp only [hA'τ]; rw [if_pos hgv]
      rw [hL, hRlim]
      exact hgate_tendsto_good v hgv
    · have hL : (fun z => A' z v) = (fun _ => (0 : ℂ)) := by
        funext z; simp only [hA']; rw [if_neg hgv]
      have hRlim : A'τ v = 0 := by simp only [hA'τ]; rw [if_neg hgv]
      rw [hL, hRlim]
      exact tendsto_const_nhds
  -- the selected layer-`j` gate blows up
  have hRHSblow : Tendsto
      (fun z => ‖(step1ActiveStratificationData hr H p).gate vbad z‖) (puncturedNhds τ) atTop := by
    obtain ⟨κ, cκ, hκ, hNF, _⟩ := step1SelectedGate_normalForm_of_tier p h hj' hτ
    have hblowCsig : BlowsUpAt (fun z => csig ((step1ActiveStratificationData hr H p).level
        (⟨j, hj'⟩, step1SelectedHead H.chains h j) z)) τ :=
      hNF.blowsUpAt (by exact_mod_cast hκ)
    have hΩsucc := step1ActiveStratum_punctured_omega_succ hj' hstratum
    have heqnorm : (fun z => ‖csig ((step1ActiveStratificationData hr H p).level
          (⟨j, hj'⟩, step1SelectedHead H.chains h j) z)‖)
        =ᶠ[puncturedNhds τ] (fun z => ‖(step1ActiveStratificationData hr H p).gate vbad z‖) := by
      filter_upwards [hΩsucc] with z hz
      have hgf := (hD.gate_formula ⟨j, hj'⟩ (step1SelectedHead H.chains h j) selactive) hz
      rw [hvbad_def, hgf]
    exact hblowCsig.congr' heqnorm
  -- the current tier's dominance holds at `τ`
  have hdomτ : step1TowerDominance hr H p h j τ := step1TowerDominance_of_tier hτ
  -- per-member, per-stage persistence of a single strict inequality
  have core : ∀ (ix : Step1DominanceFamilyIndex H p.1 h)
      (i : Fin (step1DominanceFamilyChainLength H p.1 h (step1DominanceFamily H p.2 h ix).idx)),
      ∀ᶠ z in puncturedNhds τ, i.1 < j + 1 ->
        dominanceTowerThreshold (step1DominanceFamily H p.2 h ix).tower i
            (step1GateAssignment hr H p z)
          < ‖step1GateAssignment hr H p z
              ((step1DominanceFamilyHeadChain H p.1 h
                (step1DominanceFamily H p.2 h ix).idx).selectedVar i)‖ := by
    intro ix
    set M := step1DominanceFamily H p.2 h ix with hM
    set c := step1DominanceFamilyHeadChain H p.1 h M.idx with hc
    intro i
    by_cases hij : i.1 < j + 1
    · have hij_le : i.1 ≤ j := Nat.lt_succ_iff.mp hij
      -- support facts for the member's stage-`i` thresholds
      have hvarGood : ∀ (s : Fin (M.tower.degree i)) (v : FormalVar (m + 1) k),
          v ∈ (M.tower.lowerCoeff i s).vars -> (v.1.1 ≤ j ∧ v ≠ vbad) := by
        intro s v hv
        have hlayer : v.1.1 ≤ i.1 :=
          mem_vars_layer_le_of_polynomialInLayersLE (M.lowerCoeff_support i s) hv
        refine ⟨le_trans hlayer hij_le, ?_⟩
        intro hvbadEq
        have hvj : v.1.1 = j := by rw [hvbadEq]
        have hij_eq : i.1 = j := le_antisymm hij_le (by rw [← hvj]; exact hlayer)
        have hsel : c.selectedVar i = vbad := by
          rw [hc, step1DominanceFamilyHeadChain_selectedVar, hvbad_def]
          exact Prod.ext_iff.mpr ⟨Fin.ext hij_eq, congrArg (step1SelectedHead H.chains h) hij_eq⟩
        apply M.lowerCoeff_selectedVar_notMem i s
        change c.selectedVar i ∈ (M.tower.lowerCoeff i s).vars
        rw [hsel, ← hvbadEq]
        exact hv
      have hpriorGood : ∀ jj : Fin (step1DominanceFamilyChainLength H p.1 h M.idx),
          jj.1 < i.1 -> ((c.selectedVar jj).1.1 ≤ j ∧ c.selectedVar jj ≠ vbad) := by
        intro jj hjjlt
        have hlayer : (c.selectedVar jj).1.1 = jj.1 := by
          rw [hc, step1DominanceFamilyHeadChain_selectedVar]
        have hjjltj : jj.1 < j := lt_of_lt_of_le hjjlt hij_le
        refine ⟨by rw [hlayer]; exact le_of_lt hjjltj, ?_⟩
        intro hbad
        have hcopy := hlayer
        rw [hbad, hvbad_layer] at hcopy
        omega
      -- the threshold along the true assignment converges to its value at `A'τ`
      have hcongr : ∀ z : ℂ, dominanceTowerThreshold M.tower i (step1GateAssignment hr H p z)
          = dominanceTowerThreshold M.tower i (A' z) := by
        intro z
        refine dominanceTowerThreshold_congr_of_agree M.tower i ?_ ?_
        · intro s
          refine evalFormalPolyComplex_congr_on_vars (M.tower.lowerCoeff i s) ?_
          intro v hv
          have hg2 := hvarGood s v hv
          have : A' z v = step1GateAssignment hr H p z v := by simp only [hA']; rw [if_pos hg2]
          exact this.symm
        · intro jj hjjlt
          have hg2 := hpriorGood jj hjjlt
          have : A' z (c.selectedVar jj) = step1GateAssignment hr H p z (c.selectedVar jj) := by
            simp only [hA']; rw [if_pos hg2]
          exact this.symm
      have hthrTendsto : Tendsto
          (fun z => dominanceTowerThreshold M.tower i (step1GateAssignment hr H p z))
          (puncturedNhds τ) (nhds (dominanceTowerThreshold M.tower i A'τ)) := by
        have hcomp : Tendsto (fun z => dominanceTowerThreshold M.tower i (A' z))
            (puncturedNhds τ) (nhds (dominanceTowerThreshold M.tower i A'τ)) :=
          ((continuous_dominanceTowerThreshold M.tower M.topConstant_ne_zero i).tendsto A'τ).comp
            hA'tendsto
        exact hcomp.congr (fun z => (hcongr z).symm)
      rcases lt_or_eq_of_le hij_le with hlt | heq
      · -- lower stage: persist the strict inequality inherited from tier `j`
        have hthrEq : dominanceTowerThreshold M.tower i A'τ
            = dominanceTowerThreshold M.tower i (step1GateAssignment hr H p τ) := by
          refine dominanceTowerThreshold_congr_of_agree M.tower i ?_ ?_
          · intro s
            refine evalFormalPolyComplex_congr_on_vars (M.tower.lowerCoeff i s) ?_
            intro v hv
            have hg2 := hvarGood s v hv
            have hAv : A'τ v = csig ((step1ActiveStratificationData hr H p).level v τ) := by
              simp only [hA'τ]; rw [if_pos hg2]
            have hlayerlt : v.1.1 < j :=
              lt_of_le_of_lt
                (mem_vars_layer_le_of_polynomialInLayersLE (M.lowerCoeff_support i s) hv) hlt
            rw [hAv, hg τ v, hgateτ v hlayerlt]
          · intro jj hjjlt
            have hAv : A'τ (c.selectedVar jj)
                = csig ((step1ActiveStratificationData hr H p).level (c.selectedVar jj) τ) := by
              simp only [hA'τ]; rw [if_pos (hpriorGood jj hjjlt)]
            have hlayerlt : (c.selectedVar jj).1.1 < j := by
              have hll : (c.selectedVar jj).1.1 = jj.1 := by
                rw [hc, step1DominanceFamilyHeadChain_selectedVar]
              rw [hll]; exact lt_trans hjjlt hlt
            rw [hAv, hg τ (c.selectedVar jj), hgateτ (c.selectedVar jj) hlayerlt]
        have hRHStend : Tendsto (fun z => ‖step1GateAssignment hr H p z (c.selectedVar i)‖)
            (puncturedNhds τ)
            (nhds ‖(step1ActiveStratificationData hr H p).gate (c.selectedVar i) τ‖) := by
          have hanaRHS : AnalyticAt ℂ
              ((step1ActiveStratificationData hr H p).gate (c.selectedVar i)) τ := by
            rw [hc, step1DominanceFamilyHeadChain_selectedVar]
            exact step1LowerGate_analyticAt_of_tier p h hj' hτ hlt (step1SelectedHead H.chains h i.1)
          have hgtend : Tendsto
              (fun z => ‖(step1ActiveStratificationData hr H p).gate (c.selectedVar i) z‖)
              (puncturedNhds τ)
              (nhds ‖(step1ActiveStratificationData hr H p).gate (c.selectedVar i) τ‖) :=
            (hanaRHS.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).norm
          exact hgtend.congr (fun z => by rw [hg z (c.selectedVar i)])
        have hstrict := step1TowerDominance_iff (le_of_lt hj') hdomτ ix i hlt
        have hlimlt : dominanceTowerThreshold M.tower i A'τ
            < ‖(step1ActiveStratificationData hr H p).gate (c.selectedVar i) τ‖ := by
          rw [hthrEq, ← hg τ (c.selectedVar i)]
          exact hstrict
        have hp := hthrTendsto.eventually_lt hRHStend hlimlt
        exact hp.mono (fun z hz _ => hz)
      · -- top stage: the selected gate blows up, clearing the bounded threshold
        have hsel : c.selectedVar i = vbad := by
          rw [hc, step1DominanceFamilyHeadChain_selectedVar, hvbad_def]
          exact Prod.ext_iff.mpr ⟨Fin.ext heq, congrArg (step1SelectedHead H.chains h) heq⟩
        have hRHSblow' : Tendsto (fun z => ‖step1GateAssignment hr H p z (c.selectedVar i)‖)
            (puncturedNhds τ) atTop := by
          have hfe : (fun z => ‖step1GateAssignment hr H p z (c.selectedVar i)‖)
              = (fun z => ‖(step1ActiveStratificationData hr H p).gate vbad z‖) := by
            funext z; rw [hg z (c.selectedVar i), hsel]
          rw [hfe]; exact hRHSblow
        have hp : ∀ᶠ z in puncturedNhds τ,
            dominanceTowerThreshold M.tower i (step1GateAssignment hr H p z)
              < ‖step1GateAssignment hr H p z (c.selectedVar i)‖ := by
          filter_upwards
            [hthrTendsto (Iio_mem_nhds (lt_add_one (dominanceTowerThreshold M.tower i A'τ))),
             hRHSblow'.eventually
               (eventually_gt_atTop (dominanceTowerThreshold M.tower i A'τ + 1))]
            with z hz1 hz2
          exact lt_trans (Set.mem_Iio.mp hz1) hz2
        exact hp.mono (fun z hz _ => hz)
    · exact Filter.Eventually.of_forall (fun z hcontra => absurd hcontra hij)
  -- assemble the finite family and extract a common radius
  haveI : Finite (Σ ix : Step1DominanceFamilyIndex H p.1 h,
      Fin (step1DominanceFamilyChainLength H p.1 h (step1DominanceFamily H p.2 h ix).idx)) := by
    infer_instance
  have hQ : ∀ᶠ z in puncturedNhds τ,
      ∀ w : (Σ ix : Step1DominanceFamilyIndex H p.1 h,
        Fin (step1DominanceFamilyChainLength H p.1 h (step1DominanceFamily H p.2 h ix).idx)),
        w.2.1 < j + 1 ->
          dominanceTowerThreshold (step1DominanceFamily H p.2 h w.1).tower w.2
              (step1GateAssignment hr H p z)
            < ‖step1GateAssignment hr H p z
                ((step1DominanceFamilyHeadChain H p.1 h
                  (step1DominanceFamily H p.2 h w.1).idx).selectedVar w.2)‖ := by
    rw [Filter.eventually_all]
    rintro ⟨ix, i⟩
    exact core ix i
  have heventually : ∀ᶠ z in puncturedNhds τ, step1TowerDominance hr H p h (j + 1) z := by
    filter_upwards [hQ] with z hz
    unfold step1TowerDominance
    rw [dif_pos (show j + 1 ≤ m + 1 by omega)]
    intro ix i hi
    exact hz ⟨ix, i⟩ hi
  have hmem := Metric.mem_nhdsWithin_iff.mp heventually
  refine ⟨Classical.choose hmem, (Classical.choose_spec hmem).1, ?_⟩
  intro z hz
  exact (Classical.choose_spec hmem).2 ⟨Metric.mem_ball.mpr hz.2, by simpa using hz.1⟩

/-! ## M4.b — successor selected-level pole normal form (`lem:successor-pole`)

The heart of `lem:successor-pole`/`cor:successor-pole-payload`: at a tier point
`τ ∈ T p h j` the successor selected level `H'_{j+1,a_{j+1}}` has an exact Laurent
pole of order `2κ` (with `κ = κ_j` the vanishing order of the current selected
level, from C4b) and nonzero leading coefficient `τ · Ψ_{j+1}(τ) · c_κ⁻²`.  The
three ingredients named in the ledger are combined: the exact sigmoid pole of the
current selected gate (`step1SelectedGate_normalForm_of_tier`, C4b), the
quadratic/single-variable split of the successor slope in the selected layer-`j`
variable (`coeffOfVar` tools), and the finite-family dominance nonvanishing
`Ψ_{j+1}(τ) ≠ 0` (`step1TowerDominance_eval_ne_zero` on the stage-`j` ignition
member of `𝓕_h`). -/

/-- An analytic function with a nonzero value at `ξ` is a Laurent normal form of
order `0` (a removable/regular point). -/
theorem laurentNormalFormAt_zero_of_analyticAt {a : ℂ -> ℂ} {ξ : ℂ}
    (ha : AnalyticAt ℂ a ξ) (hne : a ξ ≠ 0) :
    LaurentNormalFormAt a ξ 0 (a ξ) := by
  refine ⟨hne, a, ha, rfl, ?_⟩
  filter_upwards with z
  simp

/-- Transport a Laurent normal form across a proof that its order equals another
integer. -/
theorem laurentNF_order_cast {f : ℂ -> ℂ} {ξ : ℂ} {μ μ' : ℤ} {c : ℂ}
    (h : LaurentNormalFormAt f ξ μ c) (hμ : μ = μ') :
    LaurentNormalFormAt f ξ μ' c := hμ ▸ h

/-- A variable in a polynomial supported in layers `< n` lives in a layer `< n`. -/
theorem mem_vars_layer_lt_of_polynomialInLayersLT {L kk n : Nat} {f : FormalPoly L kk}
    (hf : PolynomialInLayersLT n f) {v : FormalVar L kk} (hv : v ∈ f.vars) :
    v.1.1 < n := by
  rw [MvPolynomial.mem_vars_iff_mem_support] at hv
  obtain ⟨mono, hmono, hvmono⟩ := hv
  by_contra hcon
  exact (Finsupp.mem_support_iff.mp hvmono) (hf mono hmono v (not_lt.mp hcon))

/-- Complex evaluation of a formal polynomial is analytic at `τ` whenever every
formal variable's assignment is analytic at `τ` (a polynomial combination of
analytic coordinate functions). -/
theorem evalFormalPolyComplex_analyticAt_of_all {L kk : Nat} {τ : ℂ}
    {η : ℂ -> FormalVar L kk -> ℂ} (P : FormalPoly L kk)
    (hη : ∀ x : FormalVar L kk, AnalyticAt ℂ (fun z => η z x) τ) :
    AnalyticAt ℂ (fun z => evalFormalPolyComplex (η z) P) τ := by
  simp only [evalFormalPolyComplex]
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval₂_C]
      exact analyticAt_const
  | add p q hp hq =>
      simp only [MvPolynomial.eval₂_add]
      exact hp.add hq
  | mul_X p x hp =>
      simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      exact hp.mul (hη x)

/-- **`lem:successor-pole`(ii) leading factor.**  At a tier point `τ ∈ T p h j`
(with `j < m`), the stage-`j` ignition polynomial `ψ_{j+1}` — the `ζ_j²`
coefficient of the successor selected slope — does not vanish at the concrete gate
assignment.  This is the no-cancellation statement `Ψ_{j+1}(τ) ≠ 0`, reduced to the
member-wise finite-family dominance nonvanishing on the stage-`j` ignition member
of `𝓕_h` via the tier-`j` dominance `(T3)`. -/
theorem step1SuccessorLeadingFactor_ne_zero_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} (p : Step1SeparatedProbe H) (h : Fin k)
    {j : Nat} (hjm : j < m) {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j) :
    evalFormalPolyComplex (step1GateAssignment hr H p τ)
      (step1IgnitionPoly H.chains h p.1 j hjm) ≠ 0 := by
  have hdom : step1TowerDominance hr H p h j τ := step1TowerDominance_of_tier hτ
  have hne := step1TowerDominance_eval_ne_zero (hr := hr) (by omega : j ≤ m + 1) hdom
    (Sum.inl ⟨j, hjm⟩ : Step1DominanceFamilyIndex H p.1 h)
    (le_of_eq (step1DominanceFamilyChainLength_ignition H p.1 h ⟨j, hjm⟩))
  have hpoly : (step1DominanceFamily H p.2 h (Sum.inl ⟨j, hjm⟩)).poly
      = step1IgnitionPoly H.chains h p.1 j hjm := rfl
  rw [hpoly] at hne
  exact hne

/-- **M4.b — `lem:successor-pole`/`cor:successor-pole-payload` (Laurent core).**
At a tier point `τ ∈ T p h j` the successor selected level
`step1SelectedLevelFunction hr H p h (j+1) hj_succ` has an exact Laurent pole of
order `2κ` at `τ` (with `κ ≥ 1` the current selected-level vanishing order from
C4b) and nonzero leading Laurent coefficient.  This is the explicit normal form
that populates the `normalForm` field of `Step1SuccessorPoleNormalForm` and is the
input consumed by `selectedArcData_of_normalForm`. -/
theorem step1SuccessorLevel_normalForm_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} (p : Step1SeparatedProbe H) (h : Fin k)
    {j : Nat} (hj_succ : j + 1 < m + 1) {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j) :
    ∃ (κ : ℕ) (coeff : ℂ), 1 ≤ κ ∧
      LaurentNormalFormAt (step1SelectedLevelFunction hr H p h (j + 1) hj_succ) τ
        ((2 * κ : ℕ) : ℤ) coeff := by
  classical
  have hj' : j < m + 1 := by omega
  have hjm : j < m := by omega
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  -- exact vanishing order / gate pole of the current selected level (C4b)
  obtain ⟨κ, cκ, hκ, hNFs, _hNFlev⟩ :=
    step1SelectedGate_normalForm_of_tier (hr := hr) (H := H) p h hj' hτ
  -- abbreviations
  set D := step1ActiveStratificationData hr H p with hDdef
  have hD : ActiveHeadSingularStratification hr θ' p.1.1 p.1.2 D :=
    step1ActiveStratificationData_spec hr H p
  set sel := step1SelectedHead H.chains h j with hseldef
  set sel' := step1SelectedHead H.chains h (j + 1) with hsel'def
  set vbad : FormalVar (m + 1) k := ((⟨j, hj'⟩ : Fin (m + 1)), sel) with hvbaddef
  set slopePoly :=
    formalSlope θ' p.1.1 p.1.2 (⟨j + 1, hj_succ⟩ : Fin (m + 1)) sel' with hslopedef
  set s : ℂ -> ℂ := fun z => csig (D.level vbad z) with hsdef
  set cext : ℂ -> FormalVar (m + 1) k -> ℂ :=
    fun z x =>
      if x.1.1 < j then D.gate x z
      else if x = vbad then (0 : ℂ)
      else if x.1.1 = j then csig (D.level x z)
      else 0 with hcextdef
  set Psi : ℂ -> ℂ :=
    fun z => evalFormalPolyComplex (cext z) (coeffOfVar vbad 2 slopePoly) with hPsidef
  set Bet : ℂ -> ℂ :=
    fun z => evalFormalPolyComplex (cext z) (coeffOfVar vbad 1 slopePoly) with hBetdef
  set Gam : ℂ -> ℂ :=
    fun z => evalFormalPolyComplex (cext z) (coeffOfVar vbad 0 slopePoly) with hGamdef
  -- the current selected gate is `s`, with an exact Laurent pole of order `κ`
  have hs : LaurentNormalFormAt s τ (κ : ℤ) cκ⁻¹ := hNFs
  -- basic stratification facts at `τ`
  have hstratum : τ ∈ step1ActiveStratum hr H p h j := by
    have hmem := (step1TierCascadeData hr H).tier_in_stratum hτ
    simpa [step1TierCascadeData] using hmem
  have hτS : τ ∈ D.stratum j := by
    simpa [step1ActiveStratum, hj'] using hstratum
  have hτΩ : τ ∈ D.Omega j := (hD.stratum_closedDiscrete ⟨j, hj'⟩).subset hτS
  have hτ_ne0 : τ ≠ 0 := by
    intro h0
    exact step1ActiveStratum_avoids_nonnegativeRealAxis (hr := hr) hstratum
      (by rw [h0]; exact zero_mem_nonnegativeRealAxis)
  have selactive : sel ∈ activeHeads θ' (⟨j, hj'⟩ : Fin (m + 1)) :=
    (mem_activeHeads θ' (⟨j, hj'⟩) sel).2 (hactiveAll (⟨j, hj'⟩) sel)
  have sel'active : sel' ∈ activeHeads θ' (⟨j + 1, hj_succ⟩ : Fin (m + 1)) :=
    (mem_activeHeads θ' (⟨j + 1, hj_succ⟩) sel').2 (hactiveAll (⟨j + 1, hj_succ⟩) sel')
  have hΩsucc : ∀ᶠ z in puncturedNhds τ, z ∈ D.Omega (j + 1) :=
    step1ActiveStratum_punctured_omega_succ (hr := hr) hj' hstratum
  -- pointwise identification of the concrete gate assignment with the data gate
  have hgate_pt : ∀ (w : ℂ) (v : FormalVar (m + 1) k),
      step1GateAssignment hr H p w v = D.gate v w := by
    intro w v
    obtain ⟨l, a⟩ := v
    exact step1GateAssignment_eq_gate (hr := hr) H p w l a
  -- support facts for the successor slope and its selected-variable coefficients
  have hslopeLT : PolynomialInLayersLT (j + 1) slopePoly :=
    formalSlope_polynomialInLayersLT θ' p.1.1 p.1.2 (⟨j + 1, hj_succ⟩ : Fin (m + 1)) sel'
  have hslopeLE : PolynomialInLayersLE j slopePoly := by
    intro mm hmm x hx
    exact hslopeLT mm hmm x (by omega)
  have hPsi_ign : coeffOfVar vbad 2 slopePoly = step1IgnitionPoly H.chains h p.1 j hjm := rfl
  have hPpsi_lt : PolynomialInLayersLT j (coeffOfVar vbad 2 slopePoly) := by
    rw [hPsi_ign]; exact step1IgnitionPoly_support H.chains h p.1 j hjm
  -- every coordinate of the analytic extension `cext` is analytic at `τ`
  have hcext_an : ∀ x : FormalVar (m + 1) k, AnalyticAt ℂ (fun z => cext z x) τ := by
    intro x
    by_cases h1 : x.1.1 < j
    · have hfun : (fun z => cext z x) = (fun z => D.gate x z) := by
        funext z; simp only [hcextdef, if_pos h1]
      rw [hfun]
      have hxeq : ((⟨x.1.1, lt_trans h1 hj'⟩ : Fin (m + 1)), x.2) = x :=
        Prod.ext_iff.mpr ⟨Fin.ext rfl, rfl⟩
      have hlow := step1LowerGate_analyticAt_of_tier (hr := hr) (H := H) p h hj' hτ h1 x.2
      rw [hxeq] at hlow
      exact hlow
    · by_cases h2 : x = vbad
      · have hfun : (fun z => cext z x) = (fun _ => (0 : ℂ)) := by
          funext z; simp only [hcextdef, if_neg h1, if_pos h2]
        rw [hfun]; exact analyticAt_const
      · by_cases h3 : x.1.1 = j
        · have hfun : (fun z => cext z x) = (fun z => csig (D.level x z)) := by
            funext z; simp only [hcextdef, if_neg h1, if_neg h2, if_pos h3]
          rw [hfun]
          have hx1 : x.1 = (⟨j, hj'⟩ : Fin (m + 1)) := Fin.ext h3
          have hx2 : x.2 ≠ sel := by
            intro hc; apply h2; rw [hvbaddef]; exact Prod.ext_iff.mpr ⟨hx1, hc⟩
          have hnotPi : D.level x τ ∉ Pi := by
            have hnp := step1NonselectedLevel_notMem_Pi_of_tier (hr := hr) (H := H)
              p h hj' hτ x.2 hx2
            have hxpair : ((⟨j, hj'⟩ : Fin (m + 1)), x.2) = x :=
              Prod.ext_iff.mpr ⟨hx1.symm, rfl⟩
            rwa [hxpair] at hnp
          have hact : x.2 ∈ activeHeads θ' x.1 :=
            (mem_activeHeads θ' x.1 x.2).2 (hactiveAll x.1 x.2)
          have hτΩx : τ ∈ D.Omega x.1.1 := by rw [h3]; exact hτΩ
          have hlevAn : AnalyticAt ℂ (D.level x) τ :=
            hD.level_holomorphic x.1 x.2 hact τ hτΩx
          have hcomp := (csig_analyticAt_of_notMem_Pi hnotPi).comp hlevAn
          simpa [Function.comp] using hcomp
        · have hfun : (fun z => cext z x) = (fun _ => (0 : ℂ)) := by
            funext z; simp only [hcextdef, if_neg h1, if_neg h2, if_neg h3]
          rw [hfun]; exact analyticAt_const
  -- the three selected-variable coefficients are analytic at `τ`
  have hPsi_an : AnalyticAt ℂ Psi τ := by
    show AnalyticAt ℂ (fun z => evalFormalPolyComplex (cext z) (coeffOfVar vbad 2 slopePoly)) τ
    exact evalFormalPolyComplex_analyticAt_of_all _ hcext_an
  have hBet_an : AnalyticAt ℂ Bet τ := by
    show AnalyticAt ℂ (fun z => evalFormalPolyComplex (cext z) (coeffOfVar vbad 1 slopePoly)) τ
    exact evalFormalPolyComplex_analyticAt_of_all _ hcext_an
  have hGam_an : AnalyticAt ℂ Gam τ := by
    show AnalyticAt ℂ (fun z => evalFormalPolyComplex (cext z) (coeffOfVar vbad 0 slopePoly)) τ
    exact evalFormalPolyComplex_analyticAt_of_all _ hcext_an
  -- leading coefficient is nonzero: `Ψ_{j+1}(τ) ≠ 0`
  have hΨτ_ne : Psi τ ≠ 0 := by
    have hval : Psi τ = evalFormalPolyComplex (step1GateAssignment hr H p τ)
        (coeffOfVar vbad 2 slopePoly) := by
      show evalFormalPolyComplex (cext τ) (coeffOfVar vbad 2 slopePoly)
        = evalFormalPolyComplex (step1GateAssignment hr H p τ) (coeffOfVar vbad 2 slopePoly)
      refine evalFormalPolyComplex_congr_on_vars (coeffOfVar vbad 2 slopePoly) ?_
      intro v hv
      have hvlt : v.1.1 < j := mem_vars_layer_lt_of_polynomialInLayersLT hPpsi_lt hv
      rw [hgate_pt τ v]
      simp only [hcextdef, if_pos hvlt]
    rw [hval, hPsi_ign]
    exact step1SuccessorLeadingFactor_ne_zero_of_tier (hr := hr) (H := H) p h hjm hτ
  -- assemble the Laurent normal form of the model function
  have hz0 : LaurentNormalFormAt (fun z : ℂ => z) τ 0 τ :=
    laurentNormalFormAt_zero_of_analyticAt (a := fun z : ℂ => z) analyticAt_id hτ_ne0
  have hΨ0 : LaurentNormalFormAt Psi τ 0 (Psi τ) :=
    laurentNormalFormAt_zero_of_analyticAt hPsi_an hΨτ_ne
  have hΨs : LaurentNormalFormAt (fun z => Psi z * s z) τ (0 + (κ : ℤ)) (Psi τ * cκ⁻¹) :=
    hΨ0.mul hs
  have hΨsβ : LaurentNormalFormAt (fun z => Psi z * s z + Bet z) τ
      (0 + (κ : ℤ)) (Psi τ * cκ⁻¹) :=
    hΨs.add_analyticAt hBet_an (by rw [zero_add]; exact_mod_cast hκ)
  have hs2 : LaurentNormalFormAt (fun z => s z * (Psi z * s z + Bet z)) τ
      ((κ : ℤ) + (0 + (κ : ℤ))) (cκ⁻¹ * (Psi τ * cκ⁻¹)) :=
    hs.mul hΨsβ
  have hzs2 : LaurentNormalFormAt (fun z => z * (s z * (Psi z * s z + Bet z))) τ
      (0 + ((κ : ℤ) + (0 + (κ : ℤ)))) (τ * (cκ⁻¹ * (Psi τ * cκ⁻¹))) :=
    hz0.mul hs2
  have hγ' : AnalyticAt ℂ (fun z => z * Gam z + (logScale r : ℂ)) τ :=
    (analyticAt_id.mul hGam_an).add analyticAt_const
  have hmodel : LaurentNormalFormAt
      (fun z => z * (s z * (Psi z * s z + Bet z)) + (z * Gam z + (logScale r : ℂ))) τ
      (0 + ((κ : ℤ) + (0 + (κ : ℤ)))) (τ * (cκ⁻¹ * (Psi τ * cκ⁻¹))) :=
    hzs2.add_analyticAt hγ' (by have := hκ; omega)
  -- the model agrees with the successor selected level on a punctured neighborhood
  have hmf :
      (fun z => z * (s z * (Psi z * s z + Bet z)) + (z * Gam z + (logScale r : ℂ)))
        =ᶠ[nhdsWithin τ ({τ}ᶜ : Set ℂ)]
      step1SelectedLevelFunction hr H p h (j + 1) hj_succ := by
    filter_upwards [hΩsucc] with z hz
    -- level formula for the successor selected level on `Ω_{j+1}`
    have hf_eq : step1SelectedLevelFunction hr H p h (j + 1) hj_succ z
        = z * evalFormalPolyComplex (step1GateAssignment hr H p z) slopePoly
          + (logScale r : ℂ) :=
      hD.level_formula (⟨j + 1, hj_succ⟩ : Fin (m + 1)) sel' sel'active hz
    -- quadratic split of the slope in the selected layer-`j` variable
    have hDdeg : MvPolynomial.degreeOf vbad slopePoly ≤ 2 :=
      blockDegreeLE_degreeOf_le
        (formalSlope_blockDegree_two θ' p.1.1 p.1.2 (⟨j + 1, hj_succ⟩ : Fin (m + 1)) sel')
    have hsplit : evalFormalPolyComplex (step1GateAssignment hr H p z) slopePoly
        = evalFormalPolyComplex (step1GateAssignment hr H p z) (coeffOfVar vbad 0 slopePoly)
          + evalFormalPolyComplex (step1GateAssignment hr H p z) (coeffOfVar vbad 1 slopePoly)
              * step1GateAssignment hr H p z vbad
          + evalFormalPolyComplex (step1GateAssignment hr H p z) (coeffOfVar vbad 2 slopePoly)
              * (step1GateAssignment hr H p z vbad) ^ 2 := by
      rw [evalFormalPolyComplex_eq_sum_coeffOfVar hDdeg (step1GateAssignment hr H p z)]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      ring
    -- the selected layer-`j` gate value is `s z`
    have hg_s : step1GateAssignment hr H p z vbad = s z := by
      have h1 : step1GateAssignment hr H p z vbad = D.gate vbad z := hgate_pt z vbad
      have h2 : D.gate vbad z = csig (D.level vbad z) := by
        rw [hvbaddef]; exact hD.gate_formula (⟨j, hj'⟩ : Fin (m + 1)) sel selactive hz
      rw [h1, h2, hsdef]
    -- the extended assignment agrees with the concrete one on layers `≤ j` off `vbad`
    have hagree : ∀ v : FormalVar (m + 1) k, v.1.1 ≤ j → v ≠ vbad →
        step1GateAssignment hr H p z v = cext z v := by
      intro v hvle hvne
      rw [hgate_pt z v]
      by_cases h1 : v.1.1 < j
      · simp only [hcextdef, if_pos h1]
      · have h3 : v.1.1 = j := le_antisymm hvle (not_lt.mp h1)
        have hvactive : v.2 ∈ activeHeads θ' v.1 :=
          (mem_activeHeads θ' v.1 v.2).2 (hactiveAll v.1 v.2)
        have hzΩ : z ∈ D.Omega (v.1.1 + 1) := by rw [h3]; exact hz
        have hgf := hD.gate_formula v.1 v.2 hvactive hzΩ
        simp only [hcextdef, if_neg h1, if_neg hvne, if_pos h3]
        exact hgf
    have hpsi_eq : evalFormalPolyComplex (step1GateAssignment hr H p z)
        (coeffOfVar vbad 2 slopePoly) = Psi z := by
      show evalFormalPolyComplex (step1GateAssignment hr H p z) (coeffOfVar vbad 2 slopePoly)
        = evalFormalPolyComplex (cext z) (coeffOfVar vbad 2 slopePoly)
      refine evalFormalPolyComplex_congr_on_vars (coeffOfVar vbad 2 slopePoly) ?_
      intro v hv
      exact hagree v
        (mem_vars_layer_le_of_polynomialInLayersLE (coeffOfVar_support_subset hslopeLE) hv)
        (fun hveq => coeffOfVar_notMem_vars (hveq ▸ hv))
    have hbet_eq : evalFormalPolyComplex (step1GateAssignment hr H p z)
        (coeffOfVar vbad 1 slopePoly) = Bet z := by
      show evalFormalPolyComplex (step1GateAssignment hr H p z) (coeffOfVar vbad 1 slopePoly)
        = evalFormalPolyComplex (cext z) (coeffOfVar vbad 1 slopePoly)
      refine evalFormalPolyComplex_congr_on_vars (coeffOfVar vbad 1 slopePoly) ?_
      intro v hv
      exact hagree v
        (mem_vars_layer_le_of_polynomialInLayersLE (coeffOfVar_support_subset hslopeLE) hv)
        (fun hveq => coeffOfVar_notMem_vars (hveq ▸ hv))
    have hgam_eq : evalFormalPolyComplex (step1GateAssignment hr H p z)
        (coeffOfVar vbad 0 slopePoly) = Gam z := by
      show evalFormalPolyComplex (step1GateAssignment hr H p z) (coeffOfVar vbad 0 slopePoly)
        = evalFormalPolyComplex (cext z) (coeffOfVar vbad 0 slopePoly)
      refine evalFormalPolyComplex_congr_on_vars (coeffOfVar vbad 0 slopePoly) ?_
      intro v hv
      exact hagree v
        (mem_vars_layer_le_of_polynomialInLayersLE (coeffOfVar_support_subset hslopeLE) hv)
        (fun hveq => coeffOfVar_notMem_vars (hveq ▸ hv))
    rw [hf_eq, hsplit, hg_s, hpsi_eq, hbet_eq, hgam_eq]
    ring
  exact ⟨κ, _, hκ, laurentNF_order_cast (hmodel.congr hmf) (by push_cast; ring)⟩

/-! ## K06B.C7.b — sibling non-identity (pure algebra)

The single *ungated* piece of `lem:tier-local`'s sibling branch: on the
successor stratification domain `Ω_{j+1}` the successor selected level differs
from every nonselected sibling level.  This is a pure-algebra statement — no arc
data, dominance, or singular-set input — and feeds the K04E sibling-avoidance
hypothesis `step1SiblingLevelFamily` (index `0` selected, index `q.succ` the
`q`-th nonselected sibling).

The proof combines the affine level formula on `Ω_{j+1}` with the corner-slope
separation `(R3)` at the probe: if the two levels agreed on `Ω_{j+1}`, then
`z · g(z) = 0` there with `g(z)` the evaluated slope difference; `g` is analytic
at the origin (which lies in every `Ω_n`), and vanishes on the punctured domain,
so `g(0) = 0`; but `g(0)` is exactly the corner-slope difference
`cornerSlopeDiffAt r θ' l c sel'`, which is nonzero by `(R3)`. -/

/-- Complex evaluation of a formal polynomial respects subtraction of polynomials. -/
theorem evalFormalPolyComplex_sub {L kk : Nat} (η : FormalVar L kk → ℂ)
    (a b : FormalPoly L kk) :
    evalFormalPolyComplex η (a - b)
      = evalFormalPolyComplex η a - evalFormalPolyComplex η b := by
  simp only [evalFormalPolyComplex, MvPolynomial.eval₂_sub]

/-- **K06B.C7.b — sibling non-identity (pure algebra).**  On the successor
stratification domain `Ω_{j+1}`, the successor selected level
(`step1SiblingLevelFamily … 0`) is not identically equal to any nonselected
sibling level (`step1SiblingLevelFamily … q.succ`).  The obstruction is the
corner-slope separation `(R3)` carried by the separated probe `p`. -/
theorem step1SiblingLevel_not_identical_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (p : Step1SeparatedProbe H) (h : Fin k) {j : Nat} {τ : ℂ}
    (hj : j < (step1TierCascadeData hr H).depth)
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j)
    (hsucc : j + 1 < (step1TierCascadeData hr H).depth)
    (q : Fin (step1NonselectedSiblingCount (step1SelectedHead H.chains h (j + 1)))) :
    ¬ Set.EqOn
        (step1SiblingLevelFamily hr H p h (by simpa [step1TierCascadeData] using hsucc)
          (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h (j + 1))) q.succ)
        (step1SiblingLevelFamily hr H p h (by simpa [step1TierCascadeData] using hsucc)
          (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h (j + 1))) 0)
        ((step1ActiveStratificationData hr H p).Omega (j + 1)) := by
  classical
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  have hproof : j + 1 < m + 1 := by
    have hd := step1TierCascadeData_depth hr H; omega
  have hD := step1ActiveStratificationData_spec hr H p
  set D := step1ActiveStratificationData hr H p with hDdef
  -- `sel'/sib/c₀/l` are `let`-bindings (not `set`) so that they do not revert the
  -- sibling index `q`, whose type mentions `step1SelectedHead H.chains h (j + 1)`
  let sel' : Fin k := step1SelectedHead H.chains h (j + 1)
  let sib := step1NonselectedSiblingEnumeration sel'
  let l : Fin (m + 1) := ⟨j + 1, hproof⟩
  let c₀ : Fin k := (sib q).1
  have hc₀ : c₀ ≠ sel' := (sib q).2
  have hc₀active : c₀ ∈ activeHeads θ' l := (mem_activeHeads θ' l c₀).2 (hactiveAll l c₀)
  have hsel'active : sel' ∈ activeHeads θ' l := (mem_activeHeads θ' l sel').2 (hactiveAll l sel')
  intro hEq
  -- the two families reduce (definitionally) to the selected level and the `c₀`
  -- sibling level via `Fin.cases`
  have hpoint : Set.EqOn (D.level (l, c₀)) (D.level (l, sel')) (D.Omega (j + 1)) := hEq
  -- the evaluated slope difference and its analytic packaging
  set slopeDiff : FormalPoly (m + 1) k :=
    formalSlope θ' p.1.1 p.1.2 l c₀ - formalSlope θ' p.1.1 p.1.2 l sel' with hslopeDiffdef
  set g : ℂ → ℂ :=
    fun z => evalFormalPolyComplex (activeComplexGateAssignment θ' D z) slopeDiff with hgdef
  -- off the origin the slope evaluations coincide, so `g` vanishes there
  have hzero : ∀ z ∈ D.Omega (j + 1), z ≠ 0 → g z = 0 := by
    intro z hz hzne
    have hval_c : D.level (l, c₀) z
        = z * evalFormalPolyComplex (activeComplexGateAssignment θ' D z)
            (formalSlope θ' p.1.1 p.1.2 l c₀) + (logScale r : ℂ) :=
      hD.level_formula l c₀ hc₀active hz
    have hval_s : D.level (l, sel') z
        = z * evalFormalPolyComplex (activeComplexGateAssignment θ' D z)
            (formalSlope θ' p.1.1 p.1.2 l sel') + (logScale r : ℂ) :=
      hD.level_formula l sel' hsel'active hz
    have heq := hpoint hz
    rw [hval_c, hval_s] at heq
    have h1 : z * evalFormalPolyComplex (activeComplexGateAssignment θ' D z)
          (formalSlope θ' p.1.1 p.1.2 l c₀)
        = z * evalFormalPolyComplex (activeComplexGateAssignment θ' D z)
          (formalSlope θ' p.1.1 p.1.2 l sel') := add_right_cancel heq
    have h2 : evalFormalPolyComplex (activeComplexGateAssignment θ' D z)
          (formalSlope θ' p.1.1 p.1.2 l c₀)
        = evalFormalPolyComplex (activeComplexGateAssignment θ' D z)
          (formalSlope θ' p.1.1 p.1.2 l sel') := mul_left_cancel₀ hzne h1
    show evalFormalPolyComplex (activeComplexGateAssignment θ' D z) slopeDiff = 0
    rw [hslopeDiffdef, evalFormalPolyComplex_sub, h2, sub_self]
  -- every gate coordinate is analytic at `0` (the origin lies in every `Ω_n`)
  have hA_an : ∀ x : FormalVar (m + 1) k,
      AnalyticAt ℂ (fun z => activeComplexGateAssignment θ' D z x) 0 := by
    intro x
    have hfun : (fun z => activeComplexGateAssignment θ' D z x) = D.gate x := by
      funext z
      rw [activeComplexGateAssignment_eq_gate_of_all_heads_active D z hactiveAll]
    rw [hfun]
    have hact : x.2 ∈ activeHeads θ' x.1 := (mem_activeHeads θ' x.1 x.2).2 (hactiveAll x.1 x.2)
    have h0Ωx : (0 : ℂ) ∈ D.Omega (x.1.1 + 1) :=
      hD.nonnegative_axis_subset (x.1.1 + 1) (by have := x.1.isLt; omega)
        zero_mem_nonnegativeRealAxis
    exact hD.gate_holomorphic x.1 x.2 hact 0 h0Ωx
  have hg_an : AnalyticAt ℂ g 0 :=
    evalFormalPolyComplex_analyticAt_of_all
      (η := fun z => activeComplexGateAssignment θ' D z) slopeDiff hA_an
  -- continuity at `0` together with punctured vanishing pins `g 0 = 0`
  have h0Ω : (0 : ℂ) ∈ D.Omega (j + 1) :=
    hD.nonnegative_axis_subset (j + 1) (le_of_lt hproof) zero_mem_nonnegativeRealAxis
  have hopen : IsOpen (D.Omega (j + 1)) := (hD.domain (j + 1) (le_of_lt hproof)).isOpen
  have hg0 : g 0 = 0 := by
    have hev : g =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ)] fun _ => (0 : ℂ) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds h0Ω), self_mem_nhdsWithin]
        with z hzΩ hz0
      exact hzero z hzΩ (by simpa using hz0)
    have h1 : Tendsto g (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ)) (nhds (g 0)) :=
      hg_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto g (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ)) (nhds (0 : ℂ)) := by
      rw [tendsto_congr' hev]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- evaluate `g 0` at the all-`alpha` corner assignment, giving the `(R3)` bilinear form
  have hg0_corner : g 0 = (cornerSlopeDiffAt r θ' l c₀ sel' p.1 : ℂ) := by
    have hA0 : activeComplexGateAssignment θ' D 0
        = fun _ : FormalVar (m + 1) k => (alpha r : ℂ) := by
      rw [activeComplexGateAssignment_eq_gate_of_all_heads_active D 0 hactiveAll]
      funext x
      exact hD.gate_zero x.1 x.2 ((mem_activeHeads θ' x.1 x.2).2 (hactiveAll x.1 x.2))
    show evalFormalPolyComplex (activeComplexGateAssignment θ' D 0) slopeDiff
        = (cornerSlopeDiffAt r θ' l c₀ sel' p.1 : ℂ)
    rw [hA0, hslopeDiffdef]
    exact evalFormal_slopeDiff_corner r θ' p.1 l c₀ sel'
  -- contradiction with corner-slope separation `(R3)`
  have hcorner0 : cornerSlopeDiffAt r θ' l c₀ sel' p.1 = 0 := by
    have hcast : (cornerSlopeDiffAt r θ' l c₀ sel' p.1 : ℂ) = 0 := by
      rw [← hg0_corner]; exact hg0
    exact_mod_cast hcast
  exact p.2.2.2 l c₀ sel' hc₀ hcorner0

/-- **M4.b — `cor:successor-pole-payload` (full record).**  From tier membership
`τ ∈ T p h j` build the successor selected-level pole normal form record at layer
`j+1`: exact pole order `q = 2κ`, nonzero leading Laurent coefficient, one punctured
stratification disc `D^×(τ,ρ) ⊆ Ω'_{j+1}`, the Laurent tie
(`step1SuccessorLevel_normalForm_of_tier`), and the selected-arc package
(`selectedArcData_of_normalForm` upgraded to `ArcStructureResult` via
`SelectedArcData.toArcStructureResult`).  The holomorphy input to the arc package is
`level_holomorphic` restricted to the punctured disc. -/
noncomputable def step1SuccessorPoleNormalForm_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} (p : Step1SeparatedProbe H) (h : Fin k)
    {j : Nat} {τ : ℂ}
    (hj : j < (step1TierCascadeData hr H).depth)
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j)
    (hsucc : j + 1 < (step1TierCascadeData hr H).depth) :
    Step1SuccessorPoleNormalForm hr H p h (j + 1)
      (by simpa [step1TierCascadeData] using hsucc) τ := by
  classical
  have hj_succ : j + 1 < m + 1 := by simpa [step1TierCascadeData] using hsucc
  have hj' : j < m + 1 := by omega
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  have hD := step1ActiveStratificationData_spec hr H p
  -- Laurent core (order `2κ`, nonzero leading coeff); extract via `.choose`
  -- since building the data-valued record cannot pattern-match a `Prop` existential
  have hex := step1SuccessorLevel_normalForm_of_tier (hr := hr) (H := H) p h hj_succ hτ
  have hspec := hex.choose_spec.choose_spec
  have hκ : 1 ≤ hex.choose := hspec.1
  have hNF : LaurentNormalFormAt (step1SelectedLevelFunction hr H p h (j + 1) hj_succ) τ
      ((2 * hex.choose : ℕ) : ℤ) hex.choose_spec.choose := hspec.2
  have hm2 : 1 ≤ 2 * hex.choose := by omega
  -- one punctured disc inside `Ω_{j+1}`
  have hstratum : τ ∈ step1ActiveStratum hr H p h j := by
    have hmem := (step1TierCascadeData hr H).tier_in_stratum hτ
    simpa [step1TierCascadeData] using hmem
  have hΩsucc : ∀ᶠ z in puncturedNhds τ,
      z ∈ (step1ActiveStratificationData hr H p).Omega (j + 1) :=
    step1ActiveStratum_punctured_omega_succ (hr := hr) hj' hstratum
  have hmem := Metric.mem_nhdsWithin_iff.mp hΩsucc
  have hρ0 : 0 < hmem.choose := hmem.choose_spec.1
  have hsub := hmem.choose_spec.2
  have hpunc_sub : puncturedDisc τ hmem.choose
      ⊆ (step1ActiveStratificationData hr H p).Omega (j + 1) := by
    intro z hz
    exact hsub ⟨Metric.mem_ball.mpr hz.2, hz.1⟩
  -- holomorphy of the successor selected level on the punctured disc
  have sel'active :
      step1SelectedHead H.chains h (j + 1)
        ∈ activeHeads θ' (⟨j + 1, hj_succ⟩ : Fin (m + 1)) :=
    (mem_activeHeads θ' (⟨j + 1, hj_succ⟩) (step1SelectedHead H.chains h (j + 1))).2
      (hactiveAll (⟨j + 1, hj_succ⟩) (step1SelectedHead H.chains h (j + 1)))
  have hHol : AnalyticOnNhd ℂ (step1SelectedLevelFunction hr H p h (j + 1) hj_succ)
      (puncturedDisc τ hmem.choose) :=
    (hD.level_holomorphic (⟨j + 1, hj_succ⟩) (step1SelectedHead H.chains h (j + 1))
      sel'active).mono hpunc_sub
  exact
    { q := 2 * hex.choose
      q_pos := hm2
      coeff := hex.choose_spec.choose
      radius := hmem.choose
      radius_pos := hρ0
      punctured_subset_successorOmega := hpunc_sub
      normalForm := hNF
      arcStructure :=
        (Classical.choice
          (selectedArcData_of_normalForm (m := 2 * hex.choose) hm2 hρ0 hHol hNF)).toArcStructureResult
          hm2 }

/-! ## K06B.C7 (a/c/d) — sibling normal forms and the canonical avoidance result

The remaining tier-local sibling bridge.  On the successor stratification domain
`Ω_{j+1}` every nonselected sibling level has a Laurent pole of order at most the
selected pole order `2κ` (C7.a), the finite sibling family satisfies the
`SiblingAvoidanceHypotheses` record (C7.c), and the K04E sequence-window
endpoint (`siblingAvoidanceResult_of_normalForm`, C6) assembles the
`SiblingAvoidanceResult` (C7.d). -/

/-- A meromorphic function of finite integer order `n` has a Laurent normal form of
Laurent-pole order `-n` and (nonzero) leading coefficient `g ξ`. -/
theorem laurentNormalFormAt_of_meromorphicOrder_int {f : ℂ -> ℂ} {ξ : ℂ} {n : ℤ}
    (hmero : MeromorphicAt f ξ) (hord : meromorphicOrderAt f ξ = (n : ℤ)) :
    ∃ cc : ℂ, LaurentNormalFormAt f ξ (-n) cc := by
  obtain ⟨g, hg, hgξ, hfg⟩ := (meromorphicOrderAt_eq_int_iff hmero).1 hord
  refine ⟨g ξ, hgξ, g, hg, rfl, ?_⟩
  filter_upwards [hfg] with z hz
  rw [hz]
  simp [smul_eq_mul, mul_comm, neg_neg]

/-- A meromorphic function that is not eventually zero, with Laurent pole order at
most `N`, has a Laurent normal form of order `μ ≤ N`. -/
theorem laurentNormalFormAt_of_meromorphic_orderBound {f : ℂ -> ℂ} {ξ : ℂ} {N : ℤ}
    (hmero : MeromorphicAt f ξ) (hne : meromorphicOrderAt f ξ ≠ ⊤)
    (hbound : ((-N : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f ξ) :
    ∃ (μ : ℤ) (cc : ℂ), μ ≤ N ∧ LaurentNormalFormAt f ξ μ cc := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨cc, hNF⟩ := laurentNormalFormAt_of_meromorphicOrder_int hmero hn.symm
  refine ⟨-n, cc, ?_, hNF⟩
  have hle : ((-N : ℤ) : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ) := hn ▸ hbound
  have hNn : (-N : ℤ) ≤ (n : ℤ) := by exact_mod_cast hle
  omega

/-- Identity-theorem `≠ ⊤` for a level function: an analytic function on a plane
domain `U` that does not vanish at `0 ∈ U` and is analytic on a punctured disc
`D^×(ξ,ρ) ⊆ U` cannot vanish on a whole punctured neighborhood of `ξ`, hence its
meromorphic order at `ξ` is finite. -/
theorem meromorphicOrderAt_ne_top_of_domain {f : ℂ -> ℂ} {U : Set ℂ} {ξ : ℂ} {ρ : ℝ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) (h0 : (0 : ℂ) ∈ U)
    (hf0 : f 0 ≠ 0) (hρ : 0 < ρ) (hsub : puncturedDisc ξ ρ ⊆ U) :
    meromorphicOrderAt f ξ ≠ ⊤ := by
  intro htop
  have hzero0 : ∀ᶠ z in nhdsWithin ξ ({ξ}ᶜ : Set ℂ), f z = 0 :=
    meromorphicOrderAt_eq_top_iff.1 htop
  obtain ⟨ε, hε, hzeroS⟩ := Metric.mem_nhdsWithin_iff.mp hzero0
  have hzero : ∀ z : ℂ, dist z ξ < ε → z ≠ ξ → f z = 0 := by
    intro z hzd hzne
    exact hzeroS ⟨Metric.mem_ball.mpr hzd, by simpa using hzne⟩
  set rr : ℝ := min ε ρ with hrr
  have hrr0 : 0 < rr := lt_min hε hρ
  set w : ℂ := ξ + ((rr / 2 : ℝ) : ℂ) with hw
  have hdwξ : dist w ξ = rr / 2 := by
    rw [hw, Complex.dist_eq, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hwU : w ∈ U := by
    apply hsub
    refine ⟨?_, ?_⟩
    · intro hwξ
      rw [hwξ, dist_self] at hdwξ
      linarith
    · rw [hdwξ]
      have : rr ≤ ρ := min_le_right _ _
      linarith
  -- `f` vanishes on the ball `B(w, rr/4)`, which avoids `ξ` and stays in `B(ξ,ε)`
  have hball_zero : ∀ z ∈ Metric.ball w (rr / 4), f z = 0 := by
    intro z hz
    have hzw : dist z w < rr / 4 := Metric.mem_ball.mp hz
    have hzξ : dist z ξ < ε := by
      have := dist_triangle z w ξ
      rw [hdwξ] at this
      have hle : rr ≤ ε := min_le_left _ _
      linarith
    have hzne : z ≠ ξ := by
      intro hzeq
      rw [hzeq, dist_comm, hdwξ] at hzw
      linarith
    exact hzero z hzξ hzne
  have hfreq : ∃ᶠ z in nhdsWithin w ({w}ᶜ : Set ℂ), f z = 0 := by
    have hev : ∀ᶠ z in nhds w, f z = 0 :=
      Metric.eventually_nhds_iff.mpr
        ⟨rr / 4, by positivity, fun {y} hy => hball_zero y (Metric.mem_ball.mpr hy)⟩
    exact (hev.filter_mono nhdsWithin_le_nhds).frequently
  have hEqOn : Set.EqOn f 0 U :=
    hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hwU hfreq
  exact hf0 (by simpa using hEqOn h0)

/-- **K06B.C7 slope-model helper.**  At a tier point `τ ∈ T p h j`, for any head
`a`, the layer-`j+1` level `H'_{j+1,a}` agrees on a punctured neighborhood of `τ`
with the explicit quadratic-in-`s` model `z ↦ z·(Ψ_a(z)·s(z)² + β_a(z)·s(z) +
γ_a(z)) + log r`, where `s = csig ∘ (selected layer-`j` level)` is the blowing-up
selected gate and `Ψ_a, β_a, γ_a` are the (analytic) selected-variable
coefficients of the successor slope.  Moreover `Ψ_a(τ)` equals the concrete
gate-assignment evaluation of the `ζ_j²` coefficient — the ignition polynomial for
the selected head. -/
theorem step1LayerLevelSlopeModel_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} (p : Step1SeparatedProbe H) (h : Fin k)
    {j : Nat} (hj' : j < m + 1) (hj_succ : j + 1 < m + 1) {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j) (a : Fin k) :
    ∃ (Psi Bet Gam : ℂ -> ℂ),
      AnalyticAt ℂ Psi τ ∧ AnalyticAt ℂ Bet τ ∧ AnalyticAt ℂ Gam τ ∧
      Psi τ = evalFormalPolyComplex (step1GateAssignment hr H p τ)
        (coeffOfVar ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) 2
          (formalSlope θ' p.1.1 p.1.2 (⟨j + 1, hj_succ⟩ : Fin (m + 1)) a)) ∧
      (step1ActiveStratificationData hr H p).level (⟨j + 1, hj_succ⟩, a)
        =ᶠ[nhdsWithin τ ({τ}ᶜ : Set ℂ)]
        (fun z => z * (Psi z *
              (csig ((step1ActiveStratificationData hr H p).level
                ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) z)) ^ 2
            + Bet z * csig ((step1ActiveStratificationData hr H p).level
                ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) z)
            + Gam z) + (logScale r : ℂ)) := by
  classical
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  set D := step1ActiveStratificationData hr H p with hDdef
  have hD : ActiveHeadSingularStratification hr θ' p.1.1 p.1.2 D :=
    step1ActiveStratificationData_spec hr H p
  set sel := step1SelectedHead H.chains h j with hseldef
  set vbad : FormalVar (m + 1) k := ((⟨j, hj'⟩ : Fin (m + 1)), sel) with hvbaddef
  have hvbad_layer : vbad.1.1 = j := by rw [hvbaddef]
  set slopePoly :=
    formalSlope θ' p.1.1 p.1.2 (⟨j + 1, hj_succ⟩ : Fin (m + 1)) a with hslopedef
  set s : ℂ -> ℂ := fun z => csig (D.level vbad z) with hsdef
  set cext : ℂ -> FormalVar (m + 1) k -> ℂ :=
    fun z x =>
      if x.1.1 < j then D.gate x z
      else if x = vbad then (0 : ℂ)
      else if x.1.1 = j then csig (D.level x z)
      else 0 with hcextdef
  set Psi : ℂ -> ℂ :=
    fun z => evalFormalPolyComplex (cext z) (coeffOfVar vbad 2 slopePoly) with hPsidef
  set Bet : ℂ -> ℂ :=
    fun z => evalFormalPolyComplex (cext z) (coeffOfVar vbad 1 slopePoly) with hBetdef
  set Gam : ℂ -> ℂ :=
    fun z => evalFormalPolyComplex (cext z) (coeffOfVar vbad 0 slopePoly) with hGamdef
  -- basic stratification facts at `τ`
  have hstratum : τ ∈ step1ActiveStratum hr H p h j := by
    have hmem := (step1TierCascadeData hr H).tier_in_stratum hτ
    simpa [step1TierCascadeData] using hmem
  have hτS : τ ∈ D.stratum j := by
    simpa [step1ActiveStratum, hj'] using hstratum
  have hτΩ : τ ∈ D.Omega j := (hD.stratum_closedDiscrete ⟨j, hj'⟩).subset hτS
  have selactive : sel ∈ activeHeads θ' (⟨j, hj'⟩ : Fin (m + 1)) :=
    (mem_activeHeads θ' (⟨j, hj'⟩) sel).2 (hactiveAll (⟨j, hj'⟩) sel)
  have aactive : a ∈ activeHeads θ' (⟨j + 1, hj_succ⟩ : Fin (m + 1)) :=
    (mem_activeHeads θ' (⟨j + 1, hj_succ⟩) a).2 (hactiveAll (⟨j + 1, hj_succ⟩) a)
  have hΩsucc : ∀ᶠ z in puncturedNhds τ, z ∈ D.Omega (j + 1) :=
    step1ActiveStratum_punctured_omega_succ (hr := hr) hj' hstratum
  have hgate_pt : ∀ (w : ℂ) (v : FormalVar (m + 1) k),
      step1GateAssignment hr H p w v = D.gate v w := by
    intro w v
    obtain ⟨l, b⟩ := v
    exact step1GateAssignment_eq_gate (hr := hr) H p w l b
  have hslopeLT : PolynomialInLayersLT (j + 1) slopePoly :=
    formalSlope_polynomialInLayersLT θ' p.1.1 p.1.2 (⟨j + 1, hj_succ⟩ : Fin (m + 1)) a
  have hslopeLE : PolynomialInLayersLE j slopePoly := by
    intro mm hmm x hx
    exact hslopeLT mm hmm x (by omega)
  have hbd2 : BlockDegreeLE 2 slopePoly :=
    formalSlope_blockDegree_two θ' p.1.1 p.1.2 (⟨j + 1, hj_succ⟩ : Fin (m + 1)) a
  have hPpsi_lt : PolynomialInLayersLT j (coeffOfVar vbad 2 slopePoly) :=
    coeffOfVar_top_polynomialInLayersLT vbad hvbad_layer hbd2 hslopeLE
  -- every coordinate of the analytic extension `cext` is analytic at `τ`
  have hcext_an : ∀ x : FormalVar (m + 1) k, AnalyticAt ℂ (fun z => cext z x) τ := by
    intro x
    by_cases h1 : x.1.1 < j
    · have hfun : (fun z => cext z x) = (fun z => D.gate x z) := by
        funext z; simp only [hcextdef, if_pos h1]
      rw [hfun]
      have hxeq : ((⟨x.1.1, lt_trans h1 hj'⟩ : Fin (m + 1)), x.2) = x :=
        Prod.ext_iff.mpr ⟨Fin.ext rfl, rfl⟩
      have hlow := step1LowerGate_analyticAt_of_tier (hr := hr) (H := H) p h hj' hτ h1 x.2
      rw [hxeq] at hlow
      exact hlow
    · by_cases h2 : x = vbad
      · have hfun : (fun z => cext z x) = (fun _ => (0 : ℂ)) := by
          funext z; simp only [hcextdef, if_neg h1, if_pos h2]
        rw [hfun]; exact analyticAt_const
      · by_cases h3 : x.1.1 = j
        · have hfun : (fun z => cext z x) = (fun z => csig (D.level x z)) := by
            funext z; simp only [hcextdef, if_neg h1, if_neg h2, if_pos h3]
          rw [hfun]
          have hx1 : x.1 = (⟨j, hj'⟩ : Fin (m + 1)) := Fin.ext h3
          have hx2 : x.2 ≠ sel := by
            intro hc; apply h2; rw [hvbaddef]; exact Prod.ext_iff.mpr ⟨hx1, hc⟩
          have hnotPi : D.level x τ ∉ Pi := by
            have hnp := step1NonselectedLevel_notMem_Pi_of_tier (hr := hr) (H := H)
              p h hj' hτ x.2 hx2
            have hxpair : ((⟨j, hj'⟩ : Fin (m + 1)), x.2) = x :=
              Prod.ext_iff.mpr ⟨hx1.symm, rfl⟩
            rwa [hxpair] at hnp
          have hact : x.2 ∈ activeHeads θ' x.1 :=
            (mem_activeHeads θ' x.1 x.2).2 (hactiveAll x.1 x.2)
          have hτΩx : τ ∈ D.Omega x.1.1 := by rw [h3]; exact hτΩ
          have hlevAn : AnalyticAt ℂ (D.level x) τ :=
            hD.level_holomorphic x.1 x.2 hact τ hτΩx
          have hcomp := (csig_analyticAt_of_notMem_Pi hnotPi).comp hlevAn
          simpa [Function.comp] using hcomp
        · have hfun : (fun z => cext z x) = (fun _ => (0 : ℂ)) := by
            funext z; simp only [hcextdef, if_neg h1, if_neg h2, if_neg h3]
          rw [hfun]; exact analyticAt_const
  have hPsi_an : AnalyticAt ℂ Psi τ := by
    show AnalyticAt ℂ (fun z => evalFormalPolyComplex (cext z) (coeffOfVar vbad 2 slopePoly)) τ
    exact evalFormalPolyComplex_analyticAt_of_all _ hcext_an
  have hBet_an : AnalyticAt ℂ Bet τ := by
    show AnalyticAt ℂ (fun z => evalFormalPolyComplex (cext z) (coeffOfVar vbad 1 slopePoly)) τ
    exact evalFormalPolyComplex_analyticAt_of_all _ hcext_an
  have hGam_an : AnalyticAt ℂ Gam τ := by
    show AnalyticAt ℂ (fun z => evalFormalPolyComplex (cext z) (coeffOfVar vbad 0 slopePoly)) τ
    exact evalFormalPolyComplex_analyticAt_of_all _ hcext_an
  -- concrete value of `Ψ_a` at `τ`
  have hΨτ_eq : Psi τ = evalFormalPolyComplex (step1GateAssignment hr H p τ)
      (coeffOfVar vbad 2 slopePoly) := by
    show evalFormalPolyComplex (cext τ) (coeffOfVar vbad 2 slopePoly)
      = evalFormalPolyComplex (step1GateAssignment hr H p τ) (coeffOfVar vbad 2 slopePoly)
    refine evalFormalPolyComplex_congr_on_vars (coeffOfVar vbad 2 slopePoly) ?_
    intro v hv
    have hvlt : v.1.1 < j := mem_vars_layer_lt_of_polynomialInLayersLT hPpsi_lt hv
    rw [hgate_pt τ v]
    simp only [hcextdef, if_pos hvlt]
  refine ⟨Psi, Bet, Gam, hPsi_an, hBet_an, hGam_an, hΨτ_eq, ?_⟩
  -- the model agrees with the level on a punctured neighborhood
  filter_upwards [hΩsucc] with z hz
  have hf_eq : D.level (⟨j + 1, hj_succ⟩, a) z
      = z * evalFormalPolyComplex (step1GateAssignment hr H p z) slopePoly
        + (logScale r : ℂ) :=
    hD.level_formula (⟨j + 1, hj_succ⟩ : Fin (m + 1)) a aactive hz
  have hDdeg : MvPolynomial.degreeOf vbad slopePoly ≤ 2 :=
    blockDegreeLE_degreeOf_le hbd2
  have hsplit : evalFormalPolyComplex (step1GateAssignment hr H p z) slopePoly
      = evalFormalPolyComplex (step1GateAssignment hr H p z) (coeffOfVar vbad 0 slopePoly)
        + evalFormalPolyComplex (step1GateAssignment hr H p z) (coeffOfVar vbad 1 slopePoly)
            * step1GateAssignment hr H p z vbad
        + evalFormalPolyComplex (step1GateAssignment hr H p z) (coeffOfVar vbad 2 slopePoly)
            * (step1GateAssignment hr H p z vbad) ^ 2 := by
    rw [evalFormalPolyComplex_eq_sum_coeffOfVar hDdeg (step1GateAssignment hr H p z)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    ring
  have hg_s : step1GateAssignment hr H p z vbad = s z := by
    have h1 : step1GateAssignment hr H p z vbad = D.gate vbad z := hgate_pt z vbad
    have h2 : D.gate vbad z = csig (D.level vbad z) := by
      rw [hvbaddef]; exact hD.gate_formula (⟨j, hj'⟩ : Fin (m + 1)) sel selactive hz
    rw [h1, h2, hsdef]
  have hagree : ∀ v : FormalVar (m + 1) k, v.1.1 ≤ j → v ≠ vbad →
      step1GateAssignment hr H p z v = cext z v := by
    intro v hvle hvne
    rw [hgate_pt z v]
    by_cases h1 : v.1.1 < j
    · simp only [hcextdef, if_pos h1]
    · have h3 : v.1.1 = j := le_antisymm hvle (not_lt.mp h1)
      have hvactive : v.2 ∈ activeHeads θ' v.1 :=
        (mem_activeHeads θ' v.1 v.2).2 (hactiveAll v.1 v.2)
      have hzΩ : z ∈ D.Omega (v.1.1 + 1) := by rw [h3]; exact hz
      have hgf := hD.gate_formula v.1 v.2 hvactive hzΩ
      simp only [hcextdef, if_neg h1, if_neg hvne, if_pos h3]
      exact hgf
  have hpsi_eq : evalFormalPolyComplex (step1GateAssignment hr H p z)
      (coeffOfVar vbad 2 slopePoly) = Psi z := by
    show evalFormalPolyComplex (step1GateAssignment hr H p z) (coeffOfVar vbad 2 slopePoly)
      = evalFormalPolyComplex (cext z) (coeffOfVar vbad 2 slopePoly)
    refine evalFormalPolyComplex_congr_on_vars (coeffOfVar vbad 2 slopePoly) ?_
    intro v hv
    exact hagree v
      (mem_vars_layer_le_of_polynomialInLayersLE (coeffOfVar_support_subset hslopeLE) hv)
      (fun hveq => coeffOfVar_notMem_vars (hveq ▸ hv))
  have hbet_eq : evalFormalPolyComplex (step1GateAssignment hr H p z)
      (coeffOfVar vbad 1 slopePoly) = Bet z := by
    show evalFormalPolyComplex (step1GateAssignment hr H p z) (coeffOfVar vbad 1 slopePoly)
      = evalFormalPolyComplex (cext z) (coeffOfVar vbad 1 slopePoly)
    refine evalFormalPolyComplex_congr_on_vars (coeffOfVar vbad 1 slopePoly) ?_
    intro v hv
    exact hagree v
      (mem_vars_layer_le_of_polynomialInLayersLE (coeffOfVar_support_subset hslopeLE) hv)
      (fun hveq => coeffOfVar_notMem_vars (hveq ▸ hv))
  have hgam_eq : evalFormalPolyComplex (step1GateAssignment hr H p z)
      (coeffOfVar vbad 0 slopePoly) = Gam z := by
    show evalFormalPolyComplex (step1GateAssignment hr H p z) (coeffOfVar vbad 0 slopePoly)
      = evalFormalPolyComplex (cext z) (coeffOfVar vbad 0 slopePoly)
    refine evalFormalPolyComplex_congr_on_vars (coeffOfVar vbad 0 slopePoly) ?_
    intro v hv
    exact hagree v
      (mem_vars_layer_le_of_polynomialInLayersLE (coeffOfVar_support_subset hslopeLE) hv)
      (fun hveq => coeffOfVar_notMem_vars (hveq ▸ hv))
  rw [hf_eq, hsplit, hg_s, hpsi_eq, hbet_eq, hgam_eq]
  ring

/-- **K06B.C7 order helper.**  At a tier point, the layer-`j+1` level of any head
`a` is meromorphic at `τ` with Laurent pole order at most `2κ` (the selected
gate's Laurent order squared), and — when the `ζ_j²` coefficient `Ψ_a(τ)` does not
vanish — of pole order exactly `2κ`. -/
theorem step1LayerLevel_meromorphicOrder_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} (p : Step1SeparatedProbe H) (h : Fin k)
    {j : Nat} (hj' : j < m + 1) (hj_succ : j + 1 < m + 1) {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j) (a : Fin k)
    (κ : ℕ) (cκ : ℂ) (hκ : 1 ≤ κ)
    (hNFs : LaurentNormalFormAt
      (fun z => csig ((step1ActiveStratificationData hr H p).level
        ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) z)) τ (κ : ℤ) cκ⁻¹) :
    MeromorphicAt ((step1ActiveStratificationData hr H p).level (⟨j + 1, hj_succ⟩, a)) τ ∧
    (((-(2 * κ : ℤ)) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt ((step1ActiveStratificationData hr H p).level (⟨j + 1, hj_succ⟩, a)) τ ∧
    (evalFormalPolyComplex (step1GateAssignment hr H p τ)
        (coeffOfVar ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) 2
          (formalSlope θ' p.1.1 p.1.2 (⟨j + 1, hj_succ⟩ : Fin (m + 1)) a)) ≠ 0 →
      meromorphicOrderAt ((step1ActiveStratificationData hr H p).level (⟨j + 1, hj_succ⟩, a)) τ
        = (((-(2 * κ : ℤ)) : ℤ) : WithTop ℤ)) := by
  classical
  obtain ⟨Psi, Bet, Gam, hPsi_an, hBet_an, hGam_an, hΨτ_eq, hmf⟩ :=
    step1LayerLevelSlopeModel_of_tier (hr := hr) p h hj' hj_succ hτ a
  set s : ℂ -> ℂ := fun z => csig ((step1ActiveStratificationData hr H p).level
      ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) z) with hsdef
  have hstratum : τ ∈ step1ActiveStratum hr H p h j := by
    have hmem := (step1TierCascadeData hr H).tier_in_stratum hτ
    simpa [step1TierCascadeData] using hmem
  have hτ_ne0 : τ ≠ 0 := fun h0 =>
    step1ActiveStratum_avoids_nonnegativeRealAxis (hr := hr) hstratum
      (by rw [h0]; exact zero_mem_nonnegativeRealAxis)
  have hs_mero : MeromorphicAt s τ := hNFs.meromorphicAt
  have hs_ord : meromorphicOrderAt s τ = ((-(κ : ℤ) : ℤ) : WithTop ℤ) := hNFs.order_eq
  -- the two summands of the model
  set leadFn : ℂ -> ℂ := fun z => z * Psi z * (s z) ^ 2 with hleadDef
  set restFn : ℂ -> ℂ := fun z => z * Bet z * s z + (z * Gam z + (logScale r : ℂ)) with hrestDef
  have hMeq : (fun z => z * (Psi z * (s z) ^ 2 + Bet z * s z + Gam z) + (logScale r : ℂ))
      = leadFn + restFn := by
    funext z; simp only [hleadDef, hrestDef, Pi.add_apply]; ring
  have hs2_mero : MeromorphicAt (fun z => (s z) ^ 2) τ := hs_mero.pow 2
  have hzPsi_an : AnalyticAt ℂ (fun z => z * Psi z) τ := analyticAt_id.mul hPsi_an
  have hleadEq : leadFn = (fun z => z * Psi z) * (fun z => (s z) ^ 2) := by
    funext z; simp only [hleadDef, Pi.mul_apply, mul_assoc]
  have htermAEq : (fun z => z * Bet z * s z) = (fun z => z * Bet z) * s := by
    funext z; simp only [Pi.mul_apply]
  have hlead_mero : MeromorphicAt leadFn τ := hzPsi_an.meromorphicAt.mul hs2_mero
  have hzBet_an : AnalyticAt ℂ (fun z => z * Bet z) τ := analyticAt_id.mul hBet_an
  have hrestB_an : AnalyticAt ℂ (fun z => z * Gam z + (logScale r : ℂ)) τ :=
    (analyticAt_id.mul hGam_an).add analyticAt_const
  have htermA_mero : MeromorphicAt (fun z => z * Bet z * s z) τ := hzBet_an.meromorphicAt.mul hs_mero
  have hrest_mero : MeromorphicAt restFn τ := htermA_mero.add hrestB_an.meromorphicAt
  have hM_mero : MeromorphicAt (leadFn + restFn) τ := hlead_mero.add hrest_mero
  have hmf2 : (step1ActiveStratificationData hr H p).level (⟨j + 1, hj_succ⟩, a)
      =ᶠ[nhdsWithin τ ({τ}ᶜ : Set ℂ)] (leadFn + restFn) := by rw [← hMeq]; exact hmf
  have hlevel_mero : MeromorphicAt
      ((step1ActiveStratificationData hr H p).level (⟨j + 1, hj_succ⟩, a)) τ :=
    hM_mero.congr hmf2.symm
  -- order of `s²`
  have hs2_ord : meromorphicOrderAt (fun z => (s z) ^ 2) τ = ((-(2 * κ : ℤ) : ℤ) : WithTop ℤ) := by
    have heq : (fun z => (s z) ^ 2) = s * s := by funext z; simp only [Pi.mul_apply, pow_two]
    have hcast : (-(κ : ℤ)) + (-(κ : ℤ)) = -(2 * κ : ℤ) := by ring
    rw [heq, meromorphicOrderAt_mul hs_mero hs_mero, hs_ord, ← WithTop.coe_add, hcast]
  -- lower bounds
  have hlead_lb : ((-(2 * κ : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt leadFn τ := by
    rw [hleadEq, meromorphicOrderAt_mul hzPsi_an.meromorphicAt hs2_mero, hs2_ord]
    exact le_add_of_nonneg_left hzPsi_an.meromorphicOrderAt_nonneg
  have htermA_lb : ((-(κ : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun z => z * Bet z * s z) τ := by
    rw [htermAEq, meromorphicOrderAt_mul hzBet_an.meromorphicAt hs_mero, hs_ord]
    exact le_add_of_nonneg_left hzBet_an.meromorphicOrderAt_nonneg
  have ho2κ_le_oκ : ((-(2 * κ : ℤ) : ℤ) : WithTop ℤ) ≤ ((-(κ : ℤ) : ℤ) : WithTop ℤ) :=
    WithTop.coe_le_coe.mpr (by omega)
  have hrest_lb : ((-(κ : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt restFn τ := by
    refine le_trans ?_ (meromorphicOrderAt_add htermA_mero hrestB_an.meromorphicAt)
    apply le_min
    · exact htermA_lb
    · refine le_trans ?_ hrestB_an.meromorphicOrderAt_nonneg
      rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from WithTop.coe_zero.symm,
        WithTop.coe_le_coe]; omega
  -- assemble lower bound on `M`, transfer to the level
  have hM_lb : ((-(2 * κ : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (leadFn + restFn) τ :=
    le_trans (le_min hlead_lb (le_trans ho2κ_le_oκ hrest_lb))
      (meromorphicOrderAt_add hlead_mero hrest_mero)
  have hcongr : meromorphicOrderAt
      ((step1ActiveStratificationData hr H p).level (⟨j + 1, hj_succ⟩, a)) τ
      = meromorphicOrderAt (leadFn + restFn) τ :=
    meromorphicOrderAt_congr hmf2
  refine ⟨hlevel_mero, by rw [hcongr]; exact hM_lb, ?_⟩
  -- exactness when `Ψ_a(τ) ≠ 0`
  intro hΨ_ne
  have hPsiτ_ne : Psi τ ≠ 0 := by rw [hΨτ_eq]; exact hΨ_ne
  have hzPsiτ_ne : (fun z => z * Psi z) τ ≠ 0 := mul_ne_zero hτ_ne0 hPsiτ_ne
  have hlead_exact : meromorphicOrderAt leadFn τ = ((-(2 * κ : ℤ) : ℤ) : WithTop ℤ) := by
    rw [hleadEq, meromorphicOrderAt_mul_of_ne_zero (f := fun z => (s z) ^ 2) hzPsi_an hzPsiτ_ne,
      hs2_ord]
  have hrest_gt : meromorphicOrderAt leadFn τ < meromorphicOrderAt restFn τ := by
    rw [hlead_exact]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hrest_lb
  have hM_exact : meromorphicOrderAt (leadFn + restFn) τ = ((-(2 * κ : ℤ) : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_add_of_ne hlead_mero hrest_mero (ne_of_lt hrest_gt),
      min_eq_left (le_of_lt hrest_gt)]
    exact hlead_exact
  rw [hcongr]; exact hM_exact

/-- **K06B.C7.a — sibling exact-order bound.**  At a tier point, every nonselected
layer-`j+1` sibling level (`step1SiblingLevelFamily … q.succ`) has a Laurent normal
form of pole order `μ ≤ 2κ` (the selected pole order).  The selected gate's Laurent
order `κ` is supplied via `hNFs`. -/
theorem step1SiblingLevel_normalForm_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} (p : Step1SeparatedProbe H) (h : Fin k)
    {j : Nat} (hj' : j < m + 1) (hj_succ : j + 1 < m + 1) {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j)
    (κ : ℕ) (cκ : ℂ) (hκ : 1 ≤ κ)
    (hNFs : LaurentNormalFormAt (fun z => csig ((step1ActiveStratificationData hr H p).level
      ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) z)) τ (κ : ℤ) cκ⁻¹)
    (q : Fin (step1NonselectedSiblingCount (step1SelectedHead H.chains h (j + 1)))) :
    ∃ (μ : ℤ) (cc : ℂ), μ ≤ (2 * κ : ℤ) ∧
      LaurentNormalFormAt
        (step1SiblingLevelFamily hr H p h hj_succ
          (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h (j + 1))) q.succ)
        τ μ cc := by
  classical
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  have hD : ActiveHeadSingularStratification hr θ' p.1.1 p.1.2 (step1ActiveStratificationData hr H p) :=
    step1ActiveStratificationData_spec hr H p
  set c₀ : Fin k :=
    (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h (j + 1)) q).1 with hc0def
  have hc0active : c₀ ∈ activeHeads θ' (⟨j + 1, hj_succ⟩ : Fin (m + 1)) :=
    (mem_activeHeads θ' (⟨j + 1, hj_succ⟩) c₀).2 (hactiveAll (⟨j + 1, hj_succ⟩) c₀)
  obtain ⟨hmero, hlb, _⟩ :=
    step1LayerLevel_meromorphicOrder_of_tier (hr := hr) p h hj' hj_succ hτ c₀ κ cκ hκ hNFs
  have hstratum : τ ∈ step1ActiveStratum hr H p h j := by
    have hmem := (step1TierCascadeData hr H).tier_in_stratum hτ
    simpa [step1TierCascadeData] using hmem
  have hΩsucc : ∀ᶠ z in puncturedNhds τ,
      z ∈ (step1ActiveStratificationData hr H p).Omega (j + 1) :=
    step1ActiveStratum_punctured_omega_succ (hr := hr) hj' hstratum
  obtain ⟨ρ0, hρ0, hsubP⟩ := Metric.mem_nhdsWithin_iff.mp hΩsucc
  have hpunc_sub : puncturedDisc τ ρ0 ⊆ (step1ActiveStratificationData hr H p).Omega (j + 1) := by
    intro z hz
    exact hsubP ⟨Metric.mem_ball.mpr hz.2, by simpa [puncturedDisc] using hz.1⟩
  have hlevel_an : AnalyticOnNhd ℂ
      ((step1ActiveStratificationData hr H p).level (⟨j + 1, hj_succ⟩, c₀))
      ((step1ActiveStratificationData hr H p).Omega (j + 1)) :=
    hD.level_holomorphic (⟨j + 1, hj_succ⟩) c₀ hc0active
  have hpre : IsPreconnected ((step1ActiveStratificationData hr H p).Omega (j + 1)) :=
    (hD.domain (j + 1) (le_of_lt hj_succ)).isPreconnected
  have h0Ω : (0 : ℂ) ∈ (step1ActiveStratificationData hr H p).Omega (j + 1) :=
    hD.nonnegative_axis_subset (j + 1) (le_of_lt hj_succ) zero_mem_nonnegativeRealAxis
  have hf0 : (step1ActiveStratificationData hr H p).level (⟨j + 1, hj_succ⟩, c₀) 0 ≠ 0 := by
    rw [hD.level_zero (⟨j + 1, hj_succ⟩) c₀ hc0active]
    exact_mod_cast ne_of_gt (logScale_pos_of_one_lt hr)
  have hne : meromorphicOrderAt
      ((step1ActiveStratificationData hr H p).level (⟨j + 1, hj_succ⟩, c₀)) τ ≠ ⊤ :=
    meromorphicOrderAt_ne_top_of_domain hlevel_an hpre h0Ω hf0 hρ0 hpunc_sub
  obtain ⟨μ, cc, hμle, hNF⟩ :=
    laurentNormalFormAt_of_meromorphic_orderBound (N := (2 * κ : ℤ)) hmero hne hlb
  exact ⟨μ, cc, hμle, hNF⟩

/-- **K06B.C7.c — sibling avoidance hypotheses.**  At a tier point, the finite
successor sibling family satisfies the K04E `SiblingAvoidanceHypotheses` record on
the successor stratification domain `Ω_{j+1}`: the selected successor level has a
pole at `τ` (its `ζ_j²` coefficient does not vanish, by tier dominance), each family
member is holomorphic on and real on the nonnegative axis, and each sibling differs
from the selected level (C7.b). -/
theorem step1SiblingAvoidanceHypotheses_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} (p : Step1SeparatedProbe H) (h : Fin k)
    {j : Nat} (hj' : j < m + 1) (hj_succ : j + 1 < m + 1) {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j)
    (κ : ℕ) (cκ : ℂ) (hκ : 1 ≤ κ)
    (hNFs : LaurentNormalFormAt (fun z => csig ((step1ActiveStratificationData hr H p).level
      ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) z)) τ (κ : ℤ) cκ⁻¹)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0)
    (hpunc_sub : puncturedDisc τ ρ0 ⊆ (step1ActiveStratificationData hr H p).Omega (j + 1)) :
    SiblingAvoidanceHypotheses ((step1ActiveStratificationData hr H p).Omega (j + 1)) τ ρ0
      (step1SiblingLevelFamily hr H p h hj_succ
        (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h (j + 1)))) := by
  classical
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  have hD : ActiveHeadSingularStratification hr θ' p.1.1 p.1.2
      (step1ActiveStratificationData hr H p) := step1ActiveStratificationData_spec hr H p
  have hjm : j < m := by omega
  have hj_depth : j < (step1TierCascadeData hr H).depth := by
    rw [step1TierCascadeData_depth]; omega
  have hsucc_depth : j + 1 < (step1TierCascadeData hr H).depth := by
    rw [step1TierCascadeData_depth]; omega
  have hsel'active : step1SelectedHead H.chains h (j + 1)
      ∈ activeHeads θ' (⟨j + 1, hj_succ⟩ : Fin (m + 1)) :=
    (mem_activeHeads θ' (⟨j + 1, hj_succ⟩) (step1SelectedHead H.chains h (j + 1))).2
      (hactiveAll (⟨j + 1, hj_succ⟩) (step1SelectedHead H.chains h (j + 1)))
  have henumactive : ∀ q, (step1NonselectedSiblingEnumeration
      (step1SelectedHead H.chains h (j + 1)) q).1 ∈ activeHeads θ' (⟨j + 1, hj_succ⟩ : Fin (m + 1)) :=
    fun q => (mem_activeHeads θ' (⟨j + 1, hj_succ⟩) _).2 (hactiveAll (⟨j + 1, hj_succ⟩) _)
  -- selected successor level has a pole: its `ζ_j²` coefficient does not vanish
  obtain ⟨_, _, hexact0⟩ :=
    step1LayerLevel_meromorphicOrder_of_tier (hr := hr) p h hj' hj_succ hτ
      (step1SelectedHead H.chains h (j + 1)) κ cκ hκ hNFs
  have hΨ0_ne : evalFormalPolyComplex (step1GateAssignment hr H p τ)
      (coeffOfVar ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) 2
        (formalSlope θ' p.1.1 p.1.2 (⟨j + 1, hj_succ⟩ : Fin (m + 1))
          (step1SelectedHead H.chains h (j + 1)))) ≠ 0 := by
    have hign : coeffOfVar ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) 2
        (formalSlope θ' p.1.1 p.1.2 (⟨j + 1, hj_succ⟩ : Fin (m + 1))
          (step1SelectedHead H.chains h (j + 1)))
        = step1IgnitionPoly H.chains h p.1 j hjm := rfl
    rw [hign]
    exact step1SuccessorLeadingFactor_ne_zero_of_tier (hr := hr) (H := H) p h hjm hτ
  have hord0 : meromorphicOrderAt
      (step1SiblingLevelFamily hr H p h hj_succ
        (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h (j + 1))) 0) τ
      = ((-(2 * κ : ℤ) : ℤ) : WithTop ℤ) := hexact0 hΨ0_ne
  have hpole0 : ¬ AnalyticAt ℂ
      (step1SiblingLevelFamily hr H p h hj_succ
        (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h (j + 1))) 0) τ := by
    intro han
    have hnn := han.meromorphicOrderAt_nonneg
    rw [hord0] at hnn
    rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from WithTop.coe_zero.symm,
      WithTop.coe_le_coe] at hnn
    omega
  refine
    { omega_domain := hD.domain (j + 1) (le_of_lt hj_succ)
      nonneg_subset := hD.nonnegative_axis_subset (j + 1) (le_of_lt hj_succ)
      center_notMem := ?_
      puncturedDisc_subset := hpunc_sub
      radius_pos := hρ0
      analytic_on_omega := ?_
      meromorphic_at_center := ?_
      common_real_value := ?_
      real_valued_on_nonnegative := ?_
      selected_has_pole := hpole0
      sibling_not_identical := ?_ }
  · intro hτΩ
    exact hpole0 ((hD.level_holomorphic (⟨j + 1, hj_succ⟩)
      (step1SelectedHead H.chains h (j + 1)) hsel'active) τ hτΩ)
  · intro c
    refine Fin.cases ?_ ?_ c
    · exact hD.level_holomorphic (⟨j + 1, hj_succ⟩) (step1SelectedHead H.chains h (j + 1)) hsel'active
    · intro q
      exact hD.level_holomorphic (⟨j + 1, hj_succ⟩) _ (henumactive q)
  · intro c
    refine Fin.cases ?_ ?_ c
    · exact (step1LayerLevel_meromorphicOrder_of_tier (hr := hr) p h hj' hj_succ hτ
        (step1SelectedHead H.chains h (j + 1)) κ cκ hκ hNFs).1
    · intro q
      exact (step1LayerLevel_meromorphicOrder_of_tier (hr := hr) p h hj' hj_succ hτ
        _ κ cκ hκ hNFs).1
  · refine ⟨logScale r, by exact_mod_cast ne_of_gt (logScale_pos_of_one_lt hr), ?_⟩
    intro c
    refine Fin.cases ?_ ?_ c
    · exact hD.level_zero (⟨j + 1, hj_succ⟩) (step1SelectedHead H.chains h (j + 1)) hsel'active
    · intro q
      exact hD.level_zero (⟨j + 1, hj_succ⟩) _ (henumactive q)
  · intro c
    refine Fin.cases ?_ ?_ c
    · exact hD.level_real_on_nonnegative_axis (⟨j + 1, hj_succ⟩)
        (step1SelectedHead H.chains h (j + 1)) hsel'active
    · intro q
      exact hD.level_real_on_nonnegative_axis (⟨j + 1, hj_succ⟩) _ (henumactive q)
  · intro c
    exact step1SiblingLevel_not_identical_of_tier (hr := hr) (H := H) p h hj_depth hτ hsucc_depth c

/-- **K06B.C7.d — canonical sibling avoidance result.**  From tier membership at
`τ`, assemble the K04E `SiblingAvoidanceResult` on the successor stratification
domain via the sequence-window endpoint C6
(`siblingAvoidanceResult_of_normalForm`): the selected successor-level Laurent
normal form of exact order `2κ` (C4c-style, built here from the gate order `κ`),
the selected-arc data, and the sibling exact-order bounds (C7.a). -/
theorem step1CanonicalSiblingAvoidanceResult_of_tierMembership {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} (p : Step1SeparatedProbe H) (h : Fin k)
    {j : Nat} {τ : ℂ}
    (hj : j < (step1TierCascadeData hr H).depth)
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j)
    (hsucc : j + 1 < (step1TierCascadeData hr H).depth) :
    ∃ ρ0 : ℝ,
      SiblingAvoidanceResult
        ((step1ActiveStratificationData hr H p).Omega (j + 1)) τ ρ0
        (step1SiblingLevelFamily hr H p h
          (by simpa [step1TierCascadeData] using hsucc)
          (step1NonselectedSiblingEnumeration
            (step1SelectedHead H.chains h (j + 1)))) := by
  classical
  have hj_succ : j + 1 < m + 1 := by simpa [step1TierCascadeData] using hsucc
  have hj' : j < m + 1 := by omega
  have hjm : j < m := by omega
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  have hD : ActiveHeadSingularStratification hr θ' p.1.1 p.1.2
      (step1ActiveStratificationData hr H p) := step1ActiveStratificationData_spec hr H p
  have hsel'active : step1SelectedHead H.chains h (j + 1)
      ∈ activeHeads θ' (⟨j + 1, hj_succ⟩ : Fin (m + 1)) :=
    (mem_activeHeads θ' (⟨j + 1, hj_succ⟩) (step1SelectedHead H.chains h (j + 1))).2
      (hactiveAll (⟨j + 1, hj_succ⟩) (step1SelectedHead H.chains h (j + 1)))
  -- C4b: selected gate Laurent order `κ`
  obtain ⟨κ, cκ, hκ, hNFs, _⟩ := step1SelectedGate_normalForm_of_tier (hr := hr) p h hj' hτ
  have hm2 : 1 ≤ 2 * κ := by omega
  -- one punctured disc inside `Ω_{j+1}`
  have hstratum : τ ∈ step1ActiveStratum hr H p h j := by
    have hmem := (step1TierCascadeData hr H).tier_in_stratum hτ
    simpa [step1TierCascadeData] using hmem
  have hΩsucc : ∀ᶠ z in puncturedNhds τ,
      z ∈ (step1ActiveStratificationData hr H p).Omega (j + 1) :=
    step1ActiveStratum_punctured_omega_succ (hr := hr) hj' hstratum
  obtain ⟨ρ0, hρ0, hsubP⟩ := Metric.mem_nhdsWithin_iff.mp hΩsucc
  have hpunc_sub : puncturedDisc τ ρ0 ⊆ (step1ActiveStratificationData hr H p).Omega (j + 1) := by
    intro z hz
    exact hsubP ⟨Metric.mem_ball.mpr hz.2, by simpa [puncturedDisc] using hz.1⟩
  -- exact pole order `2κ` for the selected successor level (= family index `0`)
  obtain ⟨hmero0, _, hexact0⟩ :=
    step1LayerLevel_meromorphicOrder_of_tier (hr := hr) p h hj' hj_succ hτ
      (step1SelectedHead H.chains h (j + 1)) κ cκ hκ hNFs
  have hΨ0_ne : evalFormalPolyComplex (step1GateAssignment hr H p τ)
      (coeffOfVar ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) 2
        (formalSlope θ' p.1.1 p.1.2 (⟨j + 1, hj_succ⟩ : Fin (m + 1))
          (step1SelectedHead H.chains h (j + 1)))) ≠ 0 := by
    have hign : coeffOfVar ((⟨j, hj'⟩ : Fin (m + 1)), step1SelectedHead H.chains h j) 2
        (formalSlope θ' p.1.1 p.1.2 (⟨j + 1, hj_succ⟩ : Fin (m + 1))
          (step1SelectedHead H.chains h (j + 1)))
        = step1IgnitionPoly H.chains h p.1 j hjm := rfl
    rw [hign]
    exact step1SuccessorLeadingFactor_ne_zero_of_tier (hr := hr) (H := H) p h hjm hτ
  have hord0 : meromorphicOrderAt
      (step1SiblingLevelFamily hr H p h hj_succ
        (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h (j + 1))) 0) τ
      = ((-(2 * κ : ℤ) : ℤ) : WithTop ℤ) := hexact0 hΨ0_ne
  obtain ⟨c0, hNF0raw⟩ := laurentNormalFormAt_of_meromorphicOrder_int hmero0 hord0
  have hNF0 : LaurentNormalFormAt
      (step1SiblingLevelFamily hr H p h hj_succ
        (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h (j + 1))) 0)
      τ ((2 * κ : ℕ) : ℤ) c0 :=
    laurentNF_order_cast hNF0raw (by push_cast; ring)
  -- holomorphy of the selected successor level on the punctured disc
  have hHol : AnalyticOnNhd ℂ
      (step1SiblingLevelFamily hr H p h hj_succ
        (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h (j + 1))) 0)
      (puncturedDisc τ ρ0) :=
    (hD.level_holomorphic (⟨j + 1, hj_succ⟩) (step1SelectedHead H.chains h (j + 1))
      hsel'active).mono hpunc_sub
  have hA : SelectedArcData
      (step1SiblingLevelFamily hr H p h hj_succ
        (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h (j + 1))) 0)
      τ (2 * κ) c0 :=
    Classical.choice (selectedArcData_of_normalForm (m := 2 * κ) hm2 hρ0 hHol hNF0)
  -- C7.c hypotheses and C7.a sibling bounds
  have hhyp := step1SiblingAvoidanceHypotheses_of_tier (hr := hr) p h hj' hj_succ hτ κ cκ hκ hNFs
    ρ0 hρ0 hpunc_sub
  have hsib : ∀ c : Fin (step1NonselectedSiblingCount (step1SelectedHead H.chains h (j + 1))),
      ∃ (μ : ℤ) (cc : ℂ), μ ≤ ((2 * κ : ℕ) : ℤ) ∧
        LaurentNormalFormAt
          (step1SiblingLevelFamily hr H p h hj_succ
            (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h (j + 1))) c.succ)
          τ μ cc := by
    intro c
    obtain ⟨μ, cc, hle, hnf⟩ :=
      step1SiblingLevel_normalForm_of_tier (hr := hr) p h hj' hj_succ hτ κ cκ hκ hNFs c
    refine ⟨μ, cc, ?_, hnf⟩
    rw [show ((2 * κ : ℕ) : ℤ) = (2 * κ : ℤ) from by push_cast; ring]
    exact hle
  exact ⟨ρ0, _root_.TransformerIdentifiability.NLayer.KHead.siblingAvoidanceResult_of_normalForm
    hhyp hm2 hNF0 hA hsib⟩

end TransformerIdentifiability.NLayer.KHead.Step1
