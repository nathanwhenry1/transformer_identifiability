import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.TierCascade
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.TierLocal

set_option autoImplicit false

open Filter Matrix

namespace TransformerIdentifiability.NLayer.KHead.Step1

/-!
# K-head Step 1 final visible-coordinate blowup (`lem:observable-pole`, `lem:final-tier-blowup`)

This file carries milestone M8 of the K06B closure: at a final-tier point
`τ ∈ (step1TierCascadeData hr H).T p h finalTierIndex`, the selected final-layer gate has a
Laurent pole (deliverable 1), the observable coordinate `e_ι^⊤ F̂_{θ'}` splits as
`B + selectedGate · G` with `B` punctured-bounded, `G` tending to the nonzero residue value
`g_ι` (deliverable 2), and consequently the visible coordinate blows up (deliverable 4,
`step1FinalTierVisibleBlowupPayloads`).
-/

/-! ## Generic analytic utilities -/

/-- Complex evaluation of a formal polynomial is continuous under a pointwise limit of the
gate assignment: if every formal variable's assignment tends to a limit along `F`, then the
polynomial evaluation tends to the evaluation at the limit assignment. -/
theorem evalFormalPolyComplex_tendsto {L k : Nat} {α : Type*} {F : Filter α}
    {η : α → FormalVar L k → ℂ} {c : FormalVar L k → ℂ} (p : FormalPoly L k)
    (hη : ∀ x : FormalVar L k, Tendsto (fun z => η z x) F (nhds (c x))) :
    Tendsto (fun z => evalFormalPolyComplex (η z) p) F
      (nhds (evalFormalPolyComplex c p)) := by
  simp only [evalFormalPolyComplex]
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval₂_C]
      exact tendsto_const_nhds
  | add p q hp hq =>
      simp only [MvPolynomial.eval₂_add]
      exact hp.add hq
  | mul_X p x hp =>
      simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      exact hp.mul (hη x)

/-- A function tending to a finite limit along the punctured neighbourhood filter is
punctured-bounded there. -/
theorem puncturedBoundedAt_of_tendsto {G : ℂ → ℂ} {τ L : ℂ}
    (hG : Tendsto G (puncturedNhds τ) (nhds L)) :
    PuncturedBoundedAt G τ := by
  refine ⟨‖L‖ + 1, ?_⟩
  exact ((hG.norm).eventually
    (Iio_mem_nhds (show ‖L‖ < ‖L‖ + 1 by linarith))).mono (fun z hz => le_of_lt hz)

/-- Expand a matrix-vector product of a finite `ℂ`-linear combination of matrices, at one
coordinate, as the same linear combination of the coordinatewise products. -/
theorem mulVec_sum_smul_apply {n K : Nat} (c : Fin K → ℂ)
    (M : Fin K → Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) (i : Fin n) :
    ((∑ a : Fin K, c a • M a) *ᵥ w) i = ∑ a : Fin K, c a * ((M a *ᵥ w) i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-! ## Deliverable 1 — the selected final-layer gate has a Laurent pole -/

/-- **`lem:observable-pole` input.**  At a final-tier point the selected final-layer gate
`csig ∘ level` has a pole of exact order `κ ≥ 1` with leading Laurent coefficient `cκ⁻¹`;
this is `step1SelectedGate_normalForm_of_tier` (C4b) at `j = m`, transported to the `gate`
field along `gate_formula` on `Ω_{m+1}`. -/
theorem step1FinalSelectedGate_normalForm_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H} {h : Fin k} {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h
      (step1TierCascadeData hr H).finalTierIndex) :
    ∃ (κ : ℕ) (cκ : ℂ), 1 ≤ κ ∧
      LaurentNormalFormAt
        ((step1ActiveStratificationData hr H p).gate
          (⟨m, Nat.lt_succ_self m⟩, step1SelectedHead H.chains h m)) τ (κ : ℤ) cκ⁻¹ := by
  have hm : m < m + 1 := Nat.lt_succ_self m
  have hτm : τ ∈ (step1TierCascadeData hr H).T p h m := by
    simpa [step1TierCascadeData_finalTierIndex] using hτ
  obtain ⟨κ, cκ, hκ, hNFcsig, _hNFlevel⟩ :=
    step1SelectedGate_normalForm_of_tier (hr := hr) (H := H) p h hm hτm
  refine ⟨κ, cκ, hκ, ?_⟩
  have hD := step1ActiveStratificationData_spec hr H p
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  have selactive : step1SelectedHead H.chains h m ∈ activeHeads θ' ⟨m, hm⟩ :=
    (mem_activeHeads θ' ⟨m, hm⟩ (step1SelectedHead H.chains h m)).2
      (hactiveAll ⟨m, hm⟩ (step1SelectedHead H.chains h m))
  have hstratum : τ ∈ step1ActiveStratum hr H p h m := by
    have hmem := (step1TierCascadeData hr H).tier_in_stratum hτm
    simpa [step1TierCascadeData] using hmem
  have hΩsucc : ∀ᶠ z in puncturedNhds τ,
      z ∈ (step1ActiveStratificationData hr H p).Omega (m + 1) :=
    step1ActiveStratum_punctured_omega_succ (hr := hr) hm hstratum
  have hgate_formula :
      (step1ActiveStratificationData hr H p).gate
          (⟨m, hm⟩, step1SelectedHead H.chains h m)
        =ᶠ[nhdsWithin τ ({τ}ᶜ : Set ℂ)]
        (fun z => csig ((step1ActiveStratificationData hr H p).level
          (⟨m, hm⟩, step1SelectedHead H.chains h m) z)) := by
    filter_upwards [hΩsucc] with z hz
    exact hD.gate_formula ⟨m, hm⟩ (step1SelectedHead H.chains h m) selactive hz
  exact hNFcsig.congr hgate_formula.symm

/-! ## Tower-dominance at the final tier -/

/-- Every final-tier point satisfies the finite-family tower dominance predicate at the
final tier index `m` (T3 of `T_m`, vacuous when `m = 0`). -/
theorem step1FinalTowerDominance {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H} {h : Fin k} {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h m) :
    step1TowerDominance hr H p h m τ := by
  cases m with
  | zero =>
      unfold step1TowerDominance
      rw [dif_pos (by norm_num)]
      intro ix i hi
      exact absurd hi (Nat.not_lt_zero _)
  | succ m' =>
      have hparts :
          τ ∈ (step1TierCascadeData hr H).omega p h (m' + 1) ∧
            (step1TierCascadeData hr H).selectedOnlyCollision p h (m' + 1) τ ∧
              τ ∉ nonnegativeRealAxis ∧
                (step1TierCascadeData hr H).dominance p h (m' + 1) τ := by
        simpa using ((step1TierCascadeData hr H).mem_T_succ p h m' (τ := τ)).mp hτ
      simpa [step1TierCascadeData] using hparts.2.2.2

/-! ## Continuity of lower-layer polynomial evaluations at a final-tier point -/

/-- If `P` uses only variables from layers `< m`, then evaluating `P` at the complex gate
assignment is continuous at a final-tier point `τ`: every gate it reads is analytic at `τ`
(C4b, lower layers), so the evaluation tends to its value at `τ` along `puncturedNhds τ`. -/
theorem step1EvalLayersLT_tendsto {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H} {h : Fin k} {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h m)
    {P : FormalPoly (m + 1) k} (hP : PolynomialInLayersLT m P) :
    Tendsto (fun z => evalFormalPolyComplex (step1GateAssignment hr H p z) P)
      (puncturedNhds τ)
      (nhds (evalFormalPolyComplex (step1GateAssignment hr H p τ) P)) := by
  classical
  have hm : m < m + 1 := Nat.lt_succ_self m
  set η : ℂ → FormalVar (m + 1) k → ℂ :=
    fun z x => if m ≤ x.1.1 then 0 else step1GateAssignment hr H p z x with hη
  set c : FormalVar (m + 1) k → ℂ :=
    fun x => if m ≤ x.1.1 then 0 else step1GateAssignment hr H p τ x with hc
  -- every variable's assignment tends to a limit
  have hvar : ∀ x : FormalVar (m + 1) k,
      Tendsto (fun z => η z x) (puncturedNhds τ) (nhds (c x)) := by
    intro x
    by_cases hx : m ≤ x.1.1
    · simp only [hη, hc, if_pos hx]
      exact tendsto_const_nhds
    · simp only [hη, hc, if_neg hx]
      have hlt : x.1.1 < m := Nat.lt_of_not_le hx
      have hgatex : ∀ w : ℂ, step1GateAssignment hr H p w x =
          (step1ActiveStratificationData hr H p).gate
            (⟨x.1.1, lt_trans hlt hm⟩, x.2) w := by
        intro w
        have hg := step1GateAssignment_eq_gate (hr := hr) H p w x.1 x.2
        simpa using hg
      have hana :
          AnalyticAt ℂ ((step1ActiveStratificationData hr H p).gate
            (⟨x.1.1, lt_trans hlt hm⟩, x.2)) τ :=
        step1LowerGate_analyticAt_of_tier (hr := hr) (H := H) p h hm hτ hlt x.2
      have htend :
          Tendsto ((step1ActiveStratificationData hr H p).gate
              (⟨x.1.1, lt_trans hlt hm⟩, x.2)) (puncturedNhds τ)
            (nhds ((step1ActiveStratificationData hr H p).gate
              (⟨x.1.1, lt_trans hlt hm⟩, x.2) τ)) :=
        hana.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      rw [show (fun z => step1GateAssignment hr H p z x) =
            (step1ActiveStratificationData hr H p).gate
              (⟨x.1.1, lt_trans hlt hm⟩, x.2) from funext hgatex, hgatex τ]
      exact htend
  -- the modified assignment agrees with the real one on the support of `P`
  have hcongr_z : ∀ z : ℂ,
      evalFormalPolyComplex (η z) P =
        evalFormalPolyComplex (step1GateAssignment hr H p z) P := by
    intro z
    refine MvPolynomial.eval₂_congr (algebraMap ℝ ℂ) (η z)
      (step1GateAssignment hr H p z) ?_
    intro i mm hi hcoeff
    have hmem : mm ∈ P.support := MvPolynomial.mem_support_iff.mpr hcoeff
    have hi_lt : i.1.1 < m := by
      by_contra hge
      exact (Finsupp.mem_support_iff.mp hi) (hP mm hmem i (not_lt.mp hge))
    simp only [hη, if_neg (not_le.mpr hi_lt)]
  have hcongr_c : evalFormalPolyComplex c P =
      evalFormalPolyComplex (step1GateAssignment hr H p τ) P := by
    refine MvPolynomial.eval₂_congr (algebraMap ℝ ℂ) c (step1GateAssignment hr H p τ) ?_
    intro i mm hi hcoeff
    have hmem : mm ∈ P.support := MvPolynomial.mem_support_iff.mpr hcoeff
    have hi_lt : i.1.1 < m := by
      by_contra hge
      exact (Finsupp.mem_support_iff.mp hi) (hP mm hmem i (not_lt.mp hge))
    simp only [hc, if_neg (not_le.mpr hi_lt)]
  have htend := evalFormalPolyComplex_tendsto (F := puncturedNhds τ) (η := η) (c := c) P hvar
  rw [hcongr_c] at htend
  rw [show (fun z => evalFormalPolyComplex (η z) P) =
        (fun z => evalFormalPolyComplex (step1GateAssignment hr H p z) P) from
      funext hcongr_z] at htend
  exact htend

/-! ## Deliverable 2 — local residue decomposition of the observable coordinate -/

/-- **`lem:observable-pole` decomposition.**  At a final-tier point `τ`, eventually on
`puncturedNhds τ` the observable coordinate `e_ι^⊤ F̂_{θ'}` splits as `B + selectedGate · G`,
where `B` is punctured-bounded (collapse term plus nonselected last-layer gate terms), `G`
tends to `g0 = e_ι^⊤ V'_{m,a_m} w'_{m-1}(s'(τ))` (the residue polynomial evaluation), and
`g0 ≠ 0` for a visible coordinate by tower dominance (T3 of the final tier). -/
theorem step1FinalObservableCoord_localResidue {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H} {h : Fin k} {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h
      (step1TierCascadeData hr H).finalTierIndex)
    (ι : Fin d) :
    ∃ (B G : ℂ -> ℂ) (g0 : ℂ),
      PuncturedBoundedAt B τ ∧
      Tendsto G (puncturedNhds τ) (nhds g0) ∧
      (step1VisibleCoordinate H p h ι -> g0 ≠ 0) ∧
      (fun z => (step1ActiveStratificationData hr H p).observable z ι)
        =ᶠ[puncturedNhds τ]
          (fun z => B z +
            (step1ActiveStratificationData hr H p).gate
              (⟨m, Nat.lt_succ_self m⟩, step1SelectedHead H.chains h m) z * G z) := by
  classical
  have hm : m < m + 1 := Nat.lt_succ_self m
  have hτm : τ ∈ (step1TierCascadeData hr H).T p h m := by
    simpa [step1TierCascadeData_finalTierIndex] using hτ
  have hD := step1ActiveStratificationData_spec hr H p
  set sel := step1SelectedHead H.chains h m with hsel
  set Wm := formalW θ' p.1.1 p.1.2 m (Nat.le_succ m) with hWm
  set Vm := formalV θ' p.1.1 p.1.2 m (Nat.le_succ m) with hVm
  have hWlb : ∀ j : Fin d, LayerBoundedBlockAffine m (Wm j) :=
    fun j => (formalPoint_layerBoundedBlockAffine θ' p.1.1 p.1.2 m (Nat.le_succ m)).1 j
  have hVlb : ∀ j : Fin d, LayerBoundedBlockAffine m (Vm j) :=
    fun j => (formalPoint_layerBoundedBlockAffine θ' p.1.1 p.1.2 m (Nat.le_succ m)).2 j
  have hRsel :
      (formalValueMatrix θ' ⟨m, hm⟩ sel *ᵥ Wm) ι = step1ResiduePoly H.chains h p.1 ι := rfl
  refine ⟨fun z => evalFormalPolyComplex (step1GateAssignment hr H p z)
              ((formalCollapseMatrix θ' ⟨m, hm⟩ *ᵥ Vm) ι)
            + ∑ a ∈ Finset.univ.erase sel,
                step1GateAssignment hr H p z (⟨m, hm⟩, a)
                  * evalFormalPolyComplex (step1GateAssignment hr H p z)
                      ((formalValueMatrix θ' ⟨m, hm⟩ a *ᵥ Wm) ι),
          fun z => evalFormalPolyComplex (step1GateAssignment hr H p z)
              (step1ResiduePoly H.chains h p.1 ι),
          evalFormalPolyComplex (step1GateAssignment hr H p τ)
              (step1ResiduePoly H.chains h p.1 ι),
          ?_, ?_, ?_, ?_⟩
  · -- PuncturedBoundedAt B
    have hcollapse := step1EvalLayersLT_tendsto (hr := hr) hτm
      (P := (formalCollapseMatrix θ' ⟨m, hm⟩ *ᵥ Vm) ι)
      ((layerBounded_realMatrixToFormal_mulVec (collapseMatrix θ' ⟨m, hm⟩) hVlb ι).support_lt)
    have hsum :
        Tendsto (fun z => ∑ a ∈ Finset.univ.erase sel,
            step1GateAssignment hr H p z (⟨m, hm⟩, a)
              * evalFormalPolyComplex (step1GateAssignment hr H p z)
                  ((formalValueMatrix θ' ⟨m, hm⟩ a *ᵥ Wm) ι))
          (puncturedNhds τ)
          (nhds (∑ a ∈ Finset.univ.erase sel,
            csig ((step1ActiveStratificationData hr H p).level (⟨m, hm⟩, a) τ)
              * evalFormalPolyComplex (step1GateAssignment hr H p τ)
                  ((formalValueMatrix θ' ⟨m, hm⟩ a *ᵥ Wm) ι))) := by
      apply tendsto_finsetSum
      intro a ha
      have ha' : a ≠ sel := Finset.ne_of_mem_erase ha
      have hgate :
          Tendsto (fun z => step1GateAssignment hr H p z (⟨m, hm⟩, a)) (puncturedNhds τ)
            (nhds (csig ((step1ActiveStratificationData hr H p).level (⟨m, hm⟩, a) τ))) := by
        have hc4 := step1NonselectedGate_tendsto_of_tier (hr := hr) (H := H) p h hm hτm a ha'
        have hEq :
            (step1ActiveStratificationData hr H p).gate (⟨m, hm⟩, a)
              =ᶠ[puncturedNhds τ] (fun z => step1GateAssignment hr H p z (⟨m, hm⟩, a)) := by
          filter_upwards with z
          exact (step1GateAssignment_eq_gate (hr := hr) H p z ⟨m, hm⟩ a).symm
        exact Filter.Tendsto.congr' hEq hc4
      have hres := step1EvalLayersLT_tendsto (hr := hr) hτm
        (P := (formalValueMatrix θ' ⟨m, hm⟩ a *ᵥ Wm) ι)
        ((layerBounded_realMatrixToFormal_mulVec (valueMatrix θ' ⟨m, hm⟩ a) hWlb ι).support_lt)
      exact hgate.mul hres
    exact puncturedBoundedAt_of_tendsto (hcollapse.add hsum)
  · -- Tendsto G
    exact step1EvalLayersLT_tendsto (hr := hr) hτm
      (step1ResiduePoly_support H.chains h p.1 ι)
  · -- visible ⇒ g0 ≠ 0
    intro hvis
    have hne := step1TowerDominance_eval_ne_zero (hr := hr) (H := H) (p := p) (h := h)
      (j := m) (τ := τ) (Nat.le_succ m) (step1FinalTowerDominance (hr := hr) hτm)
      (Sum.inr (⟨ι, hvis⟩ : Step1ResidueCoordinateIndex H p.1 h))
      (le_of_eq (step1DominanceFamilyChainLength_residue H p.1 h ⟨ι, hvis⟩))
    exact hne
  · -- decomposition equality
    have hΩsucc : ∀ᶠ z in puncturedNhds τ,
        z ∈ (step1ActiveStratificationData hr H p).Omega (m + 1) := by
      have hstratum : τ ∈ step1ActiveStratum hr H p h m := by
        have hmem := (step1TierCascadeData hr H).tier_in_stratum hτm
        simpa [step1TierCascadeData] using hmem
      exact step1ActiveStratum_punctured_omega_succ (hr := hr) hm hstratum
    filter_upwards [hΩsucc] with z hz
    have hVdec : formalV θ' p.1.1 p.1.2 (m + 1) le_rfl
        = formalCollapseMatrix θ' ⟨m, hm⟩ *ᵥ Vm + formalGatedValueSum θ' ⟨m, hm⟩ *ᵥ Wm := by
      show (formalPoint θ' p.1.1 p.1.2 (m + 1) le_rfl).2 = _
      rw [formalPoint_succ]
      rfl
    have hobs : (step1ActiveStratificationData hr H p).observable z ι
        = evalFormalVecComplex (step1GateAssignment hr H p z)
            (formalV θ' p.1.1 p.1.2 (m + 1) le_rfl) ι :=
      congrFun (hD.observable_formula hz) ι
    have hobs2 :
        (step1ActiveStratificationData hr H p).observable z ι
          = evalFormalPolyComplex (step1GateAssignment hr H p z)
              ((formalCollapseMatrix θ' ⟨m, hm⟩ *ᵥ Vm) ι)
            + ∑ a : Fin k,
                step1GateAssignment hr H p z (⟨m, hm⟩, a)
                  * evalFormalPolyComplex (step1GateAssignment hr H p z)
                      ((formalValueMatrix θ' ⟨m, hm⟩ a *ᵥ Wm) ι) := by
      rw [hobs, hVdec, evalFormalVecComplex_add, Pi.add_apply]
      congr 1
      rw [evalFormalVecComplex_mulVec, evalFormalMatrixComplex_formalGatedValueSum,
        mulVec_sum_smul_apply]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      congr 1
      calc ((valueMatrix θ' ⟨m, hm⟩ a).map (algebraMap ℝ ℂ)
              *ᵥ evalFormalVecComplex (step1GateAssignment hr H p z) Wm) ι
          = (evalFormalMatrixComplex (step1GateAssignment hr H p z)
                (formalValueMatrix θ' ⟨m, hm⟩ a)
              *ᵥ evalFormalVecComplex (step1GateAssignment hr H p z) Wm) ι := by
              rw [formalValueMatrix, evalFormalMatrixComplex_realMatrixToFormal]
        _ = evalFormalVecComplex (step1GateAssignment hr H p z)
                (formalValueMatrix θ' ⟨m, hm⟩ a *ᵥ Wm) ι := by
              rw [evalFormalVecComplex_mulVec]
        _ = evalFormalPolyComplex (step1GateAssignment hr H p z)
                ((formalValueMatrix θ' ⟨m, hm⟩ a *ᵥ Wm) ι) := rfl
    have hsplit :
        (∑ a : Fin k, step1GateAssignment hr H p z (⟨m, hm⟩, a)
            * evalFormalPolyComplex (step1GateAssignment hr H p z)
                ((formalValueMatrix θ' ⟨m, hm⟩ a *ᵥ Wm) ι))
          = step1GateAssignment hr H p z (⟨m, hm⟩, sel)
              * evalFormalPolyComplex (step1GateAssignment hr H p z)
                  ((formalValueMatrix θ' ⟨m, hm⟩ sel *ᵥ Wm) ι)
            + ∑ a ∈ Finset.univ.erase sel,
                step1GateAssignment hr H p z (⟨m, hm⟩, a)
                  * evalFormalPolyComplex (step1GateAssignment hr H p z)
                      ((formalValueMatrix θ' ⟨m, hm⟩ a *ᵥ Wm) ι) :=
      (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ sel)).symm
    have hFsel :
        step1GateAssignment hr H p z (⟨m, hm⟩, sel)
            * evalFormalPolyComplex (step1GateAssignment hr H p z)
                ((formalValueMatrix θ' ⟨m, hm⟩ sel *ᵥ Wm) ι)
          = (step1ActiveStratificationData hr H p).gate (⟨m, hm⟩, sel) z
              * evalFormalPolyComplex (step1GateAssignment hr H p z)
                  (step1ResiduePoly H.chains h p.1 ι) := by
      rw [hRsel, step1GateAssignment_eq_gate (hr := hr) H p z ⟨m, hm⟩ sel]
    rw [hobs2, hsplit, hFsel]
    ring

/-! ## Deliverable 4 — the reduced final-tier visible-coordinate blowup payload -/

/-- **`lem:final-tier-blowup`.**  The reduced final-tier payload: at every final-tier point
some visible observable coordinate blows up.  The coordinate is chosen by
`exists_step1VisibleCoordinate`; the blowup follows from the local residue decomposition
(deliverable 2) and the selected-gate pole (deliverable 1) through
`BlowsUpAt.bounded_add_mul_tendsto_ne_zero`. -/
noncomputable def step1FinalTierVisibleBlowupPayloads {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ') :
    Step1FinalTierVisibleBlowupPayloads hr H where
  finalTier_visibleCoordinate_blowup := by
    intro p h τ hτ
    obtain ⟨ι, hvis⟩ := exists_step1VisibleCoordinate H p h
    refine ⟨ι, hvis, ?_⟩
    obtain ⟨B, G, g0, hBbd, hGtend, hg0, hEq⟩ :=
      step1FinalObservableCoord_localResidue (hr := hr) hτ ι
    obtain ⟨κ, cκ, hκ, hNF⟩ := step1FinalSelectedGate_normalForm_of_tier (hr := hr) hτ
    have hA : BlowsUpAt ((step1ActiveStratificationData hr H p).gate
        (⟨m, Nat.lt_succ_self m⟩, step1SelectedHead H.chains h m)) τ :=
      hNF.blowsUpAt (by exact_mod_cast hκ)
    have hblow : BlowsUpAt (fun z => B z +
        (step1ActiveStratificationData hr H p).gate
          (⟨m, Nat.lt_succ_self m⟩, step1SelectedHead H.chains h m) z * G z) τ :=
      BlowsUpAt.bounded_add_mul_tendsto_ne_zero hBbd hA hGtend (hg0 hvis)
    have hgoal : BlowsUpAt
        (fun z => (step1ActiveStratificationData hr H p).observable z ι) τ := by
      have hnorm :
          (fun z => ‖B z +
              (step1ActiveStratificationData hr H p).gate
                (⟨m, Nat.lt_succ_self m⟩, step1SelectedHead H.chains h m) z * G z‖)
            =ᶠ[puncturedNhds τ]
            (fun z => ‖(step1ActiveStratificationData hr H p).observable z ι‖) := by
        filter_upwards [hEq] with z hz
        rw [hz]
      exact Filter.Tendsto.congr' hnorm hblow
    exact hgoal

end TransformerIdentifiability.NLayer.KHead.Step1
