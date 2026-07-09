import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.TierCascadeData
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.ActiveStratification
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.DominanceSibling
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.Hypotheses
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.SelectedTowers

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.KHead.Step1

universe uProbe uHead uCoord

/-!
# K-head Step 1 tier-cascade — concrete bridge from K06A and K04D

The universe-polymorphic tier-cascade API lives in `Step1/TierCascadeData.lean`.
This file instantiates it for concrete Step-1 data (`step1TierCascadeData`) and
carries the analytic payload records and their `_of_payloads` assembly.  The
per-item payload *constructors* (C4/C8/C9) live in the dedicated files
`Step1/TierLocal.lean`, `Step1/FinalBlowup.lean`, and `Step1/CascadeClosure.lean`.
-/

/-! ## Concrete Step 1 bridge from K06A and K04D -/

/-- Regular targets have every head active, in the K04D sense. -/
theorem allHeadsActive_of_regular {L k d : Nat} {r : Nat} {θ : Params L k d}
    (hθ : Regularity r θ) :
    AllHeadsActive θ := by
  intro l a
  exact Regularity.valueMatrix_ne_zero hθ l a

/-- Probes used by the concrete tier cascade carry their K06A separated-set proof. -/
abbrev Step1SeparatedProbe {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ') :
    Type :=
  {p : ProbePoint d // p ∈ H.separatedSet}

namespace Step1StandingHypotheses

/-- The K06A chosen separated probe, coerced into the separated-probe subtype used by
the concrete tier-cascade data. -/
noncomputable def chosenTierProbe {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ') :
    Step1SeparatedProbe H :=
  ⟨H.separatedProbePackage.probe, by
    simpa [Step1StandingHypotheses.separatedSet] using
      H.separatedProbePackage.probe_mem⟩

end Step1StandingHypotheses

/-- The K04D active-head stratification data for one separated Step 1 probe. -/
noncomputable def step1ActiveStratificationData {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H) :
    ActiveStratificationData (m + 1) k d :=
  Classical.choose
    (K04D_prop_singular_stratification hr θ' p.1.1 p.1.2)

/-- Specification of the K04D stratification chosen for a separated Step 1 probe. -/
theorem step1ActiveStratificationData_spec {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H) :
    ActiveHeadSingularStratification hr θ' p.1.1 p.1.2
      (step1ActiveStratificationData hr H p) :=
  Classical.choose_spec
    (K04D_prop_singular_stratification hr θ' p.1.1 p.1.2)

/-- The finite layer used to read concrete K04D level/gate data from a natural tier
index.  Out-of-range indices are sent to the first layer only to make the API total. -/
def step1LayerIndex (m : Nat) (j : Nat) : Fin (m + 1) :=
  if hj : j < m + 1 then ⟨j, hj⟩ else ⟨0, Nat.succ_pos m⟩

/-- Totalized K04D active stratum used by the concrete tier data.

The out-of-range value is empty because `TierCascadeData` fields are total in the
natural layer index, while the concrete cascade only consumes indices `< m + 1`. -/
def step1ActiveStratum {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (_h : Fin k) (j : Nat) : Set ℂ :=
  if _hj : j < m + 1 then
    (step1ActiveStratificationData hr H p).stratum j
  else ∅

theorem step1ActiveStratum_avoids_nonnegativeRealAxis {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ}
    (hτ : τ ∈ step1ActiveStratum hr H p h j) :
    τ ∉ nonnegativeRealAxis := by
  unfold step1ActiveStratum at hτ
  by_cases hj : j < m + 1
  · simp [hj] at hτ
    have hD := step1ActiveStratificationData_spec hr H p
    have hdisj := stratum_disjoint_nonnegativeRealAxis (hD := hD) ⟨j, hj⟩
    rw [Set.disjoint_left] at hdisj
    exact hdisj hτ
  · simp [hj] at hτ

theorem step1ActiveStratum_punctured_isolated {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ} (hj : j < m + 1)
    (hτ : τ ∈ step1ActiveStratum hr H p h j) :
    IsPuncturedIsolated (step1ActiveStratum hr H p h j) τ := by
  let D : ActiveStratificationData (m + 1) k d :=
    step1ActiveStratificationData hr H p
  have hD : ActiveHeadSingularStratification hr θ' p.1.1 p.1.2 D := by
    simpa [D] using step1ActiveStratificationData_spec hr H p
  have hτS : τ ∈ D.stratum j := by
    simpa [step1ActiveStratum, D, hj] using hτ
  let l : Fin (m + 1) := ⟨j, hj⟩
  have hCD : ClosedDiscreteIn (D.stratum j) (D.Omega j) := by
    simpa [D, l] using hD.stratum_closedDiscrete l
  have hτΩ : τ ∈ D.Omega j := hCD.subset hτS
  have hnotacc : τ ∉ acc (D.stratum j) := hCD.noAccum τ hτΩ
  have havoid :
      ∀ᶠ z in puncturedNhds τ, z ∉ D.stratum j :=
    TransformerIdentifiability.NLayer.eventually_notMem_of_not_mem_acc hnotacc
  simpa [IsPuncturedIsolated, puncturedNhds, step1ActiveStratum, D, hj] using havoid

theorem step1ActiveStratum_punctured_omega_succ {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ} (hj : j < m + 1)
    (hτ : τ ∈ step1ActiveStratum hr H p h j) :
    ∀ᶠ z in puncturedNhds τ,
      z ∈ (step1ActiveStratificationData hr H p).Omega (j + 1) := by
  let D : ActiveStratificationData (m + 1) k d :=
    step1ActiveStratificationData hr H p
  have hD : ActiveHeadSingularStratification hr θ' p.1.1 p.1.2 D := by
    simpa [D] using step1ActiveStratificationData_spec hr H p
  have hτS : τ ∈ D.stratum j := by
    simpa [step1ActiveStratum, D, hj] using hτ
  let l : Fin (m + 1) := ⟨j, hj⟩
  have hCD : ClosedDiscreteIn (D.stratum j) (D.Omega j) := by
    simpa [D, l] using hD.stratum_closedDiscrete l
  have hτΩ : τ ∈ D.Omega j := hCD.subset hτS
  have hnotacc : τ ∉ acc (D.stratum j) := hCD.noAccum τ hτΩ
  have havoid :
      ∀ᶠ z in puncturedNhds τ, z ∉ D.stratum j :=
    TransformerIdentifiability.NLayer.eventually_notMem_of_not_mem_acc hnotacc
  have hΩevent : ∀ᶠ z in puncturedNhds τ, z ∈ D.Omega j := by
    simpa [puncturedNhds] using
      (nhdsWithin_le_nhds ((hD.domain j (Nat.le_of_lt hj)).isOpen.mem_nhds hτΩ))
  filter_upwards [hΩevent, havoid] with z hzΩ hzS
  simpa [D, l, hD.omega_succ l] using
    (show z ∈ D.Omega j \ D.stratum j from ⟨hzΩ, hzS⟩)

theorem step1_firstLayerHead_active {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (h : Fin k) :
    h ∈ activeHeads θ' ⟨0, Nat.succ_pos m⟩ := by
  simpa [IsActiveHead] using
    Regularity.valueMatrix_ne_zero H.target_regular ⟨0, Nat.succ_pos m⟩ h

theorem step1_firstLayerSlope_ne_zero {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : Step1SeparatedProbe H) (h : Fin k) :
    firstLayerSlope θ' h p.1 ≠ 0 :=
  p.2.1.1 h

/-- The affine sigmoid pole progression is indexed injectively by `ℤ` when the slope
is nonzero. -/
theorem affineSigmoidPole_injective (b lam : ℝ) (hlam : lam ≠ 0) :
    Function.Injective (affineSigmoidPole b lam) := by
  intro n m h
  have hmul := congrArg (fun z : ℂ => z * (lam : ℂ)) h
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  simp [affineSigmoidPole, TransformerIdentifiability.NLayer.sigmoidPole, hlamC] at hmul
  exact hmul

/-- Affine sigmoid pole progressions are nonempty. -/
theorem affineSigmoidPoleSet_nonempty (b lam : ℝ) :
    (affineSigmoidPoleSet b lam).Nonempty :=
  ⟨affineSigmoidPole b lam 0, 0, rfl⟩

/-- Nonconstant affine sigmoid pole progressions are infinite. -/
theorem affineSigmoidPoleSet_infinite (b lam : ℝ) (hlam : lam ≠ 0) :
    (affineSigmoidPoleSet b lam).Infinite := by
  simpa [affineSigmoidPoleSet, affineSigmoidPole,
    TransformerIdentifiability.NLayer.firstPoleSet] using
    (Set.infinite_range_iff (affineSigmoidPole_injective b lam hlam)).2
      (by infer_instance : Infinite ℤ)

theorem firstLayerPoleProgression_notMem_realAxis_of_separated {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d}
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) {τ : ℂ}
    (hτ : τ ∈ firstLayerPoleProgression r θ' p.1 h) :
    τ ∉ realAxis := by
  intro hreal
  rcases hreal with ⟨x, rfl⟩
  exact ofReal_notMem_affineSigmoidPoleSet (logScale r)
    (firstLayerSlope θ' h p.1) x
    (step1_firstLayerSlope_ne_zero H p h) hτ

theorem step1_firstPole_subset_activeStratum {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) :
    firstLayerPoleProgression r θ' p.1 h ⊆
      (step1ActiveStratificationData hr H p).stratum 0 := by
  intro τ hτ
  have hD := step1ActiveStratificationData_spec hr H p
  exact affineSigmoidPoleSet_subset_first_stratum hD (Nat.succ_pos m)
    (step1_firstLayerHead_active H h)
    (by
      simpa [firstLayerSlope] using step1_firstLayerSlope_ne_zero H p h)
    hτ

theorem step1_firstPole_subset_activeStratumTotal {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) :
    firstLayerPoleProgression r θ' p.1 h ⊆
      step1ActiveStratum hr H p h 0 := by
  intro τ hτ
  have hactive := step1_firstPole_subset_activeStratum (hr := hr) H p h hτ
  simpa [step1ActiveStratum, Nat.succ_pos] using hactive

/-- Concrete formal gate assignment used by K04E tower dominance along a Step 1 probe. -/
noncomputable def step1GateAssignment {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (τ : ℂ) : FormalVar (m + 1) k -> ℂ :=
  activeComplexGateAssignment θ' (step1ActiveStratificationData hr H p) τ

theorem step1GateAssignment_eq_gate {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (τ : ℂ) (l : Fin (m + 1)) (a : Fin k) :
    step1GateAssignment hr H p τ (l, a) =
      (step1ActiveStratificationData hr H p).gate (l, a) τ := by
  have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
  exact activeComplexGateAssignment_eq_of_active θ'
    (step1ActiveStratificationData hr H p) τ
    ((mem_activeHeads θ' l a).2 (hactiveAll l a))

/-- Selected-level odd-pi collision at a concrete Step 1 layer. -/
def step1SelectedLevelPole {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) (j : Nat) (τ : ℂ) : Prop :=
  if hj : j < m + 1 then
    (step1ActiveStratificationData hr H p).level
      (⟨j, hj⟩, step1SelectedHead H.chains h j) τ ∈ Pi
  else False

/-- True selected-only collision semantics: the selected level hits `Π` and every
sibling level in the same concrete layer avoids `Π`. -/
def step1SelectedOnlyCollision {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) (j : Nat) (τ : ℂ) : Prop :=
  if hj : j < m + 1 then
    (step1ActiveStratificationData hr H p).level
        (⟨j, hj⟩, step1SelectedHead H.chains h j) τ ∈ Pi ∧
      ∀ c : Fin k, c ≠ step1SelectedHead H.chains h j ->
        (step1ActiveStratificationData hr H p).level (⟨j, hj⟩, c) τ ∉ Pi
  else False

theorem step1SelectedOnlyCollision.selectedLevelPole {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ}
    (hcollision : step1SelectedOnlyCollision hr H p h j τ) :
    step1SelectedLevelPole hr H p h j τ := by
  unfold step1SelectedOnlyCollision step1SelectedLevelPole at *
  by_cases hj : j < m + 1
  · simp [hj] at hcollision ⊢
    exact hcollision.1
  · simp [hj] at hcollision

/-- The concrete selected level function at a Step 1 layer.  The layer-bound proof is
kept explicit so downstream pole and sibling packages can mention the same function. -/
noncomputable def step1SelectedLevelFunction {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) (j : Nat) (hj : j < m + 1) : ℂ -> ℂ :=
  (step1ActiveStratificationData hr H p).level
    (⟨j, hj⟩, step1SelectedHead H.chains h j)

/-- Pole-oriented successor selected-level payload for the concrete Step 1 cascade.

This is the K04E-facing replacement for the old successor collision wrapper: at the
lower-tier point `τ`, the successor selected level is meromorphic, is not analytic, and
carries the strengthened local arc package that produces arbitrarily close `Π`-preimages. -/
noncomputable def step1SuccessorSelectedLevelPole {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) (j : Nat) (τ : ℂ) : Prop :=
  if hj : j < m + 1 then
    MeromorphicAt (step1SelectedLevelFunction hr H p h j hj) τ ∧
      ¬ AnalyticAt ℂ (step1SelectedLevelFunction hr H p h j hj) τ ∧
        ∃ q : Nat, ArcStructureResult (step1SelectedLevelFunction hr H p h j hj) τ q
  else False

theorem step1SuccessorSelectedLevelPole.meromorphicAt {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ} (hj : j < m + 1)
    (hpole : step1SuccessorSelectedLevelPole hr H p h j τ) :
    MeromorphicAt (step1SelectedLevelFunction hr H p h j hj) τ := by
  simp [step1SuccessorSelectedLevelPole, hj] at hpole
  exact hpole.1

theorem step1SuccessorSelectedLevelPole.not_analyticAt {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ} (hj : j < m + 1)
    (hpole : step1SuccessorSelectedLevelPole hr H p h j τ) :
    ¬ AnalyticAt ℂ (step1SelectedLevelFunction hr H p h j hj) τ := by
  simp [step1SuccessorSelectedLevelPole, hj] at hpole
  exact hpole.2.1

theorem step1SuccessorSelectedLevelPole.arcStructure {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ} (hj : j < m + 1)
    (hpole : step1SuccessorSelectedLevelPole hr H p h j τ) :
    ∃ q : Nat, ArcStructureResult (step1SelectedLevelFunction hr H p h j hj) τ q := by
  simp [step1SuccessorSelectedLevelPole, hj] at hpole
  exact hpole.2.2

theorem step1SuccessorSelectedLevelPole.levelPreimageResult {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ} (hj : j < m + 1)
    (hpole : step1SuccessorSelectedLevelPole hr H p h j τ) :
    LevelPreimageResult (step1SelectedLevelFunction hr H p h j hj) τ := by
  rcases hpole.arcStructure hj with ⟨q, harc⟩
  exact lem_level_preimage harc

/-- Explicit successor-pole normal form at a Step 1 tier point.

This is the Lean-facing payload from `lem:successor-pole` and
`cor:successor-pole-payload`: it keeps the exact Laurent normal form, one
punctured stratification domain, and the K04E arc package together. -/
structure Step1SuccessorPoleNormalForm {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) (j : Nat) (hj : j < m + 1) (τ : ℂ) : Type where
  q : Nat
  q_pos : 1 ≤ q
  coeff : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  punctured_subset_successorOmega :
    puncturedDisc τ radius ⊆ (step1ActiveStratificationData hr H p).Omega j
  normalForm :
    LaurentNormalFormAt (step1SelectedLevelFunction hr H p h j hj) τ (q : ℤ) coeff
  arcStructure :
    ArcStructureResult (step1SelectedLevelFunction hr H p h j hj) τ q

namespace Step1SuccessorPoleNormalForm

/-- The leading Laurent coefficient in the successor normal form is nonzero. -/
theorem coeff_ne_zero {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {hj : j < m + 1} {τ : ℂ}
    (N : Step1SuccessorPoleNormalForm hr H p h j hj τ) :
    N.coeff ≠ 0 :=
  N.normalForm.coeff_ne_zero

/-- The successor normal form is meromorphic at the tier point. -/
theorem meromorphicAt {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {hj : j < m + 1} {τ : ℂ}
    (N : Step1SuccessorPoleNormalForm hr H p h j hj τ) :
    MeromorphicAt (step1SelectedLevelFunction hr H p h j hj) τ :=
  N.normalForm.meromorphicAt

/-- The positive-order successor normal form is not analytic at the tier point. -/
theorem not_analyticAt {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {hj : j < m + 1} {τ : ℂ}
    (N : Step1SuccessorPoleNormalForm hr H p h j hj τ) :
    ¬ AnalyticAt ℂ (step1SelectedLevelFunction hr H p h j hj) τ := by
  have hq : (1 : ℤ) ≤ (N.q : ℤ) := by
    exact_mod_cast N.q_pos
  exact N.normalForm.not_analyticAt hq

/-- The explicit normal form fills the existing pole-oriented successor field. -/
theorem successorSelectedLevelPole {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {hj : j < m + 1} {τ : ℂ}
    (N : Step1SuccessorPoleNormalForm hr H p h j hj τ) :
    step1SuccessorSelectedLevelPole hr H p h j τ := by
  simp [step1SuccessorSelectedLevelPole, hj]
  exact ⟨N.meromorphicAt, N.not_analyticAt, ⟨N.q, N.arcStructure⟩⟩

end Step1SuccessorPoleNormalForm

theorem step1_firstPole_selectedLevelPole {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) {τ : ℂ}
    (hτ : τ ∈ firstLayerPoleProgression r θ' p.1 h) :
    step1SelectedLevelPole hr H p h 0 τ := by
  let D : ActiveStratificationData (m + 1) k d :=
    step1ActiveStratificationData hr H p
  let l : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩
  have hD : ActiveHeadSingularStratification hr θ' p.1.1 p.1.2 D := by
    simpa [D] using step1ActiveStratificationData_spec hr H p
  have hΩ : τ ∈ D.Omega l.1 := by
    simp [D, l, hD.omega_zero]
  have hlevel :
      D.level (l, h) τ =
        τ * (firstLayerSlope θ' h p.1 : ℂ) + (logScale r : ℂ) := by
    have hEq :
        D.level (l, h) τ =
          τ * evalFormalPolyComplex (activeComplexGateAssignment θ' D τ)
            (formalSlope θ' p.1.1 p.1.2 l h) + (logScale r : ℂ) :=
      hD.level_formula l h (step1_firstLayerHead_active H h) hΩ
    have hfirst :
        evalFormalPolyComplex (activeComplexGateAssignment θ' D τ)
            (formalSlope θ' p.1.1 p.1.2 l h) =
          (firstLayerSlope θ' h p.1 : ℂ) := by
      simpa [l, firstLayerSlope] using
        evalFormalPolyComplex_formalSlope_first θ' p.1.1 p.1.2
          (Nat.succ_pos m) h (activeComplexGateAssignment θ' D τ)
    simpa [hfirst] using hEq
  have harg_left :
      (firstLayerSlope θ' h p.1 : ℂ) * τ + (logScale r : ℂ) ∈ Pi :=
    (firstLayerPoleProgression_hits_Pi
      (step1_firstLayerSlope_ne_zero H p h) τ).1 hτ
  have harg :
      τ * (firstLayerSlope θ' h p.1 : ℂ) + (logScale r : ℂ) ∈ Pi := by
    convert harg_left using 1
    ring
  have hpole : D.level (l, h) τ ∈ Pi := by
    simpa [hlevel] using harg
  simpa [step1SelectedLevelPole, step1SelectedHead, D, l] using hpole

theorem step1SelectedOnlyCollision_mem_activeStratum {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ}
    (hΩ : τ ∈ (step1ActiveStratificationData hr H p).Omega j)
    (hcollision : step1SelectedOnlyCollision hr H p h j τ) :
    τ ∈ step1ActiveStratum hr H p h j := by
  unfold step1SelectedOnlyCollision at hcollision
  unfold step1ActiveStratum
  by_cases hj : j < m + 1
  · simp [hj] at hcollision ⊢
    have hD := step1ActiveStratificationData_spec hr H p
    rw [hD.stratum_eq ⟨j, hj⟩]
    refine ⟨step1SelectedHead H.chains h j, ?_, hΩ, hcollision.1⟩
    have hactiveAll : AllHeadsActive θ' := allHeadsActive_of_regular H.target_regular
    exact (mem_activeHeads θ' ⟨j, hj⟩ (step1SelectedHead H.chains h j)).2
      (hactiveAll ⟨j, hj⟩ (step1SelectedHead H.chains h j))
  · simp [hj] at hcollision

/-- True K04E tower-dominance readiness (strict finite-family form, TeX `(T3)`):
for every member of the fixed finite dominance family `𝓕_h`, each selected-tower
threshold whose selected layer is staged strictly below the tier index `j` is
dominated by the corresponding selected gate value.  These strict inequalities feed
the non-strict K04E interface via `step1TowerDominance_satisfiesThresholds`. -/
def step1TowerDominance {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) (j : Nat) (τ : ℂ) : Prop :=
  if _hj : j ≤ m + 1 then
    ∀ (ix : Step1DominanceFamilyIndex H p.1 h)
      (i : Fin (step1DominanceFamilyChainLength H p.1 h
        (step1DominanceFamily H p.2 h ix).idx)),
      i.1 < j ->
        dominanceTowerThreshold (step1DominanceFamily H p.2 h ix).tower i
            (step1GateAssignment hr H p τ)
          < ‖step1GateAssignment hr H p τ
              ((step1DominanceFamilyHeadChain H p.1 h
                (step1DominanceFamily H p.2 h ix).idx).selectedVar i)‖
  else False

/-- Reduced form of `step1TowerDominance` under the tier bound `j ≤ m + 1`. -/
theorem step1TowerDominance_iff {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ} (hj : j ≤ m + 1)
    (hdom : step1TowerDominance hr H p h j τ)
    (ix : Step1DominanceFamilyIndex H p.1 h)
    (i : Fin (step1DominanceFamilyChainLength H p.1 h
      (step1DominanceFamily H p.2 h ix).idx))
    (hi : i.1 < j) :
    dominanceTowerThreshold (step1DominanceFamily H p.2 h ix).tower i
        (step1GateAssignment hr H p τ)
      < ‖step1GateAssignment hr H p τ
          ((step1DominanceFamilyHeadChain H p.1 h
            (step1DominanceFamily H p.2 h ix).idx).selectedVar i)‖ := by
  have hdom' := hdom
  unfold step1TowerDominance at hdom'
  rw [dif_pos hj] at hdom'
  exact hdom' ix i hi

/-- Conversion to the K04E non-strict tower-threshold interface: on the concrete gate
assignment, whenever every selected layer of the member `ix` is staged below the tier
index `j`, the strict finite-family dominance gives `SatisfiesTowerThresholds` for that
member's tower.  The thresholds are `≥ 1 ≥ 0`, so the strict `<` supplies the non-strict
coercion-norm inequality. -/
theorem step1TowerDominance_satisfiesThresholds {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ} (hj : j ≤ m + 1)
    (hdom : step1TowerDominance hr H p h j τ)
    (ix : Step1DominanceFamilyIndex H p.1 h)
    (hstages : step1DominanceFamilyChainLength H p.1 h
      (step1DominanceFamily H p.2 h ix).idx ≤ j) :
    SatisfiesTowerThresholds
      (step1DominanceFamilyHeadChain H p.1 h (step1DominanceFamily H p.2 h ix).idx)
      (dominanceTowerThreshold (step1DominanceFamily H p.2 h ix).tower)
      (step1GateAssignment hr H p τ) := by
  intro i
  have hnonneg : (0 : ℝ) ≤
      dominanceTowerThreshold (step1DominanceFamily H p.2 h ix).tower i
        (step1GateAssignment hr H p τ) :=
    le_trans zero_le_one
      (towerThreshold_ge_one (step1DominanceFamily H p.2 h ix).tower
        (step1DominanceFamily H p.2 h ix).topConstant_ne_zero i
        (step1GateAssignment hr H p τ))
  have hnorm : ‖((dominanceTowerThreshold (step1DominanceFamily H p.2 h ix).tower i
        (step1GateAssignment hr H p τ) : ℝ) : ℂ)‖ =
      dominanceTowerThreshold (step1DominanceFamily H p.2 h ix).tower i
        (step1GateAssignment hr H p τ) := by
    simp [abs_of_nonneg hnonneg]
  rw [hnorm]
  exact le_of_lt
    (step1TowerDominance_iff hj hdom ix i (lt_of_lt_of_le i.2 hstages))

/-- Member-wise nonvanishing: from strict finite-family dominance at tier `j` together
with the member's selected layers all staged below `j`, the member polynomial does not
vanish at the concrete gate assignment.  This is `dominance_tower_core_nonvanishing`
applied to the member's tower via `step1TowerDominance_satisfiesThresholds`. -/
theorem step1TowerDominance_eval_ne_zero {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ} (hj : j ≤ m + 1)
    (hdom : step1TowerDominance hr H p h j τ)
    (ix : Step1DominanceFamilyIndex H p.1 h)
    (hstages : step1DominanceFamilyChainLength H p.1 h
      (step1DominanceFamily H p.2 h ix).idx ≤ j) :
    (step1DominanceFamily H p.2 h ix).poly.eval₂ (algebraMap ℝ ℂ)
      (step1GateAssignment hr H p τ) ≠ 0 :=
  dominance_tower_core_nonvanishing
    (step1DominanceFamily H p.2 h ix).tower
    (step1DominanceFamily H p.2 h ix).degree_pos
    (step1DominanceFamily H p.2 h ix).topConstant_ne_zero
    (step1DominanceFamily H p.2 h ix).topConstant
    (step1DominanceFamily H p.2 h ix).finalCoeff
    (step1DominanceFamily H p.2 h ix).evalRecurrence
    (step1TowerDominance_satisfiesThresholds hj hdom ix hstages)

/-- Concrete K04E sibling family: index `0` is selected; successor indices are the
explicit nonselected siblings supplied by the caller. -/
noncomputable def step1SiblingLevelFamily {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) {j : Nat} (hj : j < m + 1) {K : Nat}
    (siblings : Fin K -> {c : Fin k // c ≠ step1SelectedHead H.chains h j}) :
    Fin (K + 1) -> ℂ -> ℂ :=
  Fin.cases
    ((step1ActiveStratificationData hr H p).level
      (⟨j, hj⟩, step1SelectedHead H.chains h j))
    (fun c =>
      (step1ActiveStratificationData hr H p).level (⟨j, hj⟩, (siblings c).1))

/-- Number of nonselected sibling heads, expressed by the canonical finite subtype
cardinality rather than hand-indexing `Fin (k - 1)`. -/
noncomputable def step1NonselectedSiblingCount {k : Nat} (a : Fin k) : Nat :=
  Fintype.card {c : Fin k // c ≠ a}

/-- Canonical enumeration of all nonselected sibling heads. -/
noncomputable def step1NonselectedSiblingEnumeration {k : Nat} (a : Fin k) :
    Fin (step1NonselectedSiblingCount a) -> {c : Fin k // c ≠ a} :=
  (Fintype.equivFin {c : Fin k // c ≠ a}).symm

theorem step1NonselectedSiblingEnumeration_injective {k : Nat} (a : Fin k) :
    Function.Injective
      (fun q : Fin (step1NonselectedSiblingCount a) =>
        (step1NonselectedSiblingEnumeration a q).1) := by
  intro q q' hq
  have hsub :
      step1NonselectedSiblingEnumeration a q =
        step1NonselectedSiblingEnumeration a q' := by
    apply Subtype.ext
    exact hq
  exact (Equiv.injective (Fintype.equivFin {c : Fin k // c ≠ a}).symm) hsub

theorem step1NonselectedSiblingEnumeration_cover {k : Nat} (a c : Fin k)
    (hc : c ≠ a) :
    ∃ q : Fin (step1NonselectedSiblingCount a),
      (step1NonselectedSiblingEnumeration a q).1 = c := by
  let x : {c : Fin k // c ≠ a} := ⟨c, hc⟩
  refine ⟨(Fintype.equivFin {c : Fin k // c ≠ a}) x, ?_⟩
  simp [step1NonselectedSiblingEnumeration, x]

/-- True sibling-readiness semantics for applying K04E sibling avoidance to the next
selected level family.  The sibling enumeration must cover exactly the nonselected heads. -/
def step1SiblingAvoidanceReady {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) (j : Nat) (τ : ℂ) : Prop :=
  if hj : j < m + 1 then
    ∃ (K : Nat)
      (siblings : Fin K -> {c : Fin k // c ≠ step1SelectedHead H.chains h j}),
      Function.Injective (fun q : Fin K => (siblings q).1) ∧
        (∀ c : Fin k, c ≠ step1SelectedHead H.chains h j ->
          ∃ q : Fin K, (siblings q).1 = c) ∧
        ∃ ρ0 : ℝ,
          SiblingAvoidanceResult
            ((step1ActiveStratificationData hr H p).Omega j) τ ρ0
            (step1SiblingLevelFamily hr H p h hj siblings)
  else False

theorem step1SiblingAvoidanceReady_of_result {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ} (hj : j < m + 1)
    {K : Nat}
    {siblings : Fin K -> {c : Fin k // c ≠ step1SelectedHead H.chains h j}}
    (hinj : Function.Injective (fun q : Fin K => (siblings q).1))
    (hcover : ∀ c : Fin k, c ≠ step1SelectedHead H.chains h j ->
      ∃ q : Fin K, (siblings q).1 = c)
    {ρ0 : ℝ}
    (hresult :
      SiblingAvoidanceResult
        ((step1ActiveStratificationData hr H p).Omega j) τ ρ0
        (step1SiblingLevelFamily hr H p h hj siblings)) :
    step1SiblingAvoidanceReady hr H p h j τ := by
  unfold step1SiblingAvoidanceReady
  simp [hj]
  exact ⟨K, siblings, hinj, hcover, ρ0, hresult⟩

theorem step1SiblingAvoidanceReady_of_canonicalResult {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ} (hj : j < m + 1)
    {ρ0 : ℝ}
    (hresult :
      SiblingAvoidanceResult
        ((step1ActiveStratificationData hr H p).Omega j) τ ρ0
        (step1SiblingLevelFamily hr H p h hj
          (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h j)))) :
    step1SiblingAvoidanceReady hr H p h j τ := by
  refine step1SiblingAvoidanceReady_of_result
    (hr := hr) (H := H) (p := p) (h := h) hj
    (step1NonselectedSiblingEnumeration_injective (step1SelectedHead H.chains h j))
    ?_ hresult
  intro c hc
  exact step1NonselectedSiblingEnumeration_cover
    (step1SelectedHead H.chains h j) c hc

theorem step1SiblingAvoidanceReady_conclusion {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ} (hj : j < m + 1)
    (hready : step1SiblingAvoidanceReady hr H p h j τ) :
    ∃ (K : Nat)
      (siblings : Fin K -> {c : Fin k // c ≠ step1SelectedHead H.chains h j}),
      Function.Injective (fun q : Fin K => (siblings q).1) ∧
        (∀ c : Fin k, c ≠ step1SelectedHead H.chains h j ->
          ∃ q : Fin K, (siblings q).1 = c) ∧
        ∃ _ : ℝ,
          SiblingAvoidanceConclusion τ
            (step1SiblingLevelFamily hr H p h hj siblings) := by
  unfold step1SiblingAvoidanceReady at hready
  simp [hj] at hready
  rcases hready with ⟨K, siblings, hinj, hcover, ρ0, hresult⟩
  exact ⟨K, siblings, hinj, hcover, ρ0, lem_sibling_avoidance hresult⟩

/-- A final observable coordinate is visible when the selected final residue vector has
nonzero value in that coordinate. -/
def step1VisibleCoordinate {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : Step1SeparatedProbe H) (h : Fin k) (c : Fin d) : Prop :=
  cascadeResidueVector (H.chains h) p.1 c ≠ 0

theorem exists_step1VisibleCoordinate {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d}
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) :
    ∃ c : Fin d, step1VisibleCoordinate H p h c := by
  classical
  have hres : cascadeResidueVector (H.chains h) p.1 ≠ 0 := (p.2.2.1 h).1
  by_contra hnone
  apply hres
  funext c
  by_contra hc
  exact hnone ⟨c, hc⟩

/-- Concrete tier-cascade data assembled from K06A separated probes, K04D active
stratification, and K04E selected-collision/dominance/sibling semantics. -/
noncomputable def step1TierCascadeData {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') :
    TierCascadeData (Step1SeparatedProbe H) (Fin k) (Fin d) where
  depth := m + 1
  depth_pos := Nat.succ_pos m
  separatedProbe := Set.univ
  selectedHead := fun _p h j => step1SelectedHead H.chains h j
  firstPoleSet := fun p h => firstLayerPoleProgression r θ' p.1 h
  omega := fun p _h j => (step1ActiveStratificationData hr H p).Omega j
  stratum := fun p h j => step1ActiveStratum hr H p h j
  level := fun p _h j a τ =>
    (step1ActiveStratificationData hr H p).level (step1LayerIndex m j, a) τ
  gate := fun p _h j a τ =>
    (step1ActiveStratificationData hr H p).gate (step1LayerIndex m j, a) τ
  dominanceThreshold := fun _p _h _j _τ => 0
  selectedOnlyCollision := fun p h j τ => step1SelectedOnlyCollision hr H p h j τ
  dominance := fun p h j τ => step1TowerDominance hr H p h j τ
  selectedGatePole := fun p h j τ =>
    step1SelectedLevelPole hr H p h j τ
  successorLevelPole := fun p h j τ =>
    step1SuccessorSelectedLevelPole hr H p h j τ
  siblingAvoidanceReady := fun p h j τ => step1SiblingAvoidanceReady hr H p h j τ
  observableCoord := fun p _h c τ =>
    (step1ActiveStratificationData hr H p).observable τ c
  visibleCoordinate := fun p h c => step1VisibleCoordinate H p h c
  firstPole_subset_stratum := by
    intro p h
    exact step1_firstPole_subset_activeStratumTotal (hr := hr) H p h
  successor_collision_mem_stratum := by
    intro p h j τ hτΩ hcollision
    exact step1SelectedOnlyCollision_mem_activeStratum (hr := hr) hτΩ hcollision
  stratum_avoids_nonnegativeRealAxis := by
    intro p h j τ hτ
    exact step1ActiveStratum_avoids_nonnegativeRealAxis (hr := hr) hτ

@[simp]
theorem step1TierCascadeData_depth {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') :
    (step1TierCascadeData hr H).depth = m + 1 :=
  rfl

@[simp]
theorem step1TierCascadeData_finalTierIndex {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') :
    (step1TierCascadeData hr H).finalTierIndex = m := by
  simp [TierCascadeData.finalTierIndex, step1TierCascadeData]

/-- The concrete first tier is nonempty for every separated Step 1 probe and head. -/
theorem step1TierCascadeData_firstTier_nonempty {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H) (h : Fin k) :
    ((step1TierCascadeData hr H).T p h 0).Nonempty := by
  simpa [step1TierCascadeData, firstLayerPoleProgression] using
    affineSigmoidPoleSet_nonempty (logScale r) (firstLayerSlope θ' h p.1)

/-- The concrete first tier is infinite for every separated Step 1 probe and head. -/
theorem step1TierCascadeData_firstTier_infinite {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H) (h : Fin k) :
    ((step1TierCascadeData hr H).T p h 0).Infinite := by
  have hslope : firstLayerSlope θ' h p.1 ≠ 0 :=
    step1_firstLayerSlope_ne_zero H p h
  simpa [step1TierCascadeData, firstLayerPoleProgression] using
    affineSigmoidPoleSet_infinite (logScale r) (firstLayerSlope θ' h p.1) hslope

theorem step1TierCascadeData_selectedGatePole {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j) :
    (step1TierCascadeData hr H).selectedGatePole p h j τ := by
  cases j with
  | zero =>
      have hfirst : τ ∈ firstLayerPoleProgression r θ' p.1 h := by
        simpa [step1TierCascadeData] using hτ
      have hpole := step1_firstPole_selectedLevelPole (hr := hr) H p h hfirst
      simpa [step1TierCascadeData] using hpole
  | succ j =>
      have hparts :
          τ ∈ (step1TierCascadeData hr H).omega p h (j + 1) ∧
            (step1TierCascadeData hr H).selectedOnlyCollision p h (j + 1) τ ∧
              τ ∉ nonnegativeRealAxis ∧
                (step1TierCascadeData hr H).dominance p h (j + 1) τ := by
        simpa using ((step1TierCascadeData hr H).mem_T_succ p h j (τ := τ)).mp hτ
      have hpole := step1SelectedOnlyCollision.selectedLevelPole hparts.2.1
      simpa [step1TierCascadeData] using hpole

theorem step1TierCascadeData_puncturedIsolatedStratum {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ}
    (hj : j < (step1TierCascadeData hr H).depth)
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j) :
    IsPuncturedIsolated ((step1TierCascadeData hr H).stratum p h j) τ := by
  have hj' : j < m + 1 := by
    simpa [step1TierCascadeData] using hj
  have hstratum : τ ∈ step1ActiveStratum hr H p h j := by
    have hmem := (step1TierCascadeData hr H).tier_in_stratum hτ
    simpa [step1TierCascadeData] using hmem
  have hisolated :=
    step1ActiveStratum_punctured_isolated (hr := hr) (H := H) (p := p)
      (h := h) hj' hstratum
  simpa [step1TierCascadeData] using hisolated

theorem step1TierCascadeData_puncturedOmegaSucc {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ}
    (hj : j < (step1TierCascadeData hr H).depth)
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j) :
    ∀ᶠ z in puncturedNhds τ,
      z ∈ (step1TierCascadeData hr H).omega p h (j + 1) := by
  have hj' : j < m + 1 := by
    simpa [step1TierCascadeData] using hj
  have hstratum : τ ∈ step1ActiveStratum hr H p h j := by
    have hmem := (step1TierCascadeData hr H).tier_in_stratum hτ
    simpa [step1TierCascadeData] using hmem
  have hΩ :=
    step1ActiveStratum_punctured_omega_succ (hr := hr) (H := H) (p := p)
      (h := h) hj' hstratum
  simpa [step1TierCascadeData] using hΩ

/-- The concrete tier singular set is exactly the K04D reduced singular set for
the active stratification attached to the separated probe. -/
theorem step1TierCascadeData_singularSet_eq_reducedSingularSet {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} (p : Step1SeparatedProbe H)
    (h : Fin k) :
    (step1TierCascadeData hr H).singularSet p h =
      reducedSingularSet (step1ActiveStratificationData hr H p) := by
  ext τ
  constructor
  · rintro ⟨j, hj, hτj⟩
    have hj' : j < m + 1 := by
      simpa [step1TierCascadeData] using hj
    have hτD : τ ∈ (step1ActiveStratificationData hr H p).stratum j := by
      have hτpair :
          j ≤ m ∧ τ ∈ (step1ActiveStratificationData hr H p).stratum j := by
        simpa [step1TierCascadeData, step1ActiveStratum] using hτj
      exact hτpair.2
    exact ⟨j, by simpa using hj', hτD⟩
  · rintro ⟨j, hj, hτj⟩
    have hj' : j < m + 1 := by
      simpa using hj
    have hjle : j ≤ m := Nat.lt_succ_iff.mp hj'
    have hτD : τ ∈ step1ActiveStratum hr H p h j := by
      simpa [step1ActiveStratum, hjle] using hτj
    exact ⟨j, by simpa [step1TierCascadeData] using hj', hτD⟩

/-- Final-tier points are punctured-isolated in the full concrete singular set.

This discharges the isolation half of `lem:final-tier-blowup`; the remaining
analytic payload is the observable-coordinate blowup. -/
theorem step1TierCascadeData_finalTier_isolated_singularSet {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h
      (step1TierCascadeData hr H).finalTierIndex) :
    IsPuncturedIsolated ((step1TierCascadeData hr H).singularSet p h) τ := by
  let D : ActiveStratificationData (m + 1) k d :=
    step1ActiveStratificationData hr H p
  have hD : ActiveHeadSingularStratification hr θ' p.1.1 p.1.2 D := by
    simpa [D] using step1ActiveStratificationData_spec hr H p
  have hSfull : StrataSystem D.stratum (m + 1) :=
    strataSystem_of_activeHeadSingularStratification hD
  have hS :
      StrataSystem D.stratum ((step1TierCascadeData hr H).finalTierIndex + 1) := by
    simpa [D, step1TierCascadeData_finalTierIndex] using hSfull
  have hτS :
      τ ∈ D.stratum (step1TierCascadeData hr H).finalTierIndex := by
    have hfinal_lt :
        (step1TierCascadeData hr H).finalTierIndex < m + 1 := by
      simpa [step1TierCascadeData] using
        (step1TierCascadeData hr H).finalTierIndex_lt_depth
    have hstratum :=
      (step1TierCascadeData hr H).finalTier_mem_finalStratum hτ
    have hstratum_pair :
        (step1TierCascadeData hr H).finalTierIndex ≤ m ∧
          τ ∈ D.stratum (step1TierCascadeData hr H).finalTierIndex := by
      simpa [D, step1TierCascadeData, step1ActiveStratum] using hstratum
    exact hstratum_pair.2
  have hτprev :
      τ ∉ partialUnion D.stratum (step1TierCascadeData hr H).finalTierIndex := by
    cases m with
    | zero =>
        simp [D, step1TierCascadeData_finalTierIndex, partialUnion]
    | succ m =>
        have hT :
            τ ∈ (step1TierCascadeData hr H).T p h (m + 1) := by
          simpa [step1TierCascadeData_finalTierIndex] using hτ
        have hparts :
            τ ∈ (step1TierCascadeData hr H).omega p h (m + 1) ∧
              (step1TierCascadeData hr H).selectedOnlyCollision p h (m + 1) τ ∧
                τ ∉ nonnegativeRealAxis ∧
                  (step1TierCascadeData hr H).dominance p h (m + 1) τ := by
          simpa using ((step1TierCascadeData hr H).mem_T_succ p h m (τ := τ)).mp hT
        have hΩ : τ ∈ D.Omega (m + 1) := by
          simpa [D, step1TierCascadeData] using hparts.1
        have hΩeq :
            D.Omega (m + 1) = (partialUnion D.stratum (m + 1))ᶜ := by
          simpa [D] using omega_eq_partialUnion_compl_derived hD (m + 1) (by omega)
        have hnot : τ ∉ partialUnion D.stratum (m + 1) := by
          simpa [hΩeq] using hΩ
        simpa [D, step1TierCascadeData_finalTierIndex] using hnot
  have hisol :
      IsPuncturedIsolated
        (partialUnion D.stratum ((step1TierCascadeData hr H).finalTierIndex + 1)) τ :=
    TransformerIdentifiability.NLayer.strata_punctured_isolated_partialUnion_succ
      (S := D.stratum)
      (j := (step1TierCascadeData hr H).finalTierIndex)
      hS hτS hτprev
  simpa [step1TierCascadeData_singularSet_eq_reducedSingularSet (hr := hr) p h,
    reducedSingularSet, D, step1TierCascadeData_finalTierIndex] using hisol

/-- Pointwise concrete tier-local assembly after the two nonformal successor payloads
are supplied.  The first four fields are already discharged by K04D/K06A bridge lemmas. -/
theorem step1TierCascadeData_tierLocalResult_of_successorPayloads {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ}
    (hj : j < (step1TierCascadeData hr H).depth)
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j)
    (hsucc :
      j + 1 < (step1TierCascadeData hr H).depth ->
        (step1TierCascadeData hr H).successorLevelPole p h (j + 1) τ)
    (hsibling :
      j + 1 < (step1TierCascadeData hr H).depth ->
        (step1TierCascadeData hr H).siblingAvoidanceReady p h (j + 1) τ) :
    TierCascadeData.TierLocalResult (step1TierCascadeData hr H) p h j τ where
  mem_stratum := (step1TierCascadeData hr H).tier_in_stratum hτ
  punctured_isolated_stratum :=
    step1TierCascadeData_puncturedIsolatedStratum (hr := hr) hj hτ
  punctured_omega_succ :=
    step1TierCascadeData_puncturedOmegaSucc (hr := hr) hj hτ
  selectedGatePole :=
    step1TierCascadeData_selectedGatePole (hr := hr) hτ
  successorSelectedLevelPole := hsucc
  siblingAvoidanceReady := hsibling

/-- Concrete `TierLocalStatement` reduced to the successor selected-level pole and
sibling-readiness payloads on nonfinal tiers. -/
theorem step1TierCascadeData_tierLocal_of_successorPayloads {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (hsucc :
      ∀ (p : Step1SeparatedProbe H) (h : Fin k) (j : Nat) (τ : ℂ),
        j < (step1TierCascadeData hr H).depth ->
          τ ∈ (step1TierCascadeData hr H).T p h j ->
            j + 1 < (step1TierCascadeData hr H).depth ->
              (step1TierCascadeData hr H).successorLevelPole p h (j + 1) τ)
    (hsibling :
      ∀ (p : Step1SeparatedProbe H) (h : Fin k) (j : Nat) (τ : ℂ),
        j < (step1TierCascadeData hr H).depth ->
          τ ∈ (step1TierCascadeData hr H).T p h j ->
            j + 1 < (step1TierCascadeData hr H).depth ->
              (step1TierCascadeData hr H).siblingAvoidanceReady p h (j + 1) τ) :
    TierCascadeData.TierLocalStatement (step1TierCascadeData hr H) := by
  intro p _hp h j τ hj hτ
  exact step1TierCascadeData_tierLocalResult_of_successorPayloads
    (hr := hr) hj hτ (hsucc p h j τ hj hτ) (hsibling p h j τ hj hτ)

theorem step1TierCascadeData_successorLevelPole_levelPreimageResult {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ}
    (hj : j < m + 1)
    (hpole : (step1TierCascadeData hr H).successorLevelPole p h j τ) :
    LevelPreimageResult (step1SelectedLevelFunction hr H p h j hj) τ := by
  have hpole' : step1SuccessorSelectedLevelPole hr H p h j τ := by
    simpa [step1TierCascadeData] using hpole
  exact hpole'.levelPreimageResult hj

theorem step1TierCascadeData_siblingAvoidanceReady_of_canonicalResult {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ}
    (hj : j < m + 1)
    {ρ0 : ℝ}
    (hresult :
      SiblingAvoidanceResult
        ((step1ActiveStratificationData hr H p).Omega j) τ ρ0
        (step1SiblingLevelFamily hr H p h hj
          (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h j)))) :
    (step1TierCascadeData hr H).siblingAvoidanceReady p h j τ := by
  have hready :
      step1SiblingAvoidanceReady hr H p h j τ :=
    step1SiblingAvoidanceReady_of_canonicalResult (hr := hr) (H := H)
      (p := p) (h := h) hj hresult
  simpa [step1TierCascadeData] using hready

/-- The remaining concrete analytic payloads needed for nonfinal Step 1 tier-local
structure.

K04D supplies the stratum/domain bookkeeping above, and K04E supplies the reusable
result interfaces.  The two fields here are the packet-local analytic bridge still
needed to turn tier membership into those K04E-shaped payloads: the successor
selected-level pole and the canonical sibling-avoidance result. -/
structure Step1TierLocalAnalyticPayloads {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') : Prop where
  successorSelectedLevelPole_of_tier :
    ∀ (p : Step1SeparatedProbe H) (h : Fin k) (j : Nat) (τ : ℂ),
      j < (step1TierCascadeData hr H).depth ->
        τ ∈ (step1TierCascadeData hr H).T p h j ->
          j + 1 < (step1TierCascadeData hr H).depth ->
            step1SuccessorSelectedLevelPole hr H p h (j + 1) τ
  canonicalSiblingAvoidanceResult_of_tier :
    ∀ (p : Step1SeparatedProbe H) (h : Fin k) (j : Nat) (τ : ℂ),
      j < (step1TierCascadeData hr H).depth ->
        τ ∈ (step1TierCascadeData hr H).T p h j ->
          (hsucc : j + 1 < (step1TierCascadeData hr H).depth) ->
            ∃ ρ0 : ℝ,
              SiblingAvoidanceResult
                ((step1ActiveStratificationData hr H p).Omega (j + 1)) τ ρ0
                (step1SiblingLevelFamily hr H p h
                  (by
                    simpa [step1TierCascadeData] using hsucc)
                  (step1NonselectedSiblingEnumeration
                    (step1SelectedHead H.chains h (j + 1))))

/-- TeX-shaped version of the tier-local analytic payloads.

The successor field is the explicit Laurent/arc normal form from
`lem:successor-pole`, while the sibling field is the canonical K04E
sequence-window result from `lem:sibling-package`. -/
structure Step1TierLocalNormalFormPayloads {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') : Type where
  successorPoleNormalForm_of_tier :
    ∀ (p : Step1SeparatedProbe H) (h : Fin k) (j : Nat) (τ : ℂ),
      j < (step1TierCascadeData hr H).depth ->
        τ ∈ (step1TierCascadeData hr H).T p h j ->
          (hsucc : j + 1 < (step1TierCascadeData hr H).depth) ->
            Step1SuccessorPoleNormalForm hr H p h (j + 1)
              (by
                simpa [step1TierCascadeData] using hsucc)
              τ
  canonicalSiblingAvoidanceResult_of_tier :
    ∀ (p : Step1SeparatedProbe H) (h : Fin k) (j : Nat) (τ : ℂ),
      j < (step1TierCascadeData hr H).depth ->
        τ ∈ (step1TierCascadeData hr H).T p h j ->
          (hsucc : j + 1 < (step1TierCascadeData hr H).depth) ->
            ∃ ρ0 : ℝ,
              SiblingAvoidanceResult
                ((step1ActiveStratificationData hr H p).Omega (j + 1)) τ ρ0
                (step1SiblingLevelFamily hr H p h
                  (by
                    simpa [step1TierCascadeData] using hsucc)
                  (step1NonselectedSiblingEnumeration
                    (step1SelectedHead H.chains h (j + 1))))

namespace Step1TierLocalNormalFormPayloads

/-- The TeX-shaped normal-form payload supplies the older analytic payload API. -/
theorem to_analyticPayloads {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (N : Step1TierLocalNormalFormPayloads hr H) :
    Step1TierLocalAnalyticPayloads hr H where
  successorSelectedLevelPole_of_tier := by
    intro p h j τ hj hτ hsucc
    exact (N.successorPoleNormalForm_of_tier p h j τ hj hτ hsucc).successorSelectedLevelPole
  canonicalSiblingAvoidanceResult_of_tier := by
    intro p h j τ hj hτ hsucc
    exact N.canonicalSiblingAvoidanceResult_of_tier p h j τ hj hτ hsucc

end Step1TierLocalNormalFormPayloads

/-- M4 successor selected-level pole payload, projected from the explicit analytic
payload package. -/
theorem step1SuccessorSelectedLevelPole_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (A : Step1TierLocalAnalyticPayloads hr H)
    {p : Step1SeparatedProbe H} {h : Fin k} {j : Nat} {τ : ℂ}
    (hj : j < (step1TierCascadeData hr H).depth)
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j)
    (hsucc : j + 1 < (step1TierCascadeData hr H).depth) :
    step1SuccessorSelectedLevelPole hr H p h (j + 1) τ :=
  A.successorSelectedLevelPole_of_tier p h j τ hj hτ hsucc

/-- M4 canonical sibling-avoidance payload, projected from the explicit analytic
payload package. -/
theorem step1CanonicalSiblingAvoidanceResult_of_tier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (A : Step1TierLocalAnalyticPayloads hr H)
    {p : Step1SeparatedProbe H} {h : Fin k} {j : Nat} {τ : ℂ}
    (hj : j < (step1TierCascadeData hr H).depth)
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j)
    (hsucc : j + 1 < (step1TierCascadeData hr H).depth) :
    ∃ ρ0 : ℝ,
      SiblingAvoidanceResult
        ((step1ActiveStratificationData hr H p).Omega (j + 1)) τ ρ0
        (step1SiblingLevelFamily hr H p h
          (by
            simpa [step1TierCascadeData] using hsucc)
          (step1NonselectedSiblingEnumeration
            (step1SelectedHead H.chains h (j + 1)))) :=
  A.canonicalSiblingAvoidanceResult_of_tier p h j τ hj hτ hsucc

/-- The concrete Step 1 tier-local statement closes once the two nonfinal analytic
payloads are supplied. -/
theorem step1TierCascadeData_tierLocal_of_analyticPayloads {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (A : Step1TierLocalAnalyticPayloads hr H) :
    TierCascadeData.TierLocalStatement (step1TierCascadeData hr H) := by
  refine step1TierCascadeData_tierLocal_of_successorPayloads
    (hr := hr) ?_ ?_
  · intro p h j τ hj hτ hsucc
    have hpole :
        step1SuccessorSelectedLevelPole hr H p h (j + 1) τ :=
      step1SuccessorSelectedLevelPole_of_tier (hr := hr) A hj hτ hsucc
    simpa [step1TierCascadeData] using hpole
  · intro p h j τ hj hτ hsucc
    have hj' : j + 1 < m + 1 := by
      simpa [step1TierCascadeData] using hsucc
    rcases step1CanonicalSiblingAvoidanceResult_of_tier (hr := hr) A hj hτ hsucc with
      ⟨ρ0, hresult⟩
    exact step1TierCascadeData_siblingAvoidanceReady_of_canonicalResult
      (hr := hr) (H := H) (p := p) (h := h) (j := j + 1) (τ := τ)
      hj' hresult

theorem step1SelectedOnlyCollision_of_canonicalSiblingLevelFamily {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} (hj : j < m + 1) {τ : ℂ}
    (hselected :
      (step1SiblingLevelFamily hr H p h hj
        (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h j))) 0 τ ∈ Pi)
    (hsiblings :
      ∀ q : Fin (step1NonselectedSiblingCount (step1SelectedHead H.chains h j)),
        (step1SiblingLevelFamily hr H p h hj
          (step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h j)))
            q.succ τ ∉ Pi) :
    step1SelectedOnlyCollision hr H p h j τ := by
  unfold step1SelectedOnlyCollision
  simp [hj]
  constructor
  · simpa [step1SiblingLevelFamily] using hselected
  · intro c hc
    rcases step1NonselectedSiblingEnumeration_cover
        (step1SelectedHead H.chains h j) c hc with
      ⟨q, hq⟩
    have hqavoid := hsiblings q
    simpa [step1SiblingLevelFamily, hq] using hqavoid

/-- Radius form of dominance persistence near a current tier point.

This is the finite-family dominance-persistence statement of the updated TeX:
inside one punctured disc around the current tier point, every point satisfies
the successor tier's concrete dominance condition. -/
structure Step1DominancePersistenceAtTier {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') (p : Step1SeparatedProbe H)
    (h : Fin k) (j : Nat) (τ : ℂ) : Type where
  radius : ℝ
  radius_pos : 0 < radius
  dominance_on_punctured :
    ∀ {z : ℂ}, z ∈ puncturedDisc τ radius ->
      step1TowerDominance hr H p h (j + 1) z

/-- Analytic payloads sufficient to prove concrete adjacent tier propagation.

The sibling field is the canonical package of `lem:sibling-package`; the
dominance field is `lem:dominance-persistence` in radius form. -/
structure Step1TierPropagationAnalyticPayloads {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') : Type where
  canonicalSiblingAvoidanceResult_of_tier :
    ∀ (p : Step1SeparatedProbe H) (h : Fin k) (j : Nat) (τ : ℂ),
      j < (step1TierCascadeData hr H).depth ->
        τ ∈ (step1TierCascadeData hr H).T p h j ->
          (hsucc : j + 1 < (step1TierCascadeData hr H).depth) ->
            ∃ ρ0 : ℝ,
              SiblingAvoidanceResult
                ((step1ActiveStratificationData hr H p).Omega (j + 1)) τ ρ0
                (step1SiblingLevelFamily hr H p h
                  (by
                    simpa [step1TierCascadeData] using hsucc)
                  (step1NonselectedSiblingEnumeration
                    (step1SelectedHead H.chains h (j + 1))))
  dominancePersistence_of_tier :
    ∀ (p : Step1SeparatedProbe H) (h : Fin k) (j : Nat) (τ : ℂ),
      j < (step1TierCascadeData hr H).depth ->
        τ ∈ (step1TierCascadeData hr H).T p h j ->
          j + 1 < (step1TierCascadeData hr H).depth ->
            Step1DominancePersistenceAtTier hr H p h j τ

/-- Concrete pointwise propagation from the two TeX analytic payloads:
canonical sibling avoidance and dominance persistence. -/
theorem step1TierCascadeData_tierPropagationResult_of_payloads {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (A : Step1TierPropagationAnalyticPayloads hr H)
    {p : Step1SeparatedProbe H} {h : Fin k} {j : Nat} {τ : ℂ}
    (hsucc : j + 1 < (step1TierCascadeData hr H).depth)
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j) :
    TierCascadeData.TierPropagationResult (step1TierCascadeData hr H) p h j τ := by
  classical
  have hj : j < (step1TierCascadeData hr H).depth := by omega
  have hj' : j + 1 < m + 1 := by
    simpa [step1TierCascadeData] using hsucc
  rcases A.canonicalSiblingAvoidanceResult_of_tier p h j τ hj hτ hsucc with
    ⟨ρ0, hresultRaw⟩
  let siblings :=
    step1NonselectedSiblingEnumeration (step1SelectedHead H.chains h (j + 1))
  let F : Fin (step1NonselectedSiblingCount (step1SelectedHead H.chains h (j + 1)) + 1) ->
      ℂ -> ℂ :=
    step1SiblingLevelFamily hr H p h hj' siblings
  have hresult :
      SiblingAvoidanceResult
        ((step1ActiveStratificationData hr H p).Omega (j + 1)) τ ρ0 F := by
    simpa [F, siblings] using hresultRaw
  let Dom := A.dominancePersistence_of_tier p h j τ hj hτ hsucc
  have hconclusion : SiblingAvoidanceConclusion τ F :=
    lem_sibling_avoidance hresult
  let hInf : EveryPuncturedDiscInfinite
      ((step1TierCascadeData hr H).T p h (j + 1)) τ := by
    intro ρ hρ
    let ρsmall : ℝ := min ρ (min ρ0 Dom.radius)
    have hρsmall_pos : 0 < ρsmall :=
      lt_min hρ (lt_min hresult.hypotheses.radius_pos Dom.radius_pos)
    have hρsmall_le_ρ : ρsmall ≤ ρ := min_le_left _ _
    have hρsmall_le_ρ0 : ρsmall ≤ ρ0 :=
      le_trans (min_le_right ρ (min ρ0 Dom.radius)) (min_le_left ρ0 Dom.radius)
    have hρsmall_le_dom : ρsmall ≤ Dom.radius :=
      le_trans (min_le_right ρ (min ρ0 Dom.radius)) (min_le_right ρ0 Dom.radius)
    have hgood :
        {z | z ∈ TransformerIdentifiability.NLayer.KHead.puncturedDisc τ ρsmall ∧
          F 0 z ∈ Pi ∧
          ∀ c : Fin (step1NonselectedSiblingCount
              (step1SelectedHead H.chains h (j + 1))),
            F c.succ z ∉ Pi}.Infinite :=
      hconclusion ρsmall hρsmall_pos
    refine hgood.mono ?_
    intro z hz
    rcases hz with ⟨hzpuncturedK, hselected, hsiblings⟩
    have hzpuncturedSmall : z ∈ puncturedDisc τ ρsmall := by
      simpa [puncturedDisc, TransformerIdentifiability.NLayer.KHead.puncturedDisc]
        using hzpuncturedK
    have hzpuncturedρ : z ∈ puncturedDisc τ ρ :=
      ⟨hzpuncturedSmall.1, lt_of_lt_of_le hzpuncturedSmall.2 hρsmall_le_ρ⟩
    have hzpuncturedρ0K :
        z ∈ TransformerIdentifiability.NLayer.KHead.puncturedDisc τ ρ0 := by
      have hzρ0 : z ∈ puncturedDisc τ ρ0 :=
        ⟨hzpuncturedSmall.1, lt_of_lt_of_le hzpuncturedSmall.2 hρsmall_le_ρ0⟩
      simpa [puncturedDisc, TransformerIdentifiability.NLayer.KHead.puncturedDisc]
        using hzρ0
    have hzΩ : z ∈ (step1ActiveStratificationData hr H p).Omega (j + 1) :=
      hresult.hypotheses.puncturedDisc_subset hzpuncturedρ0K
    have hcollision : step1SelectedOnlyCollision hr H p h (j + 1) z := by
      refine step1SelectedOnlyCollision_of_canonicalSiblingLevelFamily
        (hr := hr) (H := H) (p := p) (h := h) hj' ?_ ?_
      · simpa [F, siblings] using hselected
      · intro q
        simpa [F, siblings] using hsiblings q
    have hstratum : z ∈ step1ActiveStratum hr H p h (j + 1) :=
      step1SelectedOnlyCollision_mem_activeStratum (hr := hr) hzΩ hcollision
    have hoffAxis : z ∉ nonnegativeRealAxis :=
      step1ActiveStratum_avoids_nonnegativeRealAxis (hr := hr) hstratum
    have hdom : step1TowerDominance hr H p h (j + 1) z := by
      apply Dom.dominance_on_punctured
      exact ⟨hzpuncturedSmall.1,
        lt_of_lt_of_le hzpuncturedSmall.2 hρsmall_le_dom⟩
    have hT : z ∈ (step1TierCascadeData hr H).T p h (j + 1) := by
      rw [(step1TierCascadeData hr H).mem_T_succ p h j]
      exact ⟨by simpa [step1TierCascadeData] using hzΩ,
        by simpa [step1TierCascadeData] using hcollision,
        hoffAxis,
        by simpa [step1TierCascadeData] using hdom⟩
    exact ⟨hT, hzpuncturedρ⟩
  exact ⟨hInf, hInf.mem_acc⟩

/-- Concrete adjacent-tier propagation assembled from the 06b analytic payloads. -/
theorem step1TierCascadeData_tierPropagation_of_payloads {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (A : Step1TierPropagationAnalyticPayloads hr H) :
    TierCascadeData.TierPropagationStatement (step1TierCascadeData hr H) := by
  intro p _hp h j τ hsucc hτ
  exact step1TierCascadeData_tierPropagationResult_of_payloads
    (hr := hr) A hsucc hτ

/-- Analytic payloads for the final-tier blowup statement.

The first field is the final-domain/punctured-isolation bridge; the second is
the observable-coordinate pole/blowup bridge for a visible coordinate. -/
structure Step1FinalTierBlowupAnalyticPayloads {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') : Type where
  finalTier_isolated_singularSet :
    ∀ (p : Step1SeparatedProbe H) (h : Fin k) (τ : ℂ),
      τ ∈ (step1TierCascadeData hr H).T p h
        (step1TierCascadeData hr H).finalTierIndex ->
        IsPuncturedIsolated ((step1TierCascadeData hr H).singularSet p h) τ
  finalTier_visibleCoordinate_blowup :
    ∀ (p : Step1SeparatedProbe H) (h : Fin k) (τ : ℂ),
      τ ∈ (step1TierCascadeData hr H).T p h
        (step1TierCascadeData hr H).finalTierIndex ->
        ∃ c : Fin d,
          step1VisibleCoordinate H p h c ∧
            BlowsUpAt ((step1TierCascadeData hr H).observableCoord p h c) τ

/-- Reduced final-tier analytic payload after the singular-set isolation part has
been discharged from the concrete stratification.  The remaining analytic input
is the visible-coordinate blowup at final-tier points. -/
structure Step1FinalTierVisibleBlowupPayloads {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') : Type where
  finalTier_visibleCoordinate_blowup :
    ∀ (p : Step1SeparatedProbe H) (h : Fin k) (τ : ℂ),
      τ ∈ (step1TierCascadeData hr H).T p h
        (step1TierCascadeData hr H).finalTierIndex ->
      ∃ c : Fin d,
        step1VisibleCoordinate H p h c ∧
          BlowsUpAt ((step1TierCascadeData hr H).observableCoord p h c) τ

namespace Step1FinalTierVisibleBlowupPayloads

/-- The reduced visible-coordinate payload supplies the older final-blowup API;
final-tier isolation is now a theorem of the concrete tier cascade. -/
def to_analyticPayloads {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (V : Step1FinalTierVisibleBlowupPayloads hr H) :
    Step1FinalTierBlowupAnalyticPayloads hr H where
  finalTier_isolated_singularSet := by
    intro p h τ hτ
    exact step1TierCascadeData_finalTier_isolated_singularSet (hr := hr) hτ
  finalTier_visibleCoordinate_blowup := V.finalTier_visibleCoordinate_blowup

end Step1FinalTierVisibleBlowupPayloads

/-- Concrete final-tier blowup assembled from the final-tier analytic payloads. -/
theorem step1TierCascadeData_finalTierBlowup_of_payloads {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (A : Step1FinalTierBlowupAnalyticPayloads hr H) :
    TierCascadeData.FinalTierBlowupStatement (step1TierCascadeData hr H) := by
  intro p _hp h τ hτ
  refine ⟨?_, A.finalTier_isolated_singularSet p h τ hτ, ?_⟩
  · exact (step1TierCascadeData hr H).finalTier_mem_finalStratum hτ
  · rcases A.finalTier_visibleCoordinate_blowup p h τ hτ with ⟨c, hvisible, hblow⟩
    exact ⟨c, by simpa [step1TierCascadeData] using hvisible, hblow⟩

/-- Concrete final-tier blowup assembled from only the remaining visible-coordinate
blowup payload; singular-set isolation is supplied by
`step1TierCascadeData_finalTier_isolated_singularSet`. -/
theorem step1TierCascadeData_finalTierBlowup_of_visiblePayloads {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (V : Step1FinalTierVisibleBlowupPayloads hr H) :
    TierCascadeData.FinalTierBlowupStatement (step1TierCascadeData hr H) :=
  step1TierCascadeData_finalTierBlowup_of_payloads (hr := hr) V.to_analyticPayloads

/-- First/final nonemptiness payloads needed by the formal chain-cascade
composition.  The first-tier fields are the formal target of
`lem:first-tier-progression`; final-tier nonemptiness may be supplied either by
propagation from the first tier or directly by downstream analytic work. -/
structure Step1ChainCascadeSetPayloads {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') : Type where
  firstTier_nonempty :
    ∀ (p : Step1SeparatedProbe H), p ∈ (step1TierCascadeData hr H).separatedProbe ->
      ∀ h : Fin k, ((step1TierCascadeData hr H).T p h 0).Nonempty
  firstTier_infinite :
    ∀ (p : Step1SeparatedProbe H), p ∈ (step1TierCascadeData hr H).separatedProbe ->
      ∀ h : Fin k, ((step1TierCascadeData hr H).T p h 0).Infinite
  finalTier_nonempty :
    ∀ (p : Step1SeparatedProbe H), p ∈ (step1TierCascadeData hr H).separatedProbe ->
      ∀ h : Fin k,
        ((step1TierCascadeData hr H).T p h
          (step1TierCascadeData hr H).finalTierIndex).Nonempty

/-- Adjacent propagation supplies the final-tier nonemptiness field, while the
first-tier fields are the concrete affine pole progression facts. -/
noncomputable def step1ChainCascadeSetPayloads_of_propagation {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (P : Step1TierPropagationAnalyticPayloads hr H) :
    Step1ChainCascadeSetPayloads hr H where
  firstTier_nonempty := by
    intro p _hp h
    exact step1TierCascadeData_firstTier_nonempty (hr := hr) H p h
  firstTier_infinite := by
    intro p _hp h
    exact step1TierCascadeData_firstTier_infinite (hr := hr) H p h
  finalTier_nonempty := by
    intro p hp h
    exact TierCascadeData.finalTier_nonempty_of_firstTier_nonempty_propagation
      (D := step1TierCascadeData hr H)
      (step1TierCascadeData_tierPropagation_of_payloads (hr := hr) P)
      hp h (step1TierCascadeData_firstTier_nonempty (hr := hr) H p h)

/-- Concrete chain-cascade data from adjacent propagation and first/final set
payloads. -/
theorem step1ChainCascadeData_of_payloads {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (P : Step1TierPropagationAnalyticPayloads hr H)
    (S : Step1ChainCascadeSetPayloads hr H) :
    TierCascadeData.ChainCascadeData (step1TierCascadeData hr H) where
  firstTier_nonempty := S.firstTier_nonempty
  firstTier_infinite := S.firstTier_infinite
  propagation :=
    TierCascadeData.tierPropagation_subsetStatement
      (step1TierCascadeData_tierPropagation_of_payloads (hr := hr) P)
  finalTier_nonempty := S.finalTier_nonempty

/-- Concrete chain-cascade statement assembled from the 06b payloads. -/
theorem step1TierCascadeData_chainCascade_of_payloads {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (P : Step1TierPropagationAnalyticPayloads hr H)
    (S : Step1ChainCascadeSetPayloads hr H) :
    TierCascadeData.ChainCascadeStatement (step1TierCascadeData hr H) :=
  (step1ChainCascadeData_of_payloads (hr := hr) P S).statement

/-- Full concrete 06b payload bundle for the public `TierCascadeAPI`. -/
structure Step1TierCascadeAnalyticPayloads {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') : Type where
  tierLocal : Step1TierLocalAnalyticPayloads hr H
  propagation : Step1TierPropagationAnalyticPayloads hr H
  finalBlowup : Step1FinalTierBlowupAnalyticPayloads hr H
  chainSets : Step1ChainCascadeSetPayloads hr H

/-- The full analytic payload bundle can be assembled from the three genuine
analytic payload families; the chain-set payloads are then formal consequences of
the first-tier pole progression and adjacent propagation. -/
noncomputable def step1TierCascadeAnalyticPayloads_of_core_payloads {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (tierLocal : Step1TierLocalAnalyticPayloads hr H)
    (propagation : Step1TierPropagationAnalyticPayloads hr H)
    (finalBlowup : Step1FinalTierBlowupAnalyticPayloads hr H) :
    Step1TierCascadeAnalyticPayloads hr H where
  tierLocal := tierLocal
  propagation := propagation
  finalBlowup := finalBlowup
  chainSets := step1ChainCascadeSetPayloads_of_propagation (hr := hr) propagation

/-- Reduced full analytic payload assembly: final-tier singular-set isolation and
chain-set nonemptiness are formal consequences, so the final analytic input is
only the visible-coordinate blowup. -/
noncomputable def step1TierCascadeAnalyticPayloads_of_reduced_core_payloads {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (tierLocal : Step1TierLocalAnalyticPayloads hr H)
    (propagation : Step1TierPropagationAnalyticPayloads hr H)
    (finalBlowup : Step1FinalTierVisibleBlowupPayloads hr H) :
    Step1TierCascadeAnalyticPayloads hr H :=
  step1TierCascadeAnalyticPayloads_of_core_payloads (hr := hr)
    tierLocal propagation finalBlowup.to_analyticPayloads

/-- Public concrete 06b API assembled from explicit analytic payloads. -/
theorem step1TierCascadeAPI_of_payloads {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (A : Step1TierCascadeAnalyticPayloads hr H) :
    TierCascadeData.TierCascadeAPI (step1TierCascadeData hr H) where
  tier_local :=
    step1TierCascadeData_tierLocal_of_analyticPayloads (hr := hr) A.tierLocal
  tier_propagation :=
    step1TierCascadeData_tierPropagation_of_payloads (hr := hr) A.propagation
  final_tier_blowup :=
    step1TierCascadeData_finalTierBlowup_of_payloads (hr := hr) A.finalBlowup
  chain_cascade :=
    step1TierCascadeData_chainCascade_of_payloads (hr := hr) A.propagation A.chainSets

/-- Public concrete 06b API assembled from the reduced payload surface: adjacent
propagation supplies the chain sets, and final-tier isolation is formal. -/
theorem step1TierCascadeAPI_of_reduced_payloads {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'}
    (tierLocal : Step1TierLocalAnalyticPayloads hr H)
    (propagation : Step1TierPropagationAnalyticPayloads hr H)
    (finalBlowup : Step1FinalTierVisibleBlowupPayloads hr H) :
    TierCascadeData.TierCascadeAPI (step1TierCascadeData hr H) :=
  step1TierCascadeAPI_of_payloads (hr := hr)
    (step1TierCascadeAnalyticPayloads_of_reduced_core_payloads (hr := hr)
      tierLocal propagation finalBlowup)

/-- Terminal tiers satisfy the concrete tier-local result without successor payloads. -/
theorem step1TierCascadeData_tierLocalResult_of_no_successor {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {j : Nat} {τ : ℂ}
    (hj : j < (step1TierCascadeData hr H).depth)
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h j)
    (hterminal : ¬ j + 1 < (step1TierCascadeData hr H).depth) :
    TierCascadeData.TierLocalResult (step1TierCascadeData hr H) p h j τ := by
  refine step1TierCascadeData_tierLocalResult_of_successorPayloads
    (hr := hr) hj hτ ?_ ?_
  · intro hsucc
    exact (hterminal hsucc).elim
  · intro hsibling
    exact (hterminal hsibling).elim

/-- The concrete final tier satisfies `TierLocalResult` unconditionally. -/
theorem step1TierCascadeData_finalTierLocalResult {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {hr : 1 < r}
    {H : Step1StandingHypotheses r θ θ'} {p : Step1SeparatedProbe H}
    {h : Fin k} {τ : ℂ}
    (hτ : τ ∈ (step1TierCascadeData hr H).T p h
      (step1TierCascadeData hr H).finalTierIndex) :
    TierCascadeData.TierLocalResult (step1TierCascadeData hr H) p h
      (step1TierCascadeData hr H).finalTierIndex τ := by
  exact step1TierCascadeData_tierLocalResult_of_no_successor
    (hr := hr) (step1TierCascadeData hr H).finalTierIndex_lt_depth hτ
    (step1TierCascadeData hr H).finalTierIndex_succ_not_lt_depth

@[simp]
theorem step1TierCascadeData_separatedProbe {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') :
    (step1TierCascadeData hr H).separatedProbe = (Set.univ : Set (Step1SeparatedProbe H)) :=
  rfl

theorem chosenTierProbe_mem_step1TierCascadeData {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') :
    H.chosenTierProbe ∈ (step1TierCascadeData hr H).separatedProbe := by
  simp [step1TierCascadeData]


end TransformerIdentifiability.NLayer.KHead.Step1
