import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SigmoidMixtures
import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.Regularity
import AnyLayerIdentifiabilityProof.NLayer.KHead.Matching

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K-head depth-one base case

This file contains the depth-one endpoint used by packet `K05`.  The full TeX
argument derives the two data packages below from open-set transformer equality
via aggregate sigmoid-mixture recovery on a separated Zariski-dense probe set.
The Lean content here proves the algebraic/permutation endpoint once those
packet-specific recovery obligations are available.
-/

noncomputable section

/-- First-layer attention family in a depth-one `k`-head parameter. -/
def baseAttention {k d : Nat} (θ : Params 1 k d) :
    Fin k → Matrix (Fin d) (Fin d) ℝ :=
  fun h => attentionMatrix θ 0 h

/-- First-layer value family in a depth-one `k`-head parameter. -/
def baseValue {k d : Nat} (θ : Params 1 k d) :
    Fin k → Matrix (Fin d) (Fin d) ℝ :=
  fun h => valueMatrix θ 0 h

/-- The depth-one probe slope `wᵀ A_{1h} v`. -/
def baseSlope {k d : Nat} (θ : Params 1 k d) (w v : Vec d) :
    Fin k → ℝ :=
  fun h => matrixBilin (baseAttention θ h) w v

/-- Complexified depth-one residue coefficient `V_{1h} w`. -/
def baseCoeffC {k d : Nat} (θ : Params 1 k d) (w : Vec d) :
    Fin k → Fin d → ℂ :=
  fun h i => ((baseValue θ h *ᵥ w) i : ℂ)

/-- The entire affine part of the depth-one complex probe observable. -/
def baseEntirePartC {k d : Nat} (θ : Params 1 k d) (v : Vec d) :
    Fin d → ℂ :=
  fun i => ((collapseMatrix θ 0 *ᵥ v) i : ℂ)

/-- Depth-one complex probe observable as a finite sigmoid mixture. -/
def baseProbeMixtureC {k d : Nat} (r : Nat) (θ : Params 1 k d)
    (w v : Vec d) : ℂ → Fin d → ℂ :=
  sigmoidMixture (logScale r) (fun _ => baseEntirePartC θ v)
    (baseCoeffC θ w) (baseSlope θ w v)

@[simp]
theorem baseProbeMixtureC_apply {k d : Nat} (r : Nat) (θ : Params 1 k d)
    (w v : Vec d) (τ : ℂ) (i : Fin d) :
    baseProbeMixtureC r θ w v τ i =
      ((collapseMatrix θ 0 *ᵥ v) i : ℂ) +
        ∑ h : Fin k,
          csig (((baseSlope θ w v h : ℝ) : ℂ) * τ + (logScale r : ℂ)) *
            ((baseValue θ h *ᵥ w) i : ℂ) := by
  simp [baseProbeMixtureC, baseEntirePartC, baseCoeffC, sigmoidMixture]

/-- The TeX bias `log r` is nonzero under the standing base-case assumption
`1 < r`. -/
theorem logScale_ne_zero_of_one_lt {r : Nat} (hr : 1 < r) :
    logScale r ≠ 0 :=
  ne_of_gt (Real.log_pos (by exact_mod_cast hr))

/-- Regroup a finite sigmoid mixture by aggregate slope, coordinatewise.  This is
the cancellation-aware form needed when several heads share the same slope. -/
theorem sigmoidMixture_coord_eq_aggregate_image {p N : Nat} (b : ℝ)
    (H : ℂ → Fin N → ℂ) (M : Fin p → Fin N → ℂ) (lam : Fin p → ℝ)
    (τ : ℂ) (j : Fin N) :
    sigmoidMixture b H M lam τ j =
      H τ j + ∑ slope ∈ Finset.univ.image lam,
        csig ((slope : ℂ) * τ + (b : ℂ)) *
          aggregateCoeff M lam slope j := by
  classical
  simp only [sigmoidMixture, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  congr 1
  symm
  simp only [aggregateCoeff]
  have hgroup :=
    (Finset.sum_image'
      (s := (Finset.univ : Finset (Fin p)))
      (g := lam)
      (f := fun slope : ℝ =>
        csig ((slope : ℂ) * τ + (b : ℂ)) *
          ∑ h : Fin p, if lam h = slope then M h j else 0)
      (h := fun h : Fin p =>
        csig (((lam h : ℝ) : ℂ) * τ + (b : ℂ)) * M h j)
      ?_)
  have hleft :
      (∑ x ∈ Finset.univ.image lam,
        csig ((x : ℂ) * τ + (b : ℂ)) *
          (∑ c : Fin p, if lam c = x then M c else 0) j) =
      (∑ x ∈ Finset.univ.image lam,
        csig ((x : ℂ) * τ + (b : ℂ)) *
          ∑ c : Fin p, if lam c = x then M c j else 0) := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    congr 1
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro c _hc
    by_cases hc : lam c = x
    · simp [hc]
    · simp [hc]
  exact hleft.trans hgroup
  intro i _hi
  calc
    csig (((lam i : ℝ) : ℂ) * τ + (b : ℂ)) *
        ∑ h : Fin p, (if lam h = lam i then M h j else 0)
        = ∑ h : Fin p,
          csig (((lam i : ℝ) : ℂ) * τ + (b : ℂ)) *
            (if lam h = lam i then M h j else 0) := by
          rw [Finset.mul_sum]
    _ = ∑ h : Fin p,
          if lam h = lam i then
            csig (((lam h : ℝ) : ℂ) * τ + (b : ℂ)) * M h j
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro h _hh
          by_cases hh : lam h = lam i
          · simp [hh]
          · simp [hh]
    _ = ∑ h ∈ (Finset.univ : Finset (Fin p)) with lam h = lam i,
          csig (((lam h : ℝ) : ℂ) * τ + (b : ℂ)) * M h j := by
          rw [Finset.sum_filter]

/-- Coordinatewise holomorphy of a finite sigmoid mixture away from its aggregate
singular set.  The proof first regroups colliding slopes, so canceled aggregate
coefficients do not create artificial singularities. -/
theorem sigmoidMixture_coord_analyticOnNhd_compl {p N : Nat} (b : ℝ)
    (H : ℂ → Fin N → ℂ) (M : Fin p → Fin N → ℂ) (lam : Fin p → ℝ)
    (hH : ∀ j : Fin N,
      AnalyticOnNhd ℂ (fun τ : ℂ => H τ j) (mixtureSingularSet b M lam)ᶜ) :
    ∀ j : Fin N,
      AnalyticOnNhd ℂ (fun τ : ℂ => sigmoidMixture b H M lam τ j)
        (mixtureSingularSet b M lam)ᶜ := by
  classical
  intro j τ hτ
  have hrepr :
      (fun z : ℂ => sigmoidMixture b H M lam z j) =
        fun z : ℂ => H z j + ∑ slope ∈ Finset.univ.image lam,
          csig ((slope : ℂ) * z + (b : ℂ)) *
            aggregateCoeff M lam slope j := by
    funext z
    exact sigmoidMixture_coord_eq_aggregate_image b H M lam z j
  rw [hrepr]
  refine (hH j τ hτ).add ?_
  have hsumFun :
      (∑ slope ∈ Finset.univ.image lam,
        fun z : ℂ =>
          csig ((slope : ℂ) * z + (b : ℂ)) *
            aggregateCoeff M lam slope j) =
        (fun z : ℂ => ∑ slope ∈ Finset.univ.image lam,
          csig ((slope : ℂ) * z + (b : ℂ)) *
            aggregateCoeff M lam slope j) := by
    funext z
    simp
  rw [← hsumFun]
  refine Finset.analyticAt_sum
    (𝕜 := ℂ) (E := ℂ) (F := ℂ)
    (Finset.univ.image lam) ?_
  intro slope _hslope_image
  by_cases hcoord : aggregateCoeff M lam slope j = 0
  · simpa [hcoord] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) τ)
  · by_cases hslope0 : slope = 0
    · simpa [hslope0] using
        (analyticAt_const : AnalyticAt ℂ
          (fun _ : ℂ => csig (b : ℂ) * aggregateCoeff M lam slope j) τ)
    · have hvecne : aggregateCoeff M lam slope ≠ 0 := by
        intro hzero
        exact hcoord (congrFun hzero j)
      have hsupp : slope ∈ slopeSupportFinset M lam :=
        (mem_slopeSupportFinset_iff M lam slope).2 ⟨hslope0, hvecne⟩
      have hnotPole : τ ∉ affineSigmoidPoleSet b slope := by
        intro hτpole
        exact hτ (by
          rw [mixtureSingularSet]
          exact Set.mem_iUnion.2
            ⟨slope, Set.mem_iUnion.2 ⟨hsupp, hτpole⟩⟩)
      have hsig : AnalyticAt ℂ
          (fun z : ℂ => csig ((slope : ℂ) * z + (b : ℂ))) τ :=
        affine_csig_analyticAt_of_notMem_poleSet hslope0 hnotPole
      simpa using hsig.mul
        (analyticAt_const : AnalyticAt ℂ
          (fun _ : ℂ => aggregateCoeff M lam slope j) τ)

/-- The depth-one probe mixture is holomorphic away from its aggregate singular
set, coordinatewise. -/
theorem baseProbeMixtureC_coord_analyticOnNhd_compl {k d r : Nat}
    (θ : Params 1 k d) (w v : Vec d) (i : Fin d) :
    AnalyticOnNhd ℂ (fun τ : ℂ => baseProbeMixtureC r θ w v τ i)
      (mixtureSingularSet (logScale r) (baseCoeffC θ w)
        (baseSlope θ w v))ᶜ := by
  simpa [baseProbeMixtureC] using
    (sigmoidMixture_coord_analyticOnNhd_compl
      (b := logScale r) (H := fun _ : ℂ => baseEntirePartC θ v)
      (M := baseCoeffC θ w) (lam := baseSlope θ w v)
      (by
        intro j τ _hτ
        simpa using
          (analyticAt_const :
            AnalyticAt ℂ (fun _ : ℂ => baseEntirePartC θ v j) τ))
      i)

/-- Continuity form of `baseProbeMixtureC_coord_analyticOnNhd_compl`, used by
pole transfer. -/
theorem baseProbeMixtureC_coord_continuousAt_of_notMem_mixtureSingularSet
    {k d r : Nat} (θ : Params 1 k d) (w v : Vec d) (i : Fin d)
    {τ : ℂ}
    (hτ : τ ∉ mixtureSingularSet (logScale r) (baseCoeffC θ w)
      (baseSlope θ w v)) :
    ContinuousAt (fun z : ℂ => baseProbeMixtureC r θ w v z i) τ :=
  (baseProbeMixtureC_coord_analyticOnNhd_compl θ w v i τ hτ).continuousAt

/-- The closed probe output at depth one is exactly the depth-one mixture formula
on real positive or negative `τ`; no positivity is needed for the closed recursion. -/
theorem probeOutput_depth_one {k d r : Nat} (θ : Params 1 k d)
    (w v : Vec d) (τ : ℝ) :
    probeOutput r θ w v τ =
      collapseMatrix θ 0 *ᵥ v +
        ∑ h : Fin k,
          headGate r (baseAttention θ h) w v τ • (baseValue θ h *ᵥ w) := by
  simp [probeOutput, gatedValueSum_mulVec, layerGates, baseAttention, baseValue]

/-- On real probe times, the depth-one complex mixture is the complexification of
the closed probe output. -/
theorem baseProbeMixtureC_ofReal_eq_probeOutput {k d r : Nat}
    (θ : Params 1 k d) (w v : Vec d) (τ : ℝ) :
    baseProbeMixtureC r θ w v (τ : ℂ) =
      fun i : Fin d => ((probeOutput r θ w v τ i : ℝ) : ℂ) := by
  ext i
  have hsig : ∀ h : Fin k,
      csig ((τ : ℂ) * (baseSlope θ w v h : ℂ) + Complex.log (r : ℂ)) =
        ((headGate r (baseAttention θ h) w v τ : ℝ) : ℂ) := by
    intro h
    rw [← Complex.natCast_log (n := r)]
    rw [headGate]
    rw [← TransformerIdentifiability.NLayer.csig_ofReal
      (τ * matrixBilin (baseAttention θ h) w v + logScale r)]
    congr 1
    simp [baseSlope]
  simp [baseProbeMixtureC_apply, probeOutput_depth_one, hsig, baseAttention,
    baseValue, mul_comm]

/-- Positive-real equality of closed depth-one probe outputs gives
positive-real equality of the complex mixture formulas. -/
theorem baseProbeMixtureC_positive_real_eq_of_probeOutput_eq {k d r : Nat}
    {θ θ' : Params 1 k d} {w v : Vec d}
    (hEq :
      ∀ τ : ℝ, 0 < τ →
        probeOutput r θ w v τ = probeOutput r θ' w v τ) :
    ∀ τ : ℝ, 0 < τ →
      baseProbeMixtureC r θ w v (τ : ℂ) =
        baseProbeMixtureC r θ' w v (τ : ℂ) := by
  intro τ hτ
  calc
    baseProbeMixtureC r θ w v (τ : ℂ)
        = (fun i : Fin d => ((probeOutput r θ w v τ i : ℝ) : ℂ)) :=
          baseProbeMixtureC_ofReal_eq_probeOutput θ w v τ
    _ = (fun i : Fin d => ((probeOutput r θ' w v τ i : ℝ) : ℂ)) := by
          ext i
          exact congrArg (fun y : Vec d => ((y i : ℝ) : ℂ)) (hEq τ hτ)
    _ = baseProbeMixtureC r θ' w v (τ : ℂ) :=
          (baseProbeMixtureC_ofReal_eq_probeOutput θ' w v τ).symm

/-- A separated depth-one probe for a parameter: nonzero distinct slopes and
nonzero value coefficients. -/
structure BaseSeparatedProbe {k d : Nat} (θ : Params 1 k d)
    (w v : Vec d) : Prop where
  slope_ne_zero : ∀ h : Fin k, baseSlope θ w v h ≠ 0
  slope_injective : Function.Injective (baseSlope θ w v)
  coeff_ne_zero : ∀ h : Fin k, baseValue θ h *ᵥ w ≠ 0

namespace BaseSeparatedProbe

theorem slope_pairwise {k d : Nat} {θ : Params 1 k d} {w v : Vec d}
    (hsep : BaseSeparatedProbe θ w v) :
    Pairwise fun h g : Fin k => baseSlope θ w v h ≠ baseSlope θ w v g := by
  intro h g hne heq
  exact hne (hsep.slope_injective heq)

theorem coeffC_ne_zero {k d : Nat} {θ : Params 1 k d} {w v : Vec d}
    (hsep : BaseSeparatedProbe θ w v) (h : Fin k) :
    baseCoeffC θ w h ≠ 0 := by
  intro hzero
  apply hsep.coeff_ne_zero h
  ext i
  have hi : (((baseValue θ h *ᵥ w) i : ℝ) : ℂ) = 0 := by
    simpa [baseCoeffC] using congrFun hzero i
  exact Complex.ofReal_inj.mp hi

end BaseSeparatedProbe

/-- Positive-real equality of two depth-one probe mixtures transfers every pole
of a recovered primed aggregate slope into the unprimed aggregate singular set.
This is the upstream pole-transfer half of the aggregate recovery bridge. -/
theorem baseProbeMixtureC_pole_mem_mixtureSingularSet_of_positive_real_eq
    {k d r : Nat} (hr : 1 < r) {θ θ' : Params 1 k d} {w v : Vec d}
    (hEq :
      ∀ τ : ℝ, 0 < τ →
        baseProbeMixtureC r θ w v (τ : ℂ) =
          baseProbeMixtureC r θ' w v (τ : ℂ))
    {slope : ℝ}
    (hslope :
      slope ∈ slopeSupportFinset (baseCoeffC θ' w) (baseSlope θ' w v))
    {ξ : ℂ} (hξ : ξ ∈ affineSigmoidPoleSet (logScale r) slope) :
    ξ ∈ mixtureSingularSet (logScale r) (baseCoeffC θ w)
      (baseSlope θ w v) := by
  classical
  let E : Set ℂ :=
    mixtureSingularSet (logScale r) (baseCoeffC θ w) (baseSlope θ w v)
  let E' : Set ℂ :=
    mixtureSingularSet (logScale r) (baseCoeffC θ' w) (baseSlope θ' w v)
  have hb : logScale r ≠ 0 := logScale_ne_zero_of_one_lt hr
  have hslope_ne : slope ≠ 0 :=
    (mem_slopeSupportFinset_iff (baseCoeffC θ' w)
      (baseSlope θ' w v) slope).1 hslope |>.1
  have hcoeff_vec_ne :
      aggregateCoeff (baseCoeffC θ' w) (baseSlope θ' w v) slope ≠ 0 :=
    (mem_slopeSupportFinset_iff (baseCoeffC θ' w)
      (baseSlope θ' w v) slope).1 hslope |>.2
  obtain ⟨i, hcoeff_i⟩ :
      ∃ i : Fin d,
        aggregateCoeff (baseCoeffC θ' w) (baseSlope θ' w v) slope i ≠ 0 := by
    by_contra hnone
    apply hcoeff_vec_ne
    ext i
    by_contra hi
    exact hnone ⟨i, hi⟩
  have hEclosed : IsClosed E := by
    dsimp [E]
    exact mixtureSingularSet_closed (logScale r)
      (baseCoeffC θ w) (baseSlope θ w v)
  have hEcount : E.Countable := by
    dsimp [E]
    exact mixtureSingularSet_countable (logScale r)
      (baseCoeffC θ w) (baseSlope θ w v)
  have hE'count : E'.Countable := by
    dsimp [E']
    exact mixtureSingularSet_countable (logScale r)
      (baseCoeffC θ' w) (baseSlope θ' w v)
  have hFanalytic :
      AnalyticOnNhd ℂ (fun τ : ℂ => baseProbeMixtureC r θ w v τ i) Eᶜ := by
    dsimp [E]
    exact baseProbeMixtureC_coord_analyticOnNhd_compl θ w v i
  have hGanalytic :
      AnalyticOnNhd ℂ (fun τ : ℂ => baseProbeMixtureC r θ' w v τ i) E'ᶜ := by
    dsimp [E']
    exact baseProbeMixtureC_coord_analyticOnNhd_compl θ' w v i
  have hz0 : ((1 : ℝ) : ℂ) ∈ (E ∪ E')ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_union]
    intro hmem
    rcases hmem with hmem | hmem
    · exact ofReal_notMem_mixtureSingularSet (logScale r) 1
        (baseCoeffC θ w) (baseSlope θ w v) (by simpa [E] using hmem)
    · exact ofReal_notMem_mixtureSingularSet (logScale r) 1
        (baseCoeffC θ' w) (baseSlope θ' w v) (by simpa [E'] using hmem)
  have hE'closedDiscrete :
      ClosedDiscreteIn E' Set.univ := by
    dsimp [E']
    exact mixtureSingularSet_closedDiscrete (logScale r)
      (baseCoeffC θ' w) (baseSlope θ' w v)
  have hGisol : IsPuncturedIsolated E' ξ :=
    eventually_notMem_of_not_mem_acc
      (hE'closedDiscrete.noAccum ξ (by simp))
  have hH' :
      ∀ j : Fin d,
        AnalyticAt ℂ
          (fun τ : ℂ => (fun _ : ℂ => baseEntirePartC θ' v) τ j) ξ := by
    intro j
    simpa using
      (analyticAt_const :
        AnalyticAt ℂ (fun _ : ℂ => baseEntirePartC θ' v j) ξ)
  have hGblow :
      BlowsUpAt (fun τ : ℂ => baseProbeMixtureC r θ' w v τ i) ξ := by
    simpa [baseProbeMixtureC] using
      (sigmoidMixture_coord_blowsUpAt_of_aggregate_ne
        (b := logScale r) (slope := slope) (ξ := ξ)
        (H := fun _ : ℂ => baseEntirePartC θ' v)
        (M := baseCoeffC θ' w) (lam := baseSlope θ' w v)
        hb hslope_ne hξ hH' hcoeff_i)
  have hpole : ξ ∈ E :=
    lem_pole_transfer_of_real_tail_eq
      (E_F := E) (E_G := E')
      (F := fun τ : ℂ => baseProbeMixtureC r θ w v τ i)
      (G := fun τ : ℂ => baseProbeMixtureC r θ' w v τ i)
      (T0 := 0) (x0 := 1) (τ := ξ)
      hEclosed hEcount hE'count hFanalytic hGanalytic
      (by norm_num : (0 : ℝ) < 1) hz0
      (by
        intro t ht
        exact congrFun (hEq t ht) i)
      (by
        intro hξE
        dsimp [E] at hξE
        exact baseProbeMixtureC_coord_continuousAt_of_notMem_mixtureSingularSet
          θ w v i hξE)
      hGisol hGblow
  simpa [E] using hpole

/-- Positive-real equality of depth-one probe mixtures recovers equality of the
finite aggregate slope supports.  Coefficients on that support still require the
missing residue-comparison direction from `K04B`. -/
theorem base_slopeSupportFinset_subset_of_positive_real_eq
    {k d r : Nat} (hr : 1 < r) {θ θ' : Params 1 k d} {w v : Vec d}
    (hEq :
      ∀ τ : ℝ, 0 < τ →
        baseProbeMixtureC r θ w v (τ : ℂ) =
          baseProbeMixtureC r θ' w v (τ : ℂ)) :
    slopeSupportFinset (baseCoeffC θ' w) (baseSlope θ' w v) ⊆
      slopeSupportFinset (baseCoeffC θ w) (baseSlope θ w v) := by
  classical
  intro slope hslope
  let ξ : ℂ := affineSigmoidPole (logScale r) slope 0
  have hξ : ξ ∈ affineSigmoidPoleSet (logScale r) slope := ⟨0, rfl⟩
  have hpole :
      ξ ∈ mixtureSingularSet (logScale r) (baseCoeffC θ w)
        (baseSlope θ w v) :=
    baseProbeMixtureC_pole_mem_mixtureSingularSet_of_positive_real_eq
      (r := r) hr hEq hslope hξ
  rw [mixtureSingularSet] at hpole
  simp only [Set.mem_iUnion, exists_prop] at hpole
  rcases hpole with ⟨mu, hmu_supp, hξmu⟩
  have hb : logScale r ≠ 0 := logScale_ne_zero_of_one_lt hr
  have hslope_ne : slope ≠ 0 :=
    (mem_slopeSupportFinset_iff (baseCoeffC θ' w)
      (baseSlope θ' w v) slope).1 hslope |>.1
  have hmu_ne : mu ≠ 0 :=
    (mem_slopeSupportFinset_iff (baseCoeffC θ w)
      (baseSlope θ w v) mu).1 hmu_supp |>.1
  have hmu_eq : mu = slope := by
    by_contra hne
    have hneq : slope ≠ mu := by
      intro hsmu
      exact hne hsmu.symm
    have hinter :
        affineSigmoidPoleSet (logScale r) slope ∩
            affineSigmoidPoleSet (logScale r) mu = ∅ :=
      affineSigmoidPoleSet_inter_eq_empty_of_ne
        (b := logScale r) (lam := slope) (mu := mu)
        hb hslope_ne hmu_ne hneq
    have hboth :
        ξ ∈ affineSigmoidPoleSet (logScale r) slope ∩
          affineSigmoidPoleSet (logScale r) mu := ⟨hξ, hξmu⟩
    rw [hinter] at hboth
    exact hboth
  simpa [hmu_eq] using hmu_supp

/-- Symmetric form of `base_slopeSupportFinset_subset_of_positive_real_eq`. -/
theorem base_slopeSupportFinset_eq_of_positive_real_eq
    {k d r : Nat} (hr : 1 < r) {θ θ' : Params 1 k d} {w v : Vec d}
    (hEq :
      ∀ τ : ℝ, 0 < τ →
        baseProbeMixtureC r θ w v (τ : ℂ) =
          baseProbeMixtureC r θ' w v (τ : ℂ)) :
    slopeSupportFinset (baseCoeffC θ w) (baseSlope θ w v) =
      slopeSupportFinset (baseCoeffC θ' w) (baseSlope θ' w v) := by
  ext slope
  constructor
  · intro hslope
    exact base_slopeSupportFinset_subset_of_positive_real_eq
      (θ := θ') (θ' := θ) hr
      (fun τ hτ => (hEq τ hτ).symm) hslope
  · intro hslope
    exact base_slopeSupportFinset_subset_of_positive_real_eq
      (θ := θ) (θ' := θ') hr hEq hslope

/-- Positive-real equality of depth-one probe mixtures identifies the aggregate
coefficient at every nonzero slope. -/
theorem base_aggregateCoeff_eq_of_positive_real_eq
    {k d r : Nat} (hr : 1 < r) {θ θ' : Params 1 k d} {w v : Vec d}
    (hEq :
      ∀ τ : ℝ, 0 < τ →
        baseProbeMixtureC r θ w v (τ : ℂ) =
          baseProbeMixtureC r θ' w v (τ : ℂ)) :
    ∀ slope : ℝ, slope ≠ 0 →
      aggregateCoeff (baseCoeffC θ w) (baseSlope θ w v) slope =
        aggregateCoeff (baseCoeffC θ' w) (baseSlope θ' w v) slope := by
  have hsupp :
      slopeSupportFinset (baseCoeffC θ w) (baseSlope θ w v) =
        slopeSupportFinset (baseCoeffC θ' w) (baseSlope θ' w v) :=
    base_slopeSupportFinset_eq_of_positive_real_eq (r := r) hr hEq
  exact aggregateCoeff_eq_of_sigmoidMixture_real_tail_eq_of_slopeSupportFinset_eq
    (b := logScale r) (T0 := (0 : ℝ))
    (H := fun _ : ℂ => baseEntirePartC θ v)
    (H' := fun _ : ℂ => baseEntirePartC θ' v)
    (M := baseCoeffC θ w) (lam := baseSlope θ w v)
    (M' := baseCoeffC θ' w) (lam' := baseSlope θ' w v)
    (logScale_ne_zero_of_one_lt hr)
    (by
      intro j τ
      simpa using
        (analyticAt_const :
          AnalyticAt ℂ (fun _ : ℂ => baseEntirePartC θ v j) τ))
    (by
      intro j τ
      simpa using
        (analyticAt_const :
          AnalyticAt ℂ (fun _ : ℂ => baseEntirePartC θ' v j) τ))
    (by
      intro t ht
      simpa [baseProbeMixtureC] using hEq t ht)
    hsupp

/-- Separated probes instantiate the aggregate-recovery support statement from
`K04B` for the depth-one observable. -/
theorem base_separated_mixture_recovery {k d r : Nat}
    {θ : Params 1 k d} {w v : Vec d}
    (hsep : BaseSeparatedProbe θ w v) :
    slopeSupportFinset (baseCoeffC θ w) (baseSlope θ w v) =
        Finset.univ.image (baseSlope θ w v) ∧
      (∀ h : Fin k,
        aggregateCoeff (baseCoeffC θ w) (baseSlope θ w v)
            (baseSlope θ w v h) =
          baseCoeffC θ w h) ∧
      mixtureSingularSet (logScale r) (baseCoeffC θ w) (baseSlope θ w v) =
        ⋃ h : Fin k, affineSigmoidPoleSet (logScale r) (baseSlope θ w v h) := by
  exact lem_explicit_sigmoid_mixture_recovery (logScale r)
    (M := baseCoeffC θ w) (lam := baseSlope θ w v)
    hsep.slope_pairwise hsep.slope_ne_zero hsep.coeffC_ne_zero

/-- Support-only aggregate recovery on a dense separated probe set.  This is the
part of finite-support aggregate recovery produced by pole transfer from
positive-real equality; coefficient equality on the recovered support is the
remaining residue-comparison input. -/
structure BaseAggregateSupportRecoveryData {k d : Nat}
    (θ θ' : Params 1 k d) where
  U : Set (ProbePoint d)
  zariski_dense : ProbeZariskiDense U
  target_separated : ∀ x : ProbePoint d, x ∈ U →
    BaseSeparatedProbe θ' x.1 x.2
  support_eq_on :
    ∀ x : ProbePoint d, x ∈ U →
      slopeSupportFinset (baseCoeffC θ x.1) (baseSlope θ x.1 x.2) =
        slopeSupportFinset (baseCoeffC θ' x.1) (baseSlope θ' x.1 x.2)

/-- Support recovery together with the nonempty open probe subset used later by
the value-recovery slice.  This support-only package intentionally stops before
the missing residue coefficient comparison. -/
structure BaseAggregateSupportRecoveryOpenProbeData {k d : Nat}
    (θ θ' : Params 1 k d) where
  support : BaseAggregateSupportRecoveryData θ θ'
  Ω : Set (ProbePoint d)
  omega_open : IsOpen Ω
  omega_nonempty : Ω.Nonempty
  omega_subset : Ω ⊆ support.U

namespace BaseAggregateSupportRecoveryData

/-- Package support recovery with an already chosen nonempty Euclidean-open
probe subset, matching the shape of the downstream open-probe workflow without
asserting coefficient recovery. -/
def with_open_probe_set {k d : Nat} {θ θ' : Params 1 k d}
    (D : BaseAggregateSupportRecoveryData θ θ')
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω)
    (hΩ_nonempty : Ω.Nonempty) (hΩ_subset : Ω ⊆ D.U) :
    BaseAggregateSupportRecoveryOpenProbeData θ θ' where
  support := D
  Ω := Ω
  omega_open := hΩ_open
  omega_nonempty := hΩ_nonempty
  omega_subset := hΩ_subset

end BaseAggregateSupportRecoveryData

namespace BaseAggregateSupportRecoveryOpenProbeData

/-- The separated-probe field is available on the packaged open probe subset. -/
theorem target_separated_on_open {k d : Nat} {θ θ' : Params 1 k d}
    (D : BaseAggregateSupportRecoveryOpenProbeData θ θ') :
    ∀ x : ProbePoint d, x ∈ D.Ω → BaseSeparatedProbe θ' x.1 x.2 := by
  intro x hx
  exact D.support.target_separated x (D.omega_subset hx)

/-- Support equality is available on the packaged open probe subset. -/
theorem support_eq_on_open {k d : Nat} {θ θ' : Params 1 k d}
    (D : BaseAggregateSupportRecoveryOpenProbeData θ θ') :
    ∀ x : ProbePoint d, x ∈ D.Ω →
      slopeSupportFinset (baseCoeffC θ x.1) (baseSlope θ x.1 x.2) =
        slopeSupportFinset (baseCoeffC θ' x.1) (baseSlope θ' x.1 x.2) := by
  intro x hx
  exact D.support.support_eq_on x (D.omega_subset hx)

end BaseAggregateSupportRecoveryOpenProbeData

/-- Positive-real equality of the depth-one complex probe mixtures on a dense
separated probe set. -/
structure BasePositiveRealProbeMixtureEqualityData {k d : Nat} (r : Nat)
    (θ θ' : Params 1 k d) where
  U : Set (ProbePoint d)
  zariski_dense : ProbeZariskiDense U
  target_separated : ∀ x : ProbePoint d, x ∈ U →
    BaseSeparatedProbe θ' x.1 x.2
  positive_real_eq_on :
    ∀ x : ProbePoint d, x ∈ U → ∀ τ : ℝ, 0 < τ →
      baseProbeMixtureC r θ x.1 x.2 (τ : ℂ) =
        baseProbeMixtureC r θ' x.1 x.2 (τ : ℂ)

namespace BasePositiveRealProbeMixtureEqualityData

/-- Pole transfer turns positive-real probe-mixture equality into equality of
aggregate slope supports on every recovered probe. -/
def to_support_recovery {k d r : Nat} {θ θ' : Params 1 k d}
    (D : BasePositiveRealProbeMixtureEqualityData r θ θ') (hr : 1 < r) :
    BaseAggregateSupportRecoveryData θ θ' where
  U := D.U
  zariski_dense := D.zariski_dense
  target_separated := D.target_separated
  support_eq_on := by
    intro x hx
    exact base_slopeSupportFinset_eq_of_positive_real_eq
      (r := r) hr (D.positive_real_eq_on x hx)

/-- Positive-real mixture equality, plus an open probe subset of the dense
domain, packages directly as support recovery on the open-probe workflow. -/
def to_support_recovery_open_probe_set {k d r : Nat} {θ θ' : Params 1 k d}
    (D : BasePositiveRealProbeMixtureEqualityData r θ θ') (hr : 1 < r)
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω)
    (hΩ_nonempty : Ω.Nonempty) (hΩ_subset : Ω ⊆ D.U) :
    BaseAggregateSupportRecoveryOpenProbeData θ θ' :=
  (D.to_support_recovery hr).with_open_probe_set hΩ_open hΩ_nonempty hΩ_subset

end BasePositiveRealProbeMixtureEqualityData

/-- Positive-real equality of closed depth-one probe outputs on a dense
separated probe set. -/
structure BasePositiveRealProbeOutputEqualityData {k d : Nat} (r : Nat)
    (θ θ' : Params 1 k d) where
  U : Set (ProbePoint d)
  zariski_dense : ProbeZariskiDense U
  target_separated : ∀ x : ProbePoint d, x ∈ U →
    BaseSeparatedProbe θ' x.1 x.2
  positive_real_probeOutput_eq_on :
    ∀ x : ProbePoint d, x ∈ U → ∀ τ : ℝ, 0 < τ →
      probeOutput r θ x.1 x.2 τ = probeOutput r θ' x.1 x.2 τ

namespace BasePositiveRealProbeOutputEqualityData

/-- Closed probe-output equality on positive real probe times compiles to
positive-real equality of the complex depth-one mixture formulas. -/
def to_mixture_equality {k d r : Nat} {θ θ' : Params 1 k d}
    (D : BasePositiveRealProbeOutputEqualityData r θ θ') :
    BasePositiveRealProbeMixtureEqualityData r θ θ' where
  U := D.U
  zariski_dense := D.zariski_dense
  target_separated := D.target_separated
  positive_real_eq_on := by
    intro x hx
    exact baseProbeMixtureC_positive_real_eq_of_probeOutput_eq
      (D.positive_real_probeOutput_eq_on x hx)

/-- Positive-real probe-output equality gives the support-only aggregate
recovery package by first complexifying to mixture equality. -/
def to_support_recovery {k d r : Nat} {θ θ' : Params 1 k d}
    (D : BasePositiveRealProbeOutputEqualityData r θ θ') (hr : 1 < r) :
    BaseAggregateSupportRecoveryData θ θ' :=
  D.to_mixture_equality.to_support_recovery hr

/-- Positive-real probe-output equality, plus an open probe subset of the dense
domain, packages directly as support recovery on the open-probe workflow. -/
def to_support_recovery_open_probe_set {k d r : Nat} {θ θ' : Params 1 k d}
    (D : BasePositiveRealProbeOutputEqualityData r θ θ') (hr : 1 < r)
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω)
    (hΩ_nonempty : Ω.Nonempty) (hΩ_subset : Ω ⊆ D.U) :
    BaseAggregateSupportRecoveryOpenProbeData θ θ' :=
  (D.to_support_recovery hr).with_open_probe_set hΩ_open hΩ_nonempty hΩ_subset

end BasePositiveRealProbeOutputEqualityData

/-- Probe-wise aggregate matching produced by the meromorphic residue comparison.
The primed probes are separated; the unprimed side is still allowed to have
collisions before the counting argument below forces singleton aggregates. -/
structure BaseAggregateRecoveryData {k d : Nat}
    (θ θ' : Params 1 k d) where
  U : Set (ProbePoint d)
  zariski_dense : ProbeZariskiDense U
  target_separated : ∀ x : ProbePoint d, x ∈ U →
    BaseSeparatedProbe θ' x.1 x.2
  aggregate_eq_on :
    ∀ x : ProbePoint d, x ∈ U → ∀ slope : ℝ, slope ≠ 0 →
      aggregateCoeff (baseCoeffC θ x.1) (baseSlope θ x.1 x.2) slope =
        aggregateCoeff (baseCoeffC θ' x.1) (baseSlope θ' x.1 x.2) slope

/-- A finite-support aggregate recovery statement is enough to recover aggregate
coefficients at every nonzero slope.  This is the form returned by the current
`K04B` API: the support of nonzero aggregate slopes and the coefficient attached
to each recovered support point. -/
theorem aggregateCoeff_eq_of_support_eq_of_eq_on_support {p q N : Nat}
    {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    {M' : Fin q → Fin N → ℂ} {lam' : Fin q → ℝ}
    (hsupp : slopeSupportFinset M lam = slopeSupportFinset M' lam')
    (hcoeff :
      ∀ slope : ℝ, slope ∈ slopeSupportFinset M' lam' →
        aggregateCoeff M lam slope = aggregateCoeff M' lam' slope) :
    ∀ slope : ℝ, slope ≠ 0 →
      aggregateCoeff M lam slope = aggregateCoeff M' lam' slope := by
  intro slope hslope
  by_cases hmem' : slope ∈ slopeSupportFinset M' lam'
  · exact hcoeff slope hmem'
  · have hmem : slope ∉ slopeSupportFinset M lam := by
      intro hmem
      exact hmem' (by simpa [hsupp] using hmem)
    have hM : aggregateCoeff M lam slope = 0 := by
      by_contra hne
      exact hmem ((mem_slopeSupportFinset_iff M lam slope).2 ⟨hslope, hne⟩)
    have hM' : aggregateCoeff M' lam' slope = 0 := by
      by_contra hne
      exact hmem' ((mem_slopeSupportFinset_iff M' lam' slope).2 ⟨hslope, hne⟩)
    rw [hM, hM']

/-- The finite-support aggregate map produced by the mixture residue recovery on
a dense separated probe set.  Compared with `BaseAggregateRecoveryData`, this
stores only equality on the recovered finite support; vanishing away from the
support is derived by `aggregateCoeff_eq_of_support_eq_of_eq_on_support`. -/
structure BaseAggregateFiniteSupportRecoveryData {k d : Nat}
    (θ θ' : Params 1 k d) where
  U : Set (ProbePoint d)
  zariski_dense : ProbeZariskiDense U
  target_separated : ∀ x : ProbePoint d, x ∈ U →
    BaseSeparatedProbe θ' x.1 x.2
  support_eq_on :
    ∀ x : ProbePoint d, x ∈ U →
      slopeSupportFinset (baseCoeffC θ x.1) (baseSlope θ x.1 x.2) =
        slopeSupportFinset (baseCoeffC θ' x.1) (baseSlope θ' x.1 x.2)
  aggregate_eq_on_support :
    ∀ x : ProbePoint d, x ∈ U → ∀ slope : ℝ,
      slope ∈
          slopeSupportFinset (baseCoeffC θ' x.1) (baseSlope θ' x.1 x.2) →
        aggregateCoeff (baseCoeffC θ x.1) (baseSlope θ x.1 x.2) slope =
          aggregateCoeff (baseCoeffC θ' x.1) (baseSlope θ' x.1 x.2) slope

namespace BaseAggregateFiniteSupportRecoveryData

/-- Finite-support aggregate recovery extends to equality of aggregate
coefficients at every nonzero slope. -/
theorem aggregate_eq_on {k d : Nat} {θ θ' : Params 1 k d}
    (D : BaseAggregateFiniteSupportRecoveryData θ θ') :
    ∀ x : ProbePoint d, x ∈ D.U → ∀ slope : ℝ, slope ≠ 0 →
      aggregateCoeff (baseCoeffC θ x.1) (baseSlope θ x.1 x.2) slope =
        aggregateCoeff (baseCoeffC θ' x.1) (baseSlope θ' x.1 x.2) slope := by
  intro x hx
  exact aggregateCoeff_eq_of_support_eq_of_eq_on_support
    (M := baseCoeffC θ x.1) (lam := baseSlope θ x.1 x.2)
    (M' := baseCoeffC θ' x.1) (lam' := baseSlope θ' x.1 x.2)
    (D.support_eq_on x hx) (D.aggregate_eq_on_support x hx)

/-- Compile the finite-support aggregate map recovered by `K04B` into the
aggregate coefficient package consumed by the base-case finite counting step. -/
def to_aggregate_recovery {k d : Nat} {θ θ' : Params 1 k d}
    (D : BaseAggregateFiniteSupportRecoveryData θ θ') :
    BaseAggregateRecoveryData θ θ' where
  U := D.U
  zariski_dense := D.zariski_dense
  target_separated := D.target_separated
  aggregate_eq_on := D.aggregate_eq_on

end BaseAggregateFiniteSupportRecoveryData

namespace BasePositiveRealProbeMixtureEqualityData

/-- Positive-real mixture equality gives full aggregate coefficient recovery by
combining support recovery with the aggregate residue comparison. -/
def to_aggregate_recovery {k d r : Nat} {θ θ' : Params 1 k d}
    (D : BasePositiveRealProbeMixtureEqualityData r θ θ') (hr : 1 < r) :
    BaseAggregateRecoveryData θ θ' where
  U := D.U
  zariski_dense := D.zariski_dense
  target_separated := D.target_separated
  aggregate_eq_on := by
    intro x hx
    exact base_aggregateCoeff_eq_of_positive_real_eq
      (r := r) (θ := θ) (θ' := θ') (w := x.1) (v := x.2)
      hr (D.positive_real_eq_on x hx)

/-- Positive-real mixture equality also fills the finite-support aggregate
package expected by TeX-facing base-case wrappers. -/
def to_finite_support_recovery {k d r : Nat} {θ θ' : Params 1 k d}
    (D : BasePositiveRealProbeMixtureEqualityData r θ θ') (hr : 1 < r) :
    BaseAggregateFiniteSupportRecoveryData θ θ' where
  U := D.U
  zariski_dense := D.zariski_dense
  target_separated := D.target_separated
  support_eq_on := by
    intro x hx
    exact base_slopeSupportFinset_eq_of_positive_real_eq
      (r := r) (θ := θ) (θ' := θ') (w := x.1) (v := x.2)
      hr (D.positive_real_eq_on x hx)
  aggregate_eq_on_support := by
    intro x hx slope hslope
    have hslope_ne : slope ≠ 0 :=
      (mem_slopeSupportFinset_iff (baseCoeffC θ' x.1)
        (baseSlope θ' x.1 x.2) slope).1 hslope |>.1
    exact base_aggregateCoeff_eq_of_positive_real_eq
      (r := r) (θ := θ) (θ' := θ') (w := x.1) (v := x.2)
      hr (D.positive_real_eq_on x hx) slope hslope_ne

end BasePositiveRealProbeMixtureEqualityData

namespace BasePositiveRealProbeOutputEqualityData

/-- Positive-real closed probe-output equality gives full aggregate coefficient
recovery after complexifying the depth-one probe formula. -/
def to_aggregate_recovery {k d r : Nat} {θ θ' : Params 1 k d}
    (D : BasePositiveRealProbeOutputEqualityData r θ θ') (hr : 1 < r) :
    BaseAggregateRecoveryData θ θ' :=
  D.to_mixture_equality.to_aggregate_recovery hr

/-- Positive-real closed probe-output equality fills the finite-support
aggregate package after complexifying the depth-one probe formula. -/
def to_finite_support_recovery {k d r : Nat} {θ θ' : Params 1 k d}
    (D : BasePositiveRealProbeOutputEqualityData r θ θ') (hr : 1 < r) :
    BaseAggregateFiniteSupportRecoveryData θ θ' :=
  D.to_mixture_equality.to_finite_support_recovery hr

end BasePositiveRealProbeOutputEqualityData

/-- Paired slope/coefficient recovery on a dense separated probe set.  This is the
output of the residue step after aggregate supports have been matched and the
`k` primed separated slopes force unprimed aggregates to be singletons. -/
structure BasePairedProbeRecoveryData {k d : Nat}
    (θ θ' : Params 1 k d) where
  U : Set (ProbePoint d)
  zariski_dense : ProbeZariskiDense U
  paired_on :
    ∀ x : ProbePoint d, x ∈ U →
      ∃ σ : Equiv.Perm (Fin k), ∀ h : Fin k,
        baseSlope θ x.1 x.2 (σ h) = baseSlope θ' x.1 x.2 h ∧
          baseCoeffC θ x.1 (σ h) = baseCoeffC θ' x.1 h

/-- The finite counting step in the base-case residue argument: aggregate equality
against a separated primed `k`-head probe forces each recovered primed aggregate to
come from a unique unprimed head, and carries the coefficient with the same head. -/
theorem paired_recovery_of_aggregateCoeff_eq {k d : Nat}
    {θ θ' : Params 1 k d} {w v : Vec d}
    (hsep' : BaseSeparatedProbe θ' w v)
    (hagg :
      ∀ slope : ℝ, slope ≠ 0 →
        aggregateCoeff (baseCoeffC θ w) (baseSlope θ w v) slope =
          aggregateCoeff (baseCoeffC θ' w) (baseSlope θ' w v) slope) :
    ∃ σ : Equiv.Perm (Fin k), ∀ h : Fin k,
      baseSlope θ w v (σ h) = baseSlope θ' w v h ∧
        baseCoeffC θ w (σ h) = baseCoeffC θ' w h := by
  classical
  let lam : Fin k → ℝ := baseSlope θ w v
  let lam' : Fin k → ℝ := baseSlope θ' w v
  let M : Fin k → Fin d → ℂ := baseCoeffC θ w
  let M' : Fin k → Fin d → ℂ := baseCoeffC θ' w
  have hsupp_eq :
      slopeSupportFinset M lam = slopeSupportFinset M' lam' :=
    slopeSupportFinset_eq_of_aggregateCoeff_eq (M := M) (lam := lam)
      (M' := M') (lam' := lam') hagg
  have hprimed_supp : slopeSupportFinset M' lam' = Finset.univ.image lam' :=
    slopeSupportFinset_eq_image_of_pairwise_nonzero
      (M := M') (lam := lam') hsep'.slope_pairwise hsep'.slope_ne_zero
      hsep'.coeffC_ne_zero
  have hExists : ∀ h : Fin k, ∃ c : Fin k, lam c = lam' h := by
    intro h
    have hmem_prime : lam' h ∈ slopeSupportFinset M' lam' := by
      rw [hprimed_supp]
      exact Finset.mem_image.mpr ⟨h, Finset.mem_univ h, rfl⟩
    have hmem_un : lam' h ∈ slopeSupportFinset M lam := by
      simpa [hsupp_eq] using hmem_prime
    have hmem_filter :
        lam' h ∈ (Finset.univ.image lam).filter
          (fun slope => slope ≠ 0 ∧ aggregateCoeff M lam slope ≠ 0) := by
      simpa [slopeSupportFinset] using hmem_un
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hmem_filter).1 with
      ⟨c, _hc, hc⟩
    exact ⟨c, hc⟩
  let σfun : Fin k → Fin k := fun h => Classical.choose (hExists h)
  have hσfun : ∀ h : Fin k, lam (σfun h) = lam' h := fun h =>
    Classical.choose_spec (hExists h)
  have hσinj : Function.Injective σfun := by
    intro h g hhg
    apply hsep'.slope_injective
    calc
      lam' h = lam (σfun h) := (hσfun h).symm
      _ = lam (σfun g) := by rw [hhg]
      _ = lam' g := hσfun g
  have hσbij : Function.Bijective σfun :=
    hσinj.bijective_of_finite
  let σ : Equiv.Perm (Fin k) := Equiv.ofBijective σfun hσbij
  have hlam_inj : Function.Injective lam := by
    intro c d hcd
    rcases hσbij.2 c with ⟨h, hh⟩
    rcases hσbij.2 d with ⟨g, hg⟩
    have hprime_eq : lam' h = lam' g := by
      calc
        lam' h = lam (σfun h) := (hσfun h).symm
        _ = lam c := by rw [hh]
        _ = lam d := hcd
        _ = lam (σfun g) := by rw [hg]
        _ = lam' g := hσfun g
    have hhg : h = g := hsep'.slope_injective hprime_eq
    calc
      c = σfun h := hh.symm
      _ = σfun g := by rw [hhg]
      _ = d := hg
  have hlam_pairwise : Pairwise fun i j : Fin k => lam i ≠ lam j := by
    intro i j hij heq
    exact hij (hlam_inj heq)
  refine ⟨σ, ?_⟩
  intro h
  change lam (σfun h) = lam' h ∧ M (σfun h) = M' h
  refine ⟨hσfun h, ?_⟩
  calc
    M (σfun h) = aggregateCoeff M lam (lam (σfun h)) :=
      (aggregateCoeff_eq_single_of_pairwise (M := M) (lam := lam)
        hlam_pairwise (σfun h)).symm
    _ = aggregateCoeff M lam (lam' h) := by rw [hσfun h]
    _ = aggregateCoeff M' lam' (lam' h) := hagg (lam' h) (hsep'.slope_ne_zero h)
    _ = M' h :=
      aggregateCoeff_eq_single_of_pairwise (M := M') (lam := lam')
        hsep'.slope_pairwise h

namespace BaseAggregateRecoveryData

/-- Aggregate residue matching on a dense separated set compiles to paired
probe-wise recovery. -/
def paired_recovery {k d : Nat} {θ θ' : Params 1 k d}
    (D : BaseAggregateRecoveryData θ θ') :
    BasePairedProbeRecoveryData θ θ' where
  U := D.U
  zariski_dense := D.zariski_dense
  paired_on := by
    intro x hx
    exact paired_recovery_of_aggregateCoeff_eq
      (D.target_separated x hx) (D.aggregate_eq_on x hx)

end BaseAggregateRecoveryData

namespace BaseAggregateFiniteSupportRecoveryData

/-- The finite-support aggregate package is sufficient for paired probe-wise
recovery via the aggregate coefficient package. -/
def paired_recovery {k d : Nat} {θ θ' : Params 1 k d}
    (D : BaseAggregateFiniteSupportRecoveryData θ θ') :
    BasePairedProbeRecoveryData θ θ' :=
  D.to_aggregate_recovery.paired_recovery

end BaseAggregateFiniteSupportRecoveryData

/-- Regularity makes the primed depth-one attention family injective. -/
theorem baseAttention_injective_of_regular {k d r : Nat}
    {θ : Params 1 k d} (hθ : Regularity r θ) :
    Function.Injective (baseAttention θ) := by
  intro h g heq
  by_contra hne
  exact (hθ.headAttention_ne 0 hne) (by simpa [baseAttention] using heq)

/-- Linear maps represented by finite matrices are equal when they agree on every
vector. -/
theorem matrix_eq_of_forall_mulVec_eq_khead {d : Nat}
    {M N : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ x : Vec d, M *ᵥ x = N *ᵥ x) :
    M = N := by
  ext i j
  have hij := congrFun (h (Pi.single j (1 : ℝ))) i
  have hM : (M *ᵥ Pi.single j (1 : ℝ)) i = M i j :=
    congrFun (Matrix.mulVec_single_one M j) i
  have hN : (N *ᵥ Pi.single j (1 : ℝ)) i = N i j :=
    congrFun (Matrix.mulVec_single_one N j) i
  exact hM.symm.trans (hij.trans hN)

/-- If two finite-dimensional linear maps represented by matrices agree on a
nonempty Euclidean open set of vectors, they agree on every vector. -/
theorem matrix_mulVec_eq_of_eq_on_nonempty_open_khead {d : Nat}
    {M N : Matrix (Fin d) (Fin d) ℝ} {W : Set (Vec d)}
    (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    (hW_eq : ∀ w : Vec d, w ∈ W → M *ᵥ w = N *ᵥ w) :
    ∀ w : Vec d, M *ᵥ w = N *ᵥ w := by
  classical
  rcases hW_nonempty with ⟨w0, hw0⟩
  rcases (Metric.isOpen_iff.mp hW_open w0 hw0) with ⟨ε, hεpos, hball⟩
  have hw0eq : M *ᵥ w0 = N *ᵥ w0 := hW_eq w0 hw0
  intro x
  let a : ℝ := ε / (2 * (‖x‖ + 1))
  have hdenpos : 0 < 2 * (‖x‖ + 1) := by
    nlinarith [norm_nonneg x]
  have ha_pos : 0 < a := div_pos hεpos hdenpos
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hnorm_lt : ‖a • x‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha_pos]
    have hxden : ‖x‖ < 2 * (‖x‖ + 1) := by
      nlinarith [norm_nonneg x]
    calc
      a * ‖x‖ = ε * ‖x‖ / (2 * (‖x‖ + 1)) := by
        rw [show a = ε / (2 * (‖x‖ + 1)) by rfl]
        ring
      _ < ε := by
        rw [div_lt_iff₀ hdenpos]
        exact mul_lt_mul_of_pos_left hxden hεpos
  have hax_mem : w0 + a • x ∈ W := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : w0 + a • x - w0 = a • x := by
      ext i
      simp
    simpa [hsub] using hnorm_lt
  have hshift : M *ᵥ (w0 + a • x) = N *ᵥ (w0 + a • x) :=
    hW_eq (w0 + a • x) hax_mem
  have hshift' :
      M *ᵥ w0 + a • (M *ᵥ x) = N *ᵥ w0 + a • (N *ᵥ x) := by
    simpa [Matrix.mulVec_add, Matrix.mulVec_smul] using hshift
  ext i
  have hs := congrFun hshift' i
  have h0 := congrFun hw0eq i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs
  have hmul : a * ((M *ᵥ x) i - (N *ᵥ x) i) = 0 := by
    nlinarith
  have hdiff : (M *ᵥ x) i - (N *ᵥ x) i = 0 :=
    (mul_eq_zero.mp hmul).resolve_left ha_ne
  exact sub_eq_zero.mp hdiff

/-- A nonempty open probe set contains a nonempty open slice in the `w`
coordinate through any chosen probe.  This is the Euclidean projection step used
at the end of the TeX base case, stated in the concrete product topology needed
by value recovery. -/
theorem exists_open_w_slice_subset_of_open_probe_set {d : Nat}
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω) {x0 : ProbePoint d}
    (hx0 : x0 ∈ Ω) :
    ∃ W : Set (Vec d),
      IsOpen W ∧ W.Nonempty ∧ x0.1 ∈ W ∧
        ∀ w : Vec d, w ∈ W → (w, x0.2) ∈ Ω := by
  rcases x0 with ⟨w0, v0⟩
  rcases (Metric.isOpen_iff.mp hΩ_open (w0, v0) hx0) with
    ⟨ε, hεpos, hball⟩
  refine ⟨Metric.ball w0 ε, Metric.isOpen_ball,
    ⟨w0, Metric.mem_ball_self hεpos⟩, Metric.mem_ball_self hεpos, ?_⟩
  intro w hw
  apply hball
  rw [Metric.mem_ball] at hw ⊢
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨hw, by simpa using hεpos⟩

/-- Product equality on a Zariski-dense separated probe set, in the form produced
after aggregate recovery in the TeX base-case proof. -/
structure BaseProductIdentityData {k d : Nat}
    (θ θ' : Params 1 k d) where
  U : Set (ProbePoint d)
  zariski_dense : ProbeZariskiDense U
  product_eq_on :
    ∀ x : ProbePoint d, x ∈ U → ∀ t : ℝ,
      ∏ h : Fin k, (t - baseSlope θ x.1 x.2 h) =
        ∏ h : Fin k, (t - baseSlope θ' x.1 x.2 h)

namespace BaseProductIdentityData

/-- Zariski density pushes the separated-probe product identity to all probes. -/
theorem product_identity {k d : Nat} {θ θ' : Params 1 k d}
    (D : BaseProductIdentityData θ θ') :
    ∀ (t : ℝ) (w v : Vec d),
      ∏ h : Fin k, (t - baseSlope θ w v h) =
        ∏ h : Fin k, (t - baseSlope θ' w v h) := by
  have hid :=
    attention_product_identity_of_probeZariskiDense
      (baseAttention θ) (baseAttention θ') D.U D.zariski_dense
      (by
        intro x hx t
        simpa [baseSlope, matrixBilin] using D.product_eq_on x hx t)
  intro t w v
  simpa [baseSlope, matrixBilin] using hid t w v

/-- The algebraic globalization step extracts the unique attention permutation. -/
theorem attention_permutation {k d r : Nat} {θ θ' : Params 1 k d}
    (D : BaseProductIdentityData θ θ') (hθ' : Regularity r θ') :
    ∃! σ : Equiv.Perm (Fin k),
      ∀ h : Fin k, baseAttention θ (σ h) = baseAttention θ' h := by
  exact unique_attention_permutation (baseAttention θ) (baseAttention θ')
    (baseAttention_injective_of_regular hθ')
    (by
      intro t w v
      simpa [baseSlope, matrixBilin] using D.product_identity t w v)

end BaseProductIdentityData

/-- Value-recovery obligation after the attention permutation has been fixed.
The TeX proof obtains this from residues on the same pole progressions. -/
structure BaseValueRecoveryData {k d : Nat}
    (θ θ' : Params 1 k d) (σ : Equiv.Perm (Fin k)) : Prop where
  value_action_eq :
    ∀ h : Fin k, ∀ w : Vec d, baseValue θ (σ h) *ᵥ w = baseValue θ' h *ᵥ w

namespace BaseValueRecoveryData

/-- Pointwise complex coefficient equality on a nonempty open set of `w` probes
globalizes to the value-recovery package for the fixed attention permutation. -/
theorem of_coeffC_eq_on_nonempty_open {k d : Nat} {θ θ' : Params 1 k d}
    {σ : Equiv.Perm (Fin k)} {W : Set (Vec d)}
    (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    (hcoeff :
      ∀ h : Fin k, ∀ w : Vec d, w ∈ W →
        baseCoeffC θ w (σ h) = baseCoeffC θ' w h) :
    BaseValueRecoveryData θ θ' σ := by
  refine ⟨?_⟩
  intro h
  exact matrix_mulVec_eq_of_eq_on_nonempty_open_khead
    (M := baseValue θ (σ h)) (N := baseValue θ' h)
    hW_open hW_nonempty (by
      intro w hw
      ext i
      have hi :
          (((baseValue θ (σ h) *ᵥ w) i : ℝ) : ℂ) =
            (((baseValue θ' h *ᵥ w) i : ℝ) : ℂ) := by
        simpa [baseCoeffC] using congrFun (hcoeff h w hw) i
      exact Complex.ofReal_inj.mp hi)

theorem value_matrix_eq {k d : Nat} {θ θ' : Params 1 k d}
    {σ : Equiv.Perm (Fin k)} (D : BaseValueRecoveryData θ θ' σ)
    (h : Fin k) :
    baseValue θ (σ h) = baseValue θ' h :=
  matrix_eq_of_forall_mulVec_eq_khead (D.value_action_eq h)

end BaseValueRecoveryData

namespace BasePairedProbeRecoveryData

/-- Paired probe recovery gives the product identity on the recovered dense
probe set, hence the exact product package expected by the algebraic
globalization step. -/
theorem product_eq_on {k d : Nat} {θ θ' : Params 1 k d}
    (D : BasePairedProbeRecoveryData θ θ') :
    ∀ x : ProbePoint d, x ∈ D.U → ∀ t : ℝ,
      ∏ h : Fin k, (t - baseSlope θ x.1 x.2 h) =
        ∏ h : Fin k, (t - baseSlope θ' x.1 x.2 h) := by
  classical
  intro x hx t
  rcases D.paired_on x hx with ⟨σ, hσ⟩
  have hreindex :
      (∏ h : Fin k, (t - baseSlope θ x.1 x.2 (σ h))) =
        ∏ h : Fin k, (t - baseSlope θ x.1 x.2 h) := by
    simpa using
      (Fintype.prod_equiv σ
        (fun h : Fin k => t - baseSlope θ x.1 x.2 (σ h))
        (fun h : Fin k => t - baseSlope θ x.1 x.2 h)
        (by intro h; rfl))
  calc
    ∏ h : Fin k, (t - baseSlope θ x.1 x.2 h)
        = ∏ h : Fin k, (t - baseSlope θ x.1 x.2 (σ h)) := hreindex.symm
    _ = ∏ h : Fin k, (t - baseSlope θ' x.1 x.2 h) := by
      refine Finset.prod_congr rfl ?_
      intro h _hh
      rw [(hσ h).1]

/-- Compile paired probe recovery to the product-identity data package consumed
by `K05_prop_base_case`. -/
def to_product_identity_data {k d : Nat} {θ θ' : Params 1 k d}
    (D : BasePairedProbeRecoveryData θ θ') :
    BaseProductIdentityData θ θ' where
  U := D.U
  zariski_dense := D.zariski_dense
  product_eq_on := D.product_eq_on

/-- Once the global attention permutation has been extracted, the probe-wise
paired recovery permutation must be that same permutation at any separated
primed probe.  Therefore its paired residue coefficient is attached to the
fixed attention label. -/
theorem coeff_eq_of_attention_permutation {k d : Nat}
    {θ θ' : Params 1 k d} (D : BasePairedProbeRecoveryData θ θ')
    {σ : Equiv.Perm (Fin k)}
    (hσ_att : ∀ h : Fin k, baseAttention θ (σ h) = baseAttention θ' h)
    {x : ProbePoint d} (hx : x ∈ D.U)
    (hsep' : Function.Injective (baseSlope θ' x.1 x.2)) :
    ∀ h : Fin k, baseCoeffC θ x.1 (σ h) = baseCoeffC θ' x.1 h := by
  classical
  rcases D.paired_on x hx with ⟨τ, hτ⟩
  have hσ_slope :
      ∀ h : Fin k,
        baseSlope θ x.1 x.2 (σ h) = baseSlope θ' x.1 x.2 h := by
    intro h
    simp [baseSlope, hσ_att h]
  have hτ_eq : τ = σ := by
    apply Equiv.ext
    intro h
    have hτ_slope := (hτ h).1
    have hσ_slope_at :
        baseSlope θ x.1 x.2 (τ h) =
          baseSlope θ' x.1 x.2 (σ.symm (τ h)) := by
      simpa using hσ_slope (σ.symm (τ h))
    have htarget :
        baseSlope θ' x.1 x.2 h =
          baseSlope θ' x.1 x.2 (σ.symm (τ h)) :=
      hτ_slope.symm.trans hσ_slope_at
    have hh : h = σ.symm (τ h) := hsep' htarget
    calc
      τ h = σ (σ.symm (τ h)) := by simp
      _ = σ h := by rw [← hh]
  intro h
  simpa [hτ_eq] using (hτ h).2

/-- The residue coefficient equality obtained on an open family of separated
probes globalizes to equality of the fixed paired value matrices.  The selector
`vOf` records the TeX projection step from an open probe set to an open set of
`w`-vectors. -/
theorem value_recovery_of_open_paired {k d : Nat}
    {θ θ' : Params 1 k d} (D : BasePairedProbeRecoveryData θ θ')
    {σ : Equiv.Perm (Fin k)}
    (hσ_att : ∀ h : Fin k, baseAttention θ (σ h) = baseAttention θ' h)
    {W : Set (Vec d)} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    (vOf : Vec d → Vec d)
    (hprobe : ∀ w : Vec d, w ∈ W → (w, vOf w) ∈ D.U)
    (hsep' : ∀ w : Vec d, w ∈ W →
      Function.Injective (baseSlope θ' w (vOf w))) :
    BaseValueRecoveryData θ θ' σ := by
  refine BaseValueRecoveryData.of_coeffC_eq_on_nonempty_open
    hW_open hW_nonempty ?_
  intro h w hw
  exact D.coeff_eq_of_attention_permutation hσ_att
    (x := (w, vOf w)) (hprobe w hw) (hsep' w hw) h

/-- If paired recovery is available on a set containing a nonempty Euclidean-open
family of separated probes, the final value-recovery step needs no separately
chosen `w`-open set: an open slice is extracted from the probe set. -/
theorem value_recovery_of_open_probe_set {k d : Nat}
    {θ θ' : Params 1 k d} (D : BasePairedProbeRecoveryData θ θ')
    {σ : Equiv.Perm (Fin k)}
    (hσ_att : ∀ h : Fin k, baseAttention θ (σ h) = baseAttention θ' h)
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω)
    (hΩ_nonempty : Ω.Nonempty) (hΩ_subset : Ω ⊆ D.U)
    (hsep' : ∀ x : ProbePoint d, x ∈ Ω →
      Function.Injective (baseSlope θ' x.1 x.2)) :
    BaseValueRecoveryData θ θ' σ := by
  rcases hΩ_nonempty with ⟨x0, hx0⟩
  rcases exists_open_w_slice_subset_of_open_probe_set hΩ_open hx0 with
    ⟨W, hW_open, hW_nonempty, _hw0, hslice⟩
  refine D.value_recovery_of_open_paired hσ_att hW_open hW_nonempty
    (fun _w => x0.2) ?_ ?_
  · intro w hw
    exact hΩ_subset (hslice w hw)
  · intro w hw
    exact hsep' (w, x0.2) (hslice w hw)

end BasePairedProbeRecoveryData

namespace BaseAggregateRecoveryData

/-- Aggregate recovery plus a nonempty Euclidean-open family of separated probes
supplies value recovery for any already-fixed global attention permutation. -/
theorem value_recovery_of_open_probe_set {k d : Nat}
    {θ θ' : Params 1 k d} (D : BaseAggregateRecoveryData θ θ')
    {σ : Equiv.Perm (Fin k)}
    (hσ_att : ∀ h : Fin k, baseAttention θ (σ h) = baseAttention θ' h)
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω)
    (hΩ_nonempty : Ω.Nonempty) (hΩ_subset : Ω ⊆ D.U) :
    BaseValueRecoveryData θ θ' σ :=
  D.paired_recovery.value_recovery_of_open_probe_set hσ_att hΩ_open
    hΩ_nonempty hΩ_subset (fun x hx =>
      (D.target_separated x (hΩ_subset hx)).slope_injective)

end BaseAggregateRecoveryData

/-- The base-case proof obligations after open-set equality has been analytically
continued and the separated-pole recovery argument has been run. -/
structure BaseCaseData {k d : Nat} (r : Nat)
    (θ θ' : Params 1 k d) where
  target_regular : Regularity r θ'
  products : BaseProductIdentityData θ θ'
  value_recovery :
    ∀ σ : Equiv.Perm (Fin k),
      (∀ h : Fin k, baseAttention θ (σ h) = baseAttention θ' h) →
        BaseValueRecoveryData θ θ' σ

namespace BaseCaseData

/-- A paired probe-recovery package plus the open-set residue coefficient
globalization is enough to instantiate the reduced base-case endpoint. -/
def of_paired_recovery {k d r : Nat} {θ θ' : Params 1 k d}
    (hθ' : Regularity r θ') (D : BasePairedProbeRecoveryData θ θ')
    (hvalue :
      ∀ σ : Equiv.Perm (Fin k),
        (∀ h : Fin k, baseAttention θ (σ h) = baseAttention θ' h) →
          BaseValueRecoveryData θ θ' σ) :
    BaseCaseData r θ θ' where
  target_regular := hθ'
  products := D.to_product_identity_data
  value_recovery := hvalue

/-- TeX-facing packaging from paired probe recovery on a nonempty open family of
separated probes.  The open probe set is sliced in the `w` direction to recover
the value matrices after the global attention permutation is fixed. -/
def of_paired_recovery_open_probe_set {k d r : Nat} {θ θ' : Params 1 k d}
    (hθ' : Regularity r θ') (D : BasePairedProbeRecoveryData θ θ')
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω)
    (hΩ_nonempty : Ω.Nonempty) (hΩ_subset : Ω ⊆ D.U)
    (hsep' : ∀ x : ProbePoint d, x ∈ Ω →
      Function.Injective (baseSlope θ' x.1 x.2)) :
    BaseCaseData r θ θ' :=
  BaseCaseData.of_paired_recovery hθ' D (fun _σ hσ_att =>
    D.value_recovery_of_open_probe_set hσ_att hΩ_open hΩ_nonempty
      hΩ_subset hsep')

/-- TeX-facing packaging directly from aggregate residue recovery.  On a nonempty
open subset of the aggregate-recovery domain, the primed separated-probe field
provides the slope injectivity needed by the value-recovery slice. -/
def of_aggregate_recovery_open_probe_set {k d r : Nat} {θ θ' : Params 1 k d}
    (hθ' : Regularity r θ') (D : BaseAggregateRecoveryData θ θ')
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω)
    (hΩ_nonempty : Ω.Nonempty) (hΩ_subset : Ω ⊆ D.U) :
    BaseCaseData r θ θ' :=
  BaseCaseData.of_paired_recovery hθ' D.paired_recovery (fun _σ hσ_att =>
    D.value_recovery_of_open_probe_set hσ_att hΩ_open hΩ_nonempty
      hΩ_subset)

/-- TeX-facing packaging from the finite-support aggregate map returned by
`K04B`: support equality plus coefficient equality on recovered support first
compiles to aggregate recovery, then follows the existing open-probe endpoint. -/
def of_finite_support_recovery_open_probe_set {k d r : Nat}
    {θ θ' : Params 1 k d}
    (hθ' : Regularity r θ')
    (D : BaseAggregateFiniteSupportRecoveryData θ θ')
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω)
    (hΩ_nonempty : Ω.Nonempty) (hΩ_subset : Ω ⊆ D.U) :
    BaseCaseData r θ θ' :=
  BaseCaseData.of_aggregate_recovery_open_probe_set hθ'
    D.to_aggregate_recovery hΩ_open hΩ_nonempty hΩ_subset

/-- TeX-facing packaging directly from positive-real complex probe-mixture
equality on a dense separated probe set. -/
def of_positive_real_probe_mixture_equality_open_probe_set {k d r : Nat}
    {θ θ' : Params 1 k d}
    (hr : 1 < r) (hθ' : Regularity r θ')
    (D : BasePositiveRealProbeMixtureEqualityData r θ θ')
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω)
    (hΩ_nonempty : Ω.Nonempty) (hΩ_subset : Ω ⊆ D.U) :
    BaseCaseData r θ θ' :=
  BaseCaseData.of_finite_support_recovery_open_probe_set hθ'
    (D.to_finite_support_recovery hr) hΩ_open hΩ_nonempty
    (by
      intro x hx
      exact hΩ_subset hx)

/-- TeX-facing packaging directly from positive-real closed probe-output equality
on a dense separated probe set. -/
def of_positive_real_probeOutput_equality_open_probe_set {k d r : Nat}
    {θ θ' : Params 1 k d}
    (hr : 1 < r) (hθ' : Regularity r θ')
    (D : BasePositiveRealProbeOutputEqualityData r θ θ')
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω)
    (hΩ_nonempty : Ω.Nonempty) (hΩ_subset : Ω ⊆ D.U) :
    BaseCaseData r θ θ' :=
  BaseCaseData.of_positive_real_probe_mixture_equality_open_probe_set hr hθ'
    D.to_mixture_equality hΩ_open hΩ_nonempty
    (by
      intro x hx
      exact hΩ_subset hx)

end BaseCaseData

/-- **K05.E.prop-base-case.S/P**, reduced Lean endpoint.

Given the product identity and paired residue/value-recovery obligations produced
by the analytic part of the TeX proof, the depth-one parameters agree up to one
unique target-to-source head permutation. -/
theorem K05_prop_base_case {k d r : Nat} {θ θ' : Params 1 k d}
    (D : BaseCaseData r θ θ') :
    ∃! σ : Equiv.Perm (Fin k),
      ∀ h : Fin k,
        baseAttention θ (σ h) = baseAttention θ' h ∧
          baseValue θ (σ h) = baseValue θ' h := by
  classical
  obtain ⟨σ, hσ, hσuniq⟩ :=
    D.products.attention_permutation D.target_regular
  refine ⟨σ, ?_, ?_⟩
  · intro h
    exact ⟨hσ h, (D.value_recovery σ hσ).value_matrix_eq h⟩
  · intro τ hτ
    exact hσuniq τ (fun h => (hτ h).1)

/-- TeX-facing finite-support wrapper for the reduced base-case endpoint. -/
theorem K05_prop_base_case_of_finite_support_recovery_open_probe_set {k d r : Nat}
    {θ θ' : Params 1 k d}
    (hθ' : Regularity r θ')
    (D : BaseAggregateFiniteSupportRecoveryData θ θ')
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω)
    (hΩ_nonempty : Ω.Nonempty) (hΩ_subset : Ω ⊆ D.U) :
    ∃! σ : Equiv.Perm (Fin k),
      ∀ h : Fin k,
        baseAttention θ (σ h) = baseAttention θ' h ∧
          baseValue θ (σ h) = baseValue θ' h := by
  exact K05_prop_base_case
    (BaseCaseData.of_finite_support_recovery_open_probe_set hθ' D hΩ_open
      hΩ_nonempty hΩ_subset)

/-- TeX-facing wrapper from positive-real complex probe-mixture equality on a
dense separated probe set. -/
theorem K05_prop_base_case_of_positive_real_probe_mixture_equality_open_probe_set
    {k d r : Nat} {θ θ' : Params 1 k d}
    (hr : 1 < r) (hθ' : Regularity r θ')
    (D : BasePositiveRealProbeMixtureEqualityData r θ θ')
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω)
    (hΩ_nonempty : Ω.Nonempty) (hΩ_subset : Ω ⊆ D.U) :
    ∃! σ : Equiv.Perm (Fin k),
      ∀ h : Fin k,
        baseAttention θ (σ h) = baseAttention θ' h ∧
          baseValue θ (σ h) = baseValue θ' h := by
  exact K05_prop_base_case
    (BaseCaseData.of_positive_real_probe_mixture_equality_open_probe_set
      hr hθ' D hΩ_open hΩ_nonempty hΩ_subset)

/-- TeX-facing wrapper from positive-real closed probe-output equality on a
dense separated probe set. -/
theorem K05_prop_base_case_of_positive_real_probeOutput_equality_open_probe_set
    {k d r : Nat} {θ θ' : Params 1 k d}
    (hr : 1 < r) (hθ' : Regularity r θ')
    (D : BasePositiveRealProbeOutputEqualityData r θ θ')
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω)
    (hΩ_nonempty : Ω.Nonempty) (hΩ_subset : Ω ⊆ D.U) :
    ∃! σ : Equiv.Perm (Fin k),
      ∀ h : Fin k,
        baseAttention θ (σ h) = baseAttention θ' h ∧
          baseValue θ (σ h) = baseValue θ' h := by
  exact K05_prop_base_case
    (BaseCaseData.of_positive_real_probeOutput_equality_open_probe_set
      hr hθ' D hΩ_open hΩ_nonempty hΩ_subset)

end

end TransformerIdentifiability.NLayer.KHead
