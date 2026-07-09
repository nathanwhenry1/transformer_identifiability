import AnyLayerIdentifiabilityProof.NLayer.KHead.Core
import AnyLayerIdentifiabilityProof.NLayer.KHead.BaseCase
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.TierCascadeData
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.Hypotheses
import AnyLayerIdentifiabilityProof.NLayer.KHead.Permutation
import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.Regularity
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.ActiveStratification
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SigmoidMixtures
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.CascadeClosure
import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.AnchorCertificate

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.KHead.Step1

universe uCoord

/-!
# K-head Step 1 pole-transfer endpoint

This file is an API scaffold for the TeX packet
`06c-step1-pole-transfer`.  It records the endpoint shapes for
`lem:first-layer-pole-containment` and `prop:first-A` without asserting
the analytic pole-transfer or matching arguments as proved facts.
-/

universe uProbe uHead uPoint uAttention uValue

/-- Public data named by `lem:first-layer-pole-containment`.

`firstPoleSet p h` represents `P(q'_{1h})` at a separated probe, and
`unprimedFirstReducedStratum p` represents `S^1_{\theta,red}(w,v)`. -/
structure FirstLayerPoleContainmentData
    (Probe : Type uProbe) (Head : Type uHead) (Point : Type uPoint) where
  separatedProbe : Set Probe
  firstPoleSet : Probe -> Head -> Set Point
  unprimedFirstReducedStratum : Probe -> Set Point

/-- Prop-valued statement corresponding to
`lem:first-layer-pole-containment`. -/
def FirstLayerPoleContainmentStatement
    {Probe : Type uProbe} {Head : Type uHead} {Point : Type uPoint}
    (D : FirstLayerPoleContainmentData Probe Head Point) : Prop :=
  ∀ p : Probe, p ∈ D.separatedProbe ->
    ∀ h : Head, D.firstPoleSet p h ⊆ D.unprimedFirstReducedStratum p

/-- Endpoint data for the pole-transfer chain used to obtain first-layer
pole containment.

The fields mirror the TeX proof after the hard analytic work has been
packaged:

* `lastTier` is `T_L`;
* `lastTierClosure` is the cascade envelope `acc^{L-1}(T_L)`;
* `reducedSingularClosure` is the corresponding envelope for
  `S_{\theta,red}`;
* `transferredLastTier_subset_unprimed` is the pole-transfer endpoint
  `T_L ⊆ S_{\theta,red}`;
* the remaining fields compose cascade monotonicity and stratified
  accumulation down to the first reduced stratum.
-/
structure PoleTransferEndpointData
    (Probe : Type uProbe) (Head : Type uHead) (Point : Type uPoint)
    extends FirstLayerPoleContainmentData Probe Head Point where
  unprimedReducedSingularSet : Probe -> Set Point
  lastTier : Probe -> Head -> Set Point
  lastTierClosure : Probe -> Head -> Set Point
  reducedSingularClosure : Probe -> Set Point
  firstPole_subset_lastTierClosure :
    ∀ p : Probe, p ∈ separatedProbe ->
      ∀ h : Head, firstPoleSet p h ⊆ lastTierClosure p h
  transferredLastTier_subset_unprimed :
    ∀ p : Probe, p ∈ separatedProbe ->
      ∀ h : Head, lastTier p h ⊆ unprimedReducedSingularSet p
  lastTierClosure_mono :
    ∀ p : Probe, p ∈ separatedProbe ->
      ∀ h : Head,
        lastTier p h ⊆ unprimedReducedSingularSet p ->
          lastTierClosure p h ⊆ reducedSingularClosure p
  reducedSingularClosure_subset_firstStratum :
    ∀ p : Probe, p ∈ separatedProbe ->
      reducedSingularClosure p ⊆ unprimedFirstReducedStratum p

namespace PoleTransferEndpointData

/-- The transferred final-tier containment, exposed under the TeX endpoint
terminology. -/
theorem finalTier_subset_unprimedReducedSingularSet
    {Probe : Type uProbe} {Head : Type uHead} {Point : Type uPoint}
    (D : PoleTransferEndpointData Probe Head Point)
    {p : Probe} (hp : p ∈ D.separatedProbe) (h : Head) :
    D.lastTier p h ⊆ D.unprimedReducedSingularSet p :=
  D.transferredLastTier_subset_unprimed p hp h

/-- The scaffold proves only the formal composition of the packaged
endpoint fields: pole transfer plus cascade monotonicity plus stratified
accumulation imply the first-layer pole-containment statement. -/
theorem firstLayerPoleContainment
    {Probe : Type uProbe} {Head : Type uHead} {Point : Type uPoint}
    (D : PoleTransferEndpointData Probe Head Point) :
    FirstLayerPoleContainmentStatement D.toFirstLayerPoleContainmentData := by
  intro p hp h τ hτ
  exact D.reducedSingularClosure_subset_firstStratum p hp
    (D.lastTierClosure_mono p hp h
      (D.transferredLastTier_subset_unprimed p hp h)
      (D.firstPole_subset_lastTierClosure p hp h hτ))

end PoleTransferEndpointData

/-- Generic `TierCascadeData`-parametric builder for `PoleTransferEndpointData`.

Given an abstract tier cascade `cascade`, its packaged `ChainCascadeData` `C`,
and the two honest analytic inputs

* `poleTransfer`: the pole-transfer endpoint `T_L ⊆ S_{θ,red}` (K04B), and
* `stratAccum`: the stratified-accumulation collapse
  `acc^{L-1}(S_{θ,red}) ⊆ S^1_{θ,red}` (K04D),

this assembles a `PoleTransferEndpointData` over the coordinate type `ℂ`.

The two *proved* fields are supplied from genuinely upstream theorems:
`firstPole_subset_lastTierClosure` is discharged by the proved
`TierCascadeData.ChainCascadeData.firstPoleFinalTierClosureStatement`, and
`lastTierClosure_mono` is discharged by `accIter_mono`.  The remaining two
fields are the caller-supplied analytic hypotheses above; they are legitimate
parameters standing for the K04B/K04D facts, not restatements of the target
first-layer pole-containment conclusion. -/
noncomputable def poleTransferEndpointData_of_cascade
    {Probe : Type uProbe} {Head : Type uHead} {Coord : Type uCoord}
    (cascade : TierCascadeData Probe Head Coord)
    (C : TierCascadeData.ChainCascadeData cascade)
    (unprimedReducedSingularSet : Probe → Set ℂ)
    (unprimedFirstReducedStratum : Probe → Set ℂ)
    (poleTransfer :
      ∀ p, p ∈ cascade.separatedProbe → ∀ h,
        cascade.T p h cascade.finalTierIndex ⊆ unprimedReducedSingularSet p)
    (stratAccum :
      ∀ p, p ∈ cascade.separatedProbe →
        accIter cascade.finalTierIndex (unprimedReducedSingularSet p)
          ⊆ unprimedFirstReducedStratum p) :
    PoleTransferEndpointData Probe Head ℂ where
  separatedProbe := cascade.separatedProbe
  firstPoleSet := cascade.firstPoleSet
  unprimedFirstReducedStratum := unprimedFirstReducedStratum
  unprimedReducedSingularSet := unprimedReducedSingularSet
  lastTier := fun p h => cascade.T p h cascade.finalTierIndex
  lastTierClosure := fun p h =>
    accIter cascade.finalTierIndex (cascade.T p h cascade.finalTierIndex)
  reducedSingularClosure := fun p =>
    accIter cascade.finalTierIndex (unprimedReducedSingularSet p)
  firstPole_subset_lastTierClosure := C.firstPoleFinalTierClosureStatement
  transferredLastTier_subset_unprimed := poleTransfer
  lastTierClosure_mono := fun _p _hp _h hsub =>
    accIter_mono hsub cascade.finalTierIndex
  reducedSingularClosure_subset_firstStratum := fun p hp => stratAccum p hp

/-- The first-layer pole-containment statement furnished for free by the
generic cascade builder (specialising `PoleTransferEndpointData.firstLayerPoleContainment`). -/
theorem firstLayerPoleContainment_of_cascade
    {Probe : Type uProbe} {Head : Type uHead} {Coord : Type uCoord}
    (cascade : TierCascadeData Probe Head Coord)
    (C : TierCascadeData.ChainCascadeData cascade)
    (unprimedReducedSingularSet : Probe → Set ℂ)
    (unprimedFirstReducedStratum : Probe → Set ℂ)
    (poleTransfer :
      ∀ p, p ∈ cascade.separatedProbe → ∀ h,
        cascade.T p h cascade.finalTierIndex ⊆ unprimedReducedSingularSet p)
    (stratAccum :
      ∀ p, p ∈ cascade.separatedProbe →
        accIter cascade.finalTierIndex (unprimedReducedSingularSet p)
          ⊆ unprimedFirstReducedStratum p) :
    FirstLayerPoleContainmentStatement
      (poleTransferEndpointData_of_cascade cascade C unprimedReducedSingularSet
          unprimedFirstReducedStratum poleTransfer stratAccum).toFirstLayerPoleContainmentData :=
  (poleTransferEndpointData_of_cascade cascade C unprimedReducedSingularSet
      unprimedFirstReducedStratum poleTransfer stratAccum).firstLayerPoleContainment

/-- Public data named by `prop:first-A`.

`unprimedActive a` is the activity predicate for the unprimed first-layer
head `a`; in the TeX proof this is `V_{1a} ≠ 0`. -/
structure FirstLayerAttentionIdentificationData
    (Head : Type uHead) (Attention : Type uAttention) (Value : Type uValue) where
  unprimedAttention : Head -> Attention
  primedAttention : Head -> Attention
  unprimedValue : Head -> Value
  primedValue : Head -> Value
  unprimedActive : Head -> Prop

/-- The attention equality predicate extracted by `prop:first-A`. -/
def FirstLayerAttentionPermutationPredicate
    {Head : Type uHead} {Attention : Type uAttention} {Value : Type uValue}
    (D : FirstLayerAttentionIdentificationData Head Attention Value)
    (σ : Equiv.Perm Head) : Prop :=
  ∀ h : Head, D.unprimedAttention (σ h) = D.primedAttention h

/-- The matched-activity predicate in the final sentence of `prop:first-A`. -/
def FirstLayerMatchedActivityPredicate
    {Head : Type uHead} {Attention : Type uAttention} {Value : Type uValue}
    (D : FirstLayerAttentionIdentificationData Head Attention Value)
    (σ : Equiv.Perm Head) : Prop :=
  ∀ h : Head, D.unprimedActive (σ h)

/-- Result object corresponding to `prop:first-A`.

The uniqueness field applies only to the attention equality, matching the
TeX statement: activity is an additional conclusion for the same extracted
permutation. -/
structure FirstLayerAttentionIdentificationResult
    {Head : Type uHead} {Attention : Type uAttention} {Value : Type uValue}
    (D : FirstLayerAttentionIdentificationData Head Attention Value) where
  sigma : Equiv.Perm Head
  attention_eq : FirstLayerAttentionPermutationPredicate D sigma
  attention_unique :
    ∀ ρ : Equiv.Perm Head,
      FirstLayerAttentionPermutationPredicate D ρ -> ρ = sigma
  matched_active : FirstLayerMatchedActivityPredicate D sigma

/-- Prop-valued statement corresponding to `prop:first-A`. -/
def FirstLayerAttentionIdentificationStatement
    {Head : Type uHead} {Attention : Type uAttention} {Value : Type uValue}
    (D : FirstLayerAttentionIdentificationData Head Attention Value) : Prop :=
  Nonempty (FirstLayerAttentionIdentificationResult D)

namespace FirstLayerAttentionIdentificationResult

/-- The extracted first-layer permutation is unique for attention equality. -/
theorem existsUnique_attention
    {Head : Type uHead} {Attention : Type uAttention} {Value : Type uValue}
    {D : FirstLayerAttentionIdentificationData Head Attention Value}
    (R : FirstLayerAttentionIdentificationResult D) :
    ∃! σ : Equiv.Perm Head, FirstLayerAttentionPermutationPredicate D σ := by
  refine ⟨R.sigma, R.attention_eq, ?_⟩
  intro ρ hρ
  exact R.attention_unique ρ hρ

/-- Activity of the unprimed head matched to a primed first-layer head. -/
theorem matchedActive
    {Head : Type uHead} {Attention : Type uAttention} {Value : Type uValue}
    {D : FirstLayerAttentionIdentificationData Head Attention Value}
    (R : FirstLayerAttentionIdentificationResult D) (h : Head) :
    D.unprimedActive (R.sigma h) :=
  R.matched_active h

/-- Any result object witnesses the Prop-valued first-attention
identification statement. -/
theorem statement
    {Head : Type uHead} {Attention : Type uAttention} {Value : Type uValue}
    {D : FirstLayerAttentionIdentificationData Head Attention Value}
    (R : FirstLayerAttentionIdentificationResult D) :
    FirstLayerAttentionIdentificationStatement D :=
  ⟨R⟩

end FirstLayerAttentionIdentificationResult

/-- Density adapter: the inline probe-set Zariski density notion
`ZariskiDenseProbeSet` (in the `(w, v)` probe evaluation) coincides with the
bilinear-variable density notion `ProbeZariskiDense`.  The two are definitionally
equal: `ProbePoly d = MvPolynomial (ProbeVar d) ℝ = MvPolynomial (BilinVar d) ℝ`,
and `probePolyEval p.1 p.2 = Sum.elim p.1 p.2` as functions on `Sum (Fin d) (Fin d)`. -/
theorem probeZariskiDense_of_zariskiDenseProbeSet {d : Nat}
    {U : Set (ProbePoint d)} (h : ZariskiDenseProbeSet U) : ProbeZariskiDense U := by
  intro P hP
  refine h P (fun p hp => ?_)
  have hfun : probePolyEval p.1 p.2 = Sum.elim p.1 p.2 := by
    funext x; cases x <;> rfl
  rw [hfun]
  exact hP p hp

/-- Regularity makes the primed first-layer (`layer 0`) attention family injective,
mirroring the depth-one base-case fact `baseAttention_injective_of_regular`. -/
theorem firstLayerAttention_injective_of_regular {m k d : Nat} {r : Nat}
    {θ' : Params (m + 1) k d} (hθ' : Regularity r θ') :
    Function.Injective (attentionMatrix θ' 0) := by
  intro h g heq
  by_contra hne
  exact (hθ'.headAttention_ne 0 hne) heq

/-! ## Concrete K06C.M3 pole-transfer endpoint for the Step-1 tier cascade

The declarations below discharge the concrete first-layer pole-containment
statement `lem:first-layer-pole-containment` for `step1TierCascadeData hr H`,
transferring the *primed* final-tier poles into the **unprimed-`θ`** reduced
singular set / first reduced stratum.

The unprimed target stratum is built from a *separate* stratification
`activeConstructedStratificationData θ p.1.1 p.1.2` on the *unprimed* parameters
`θ` (NOT the cascade's own primed `θ'`-stratification), so the resulting
containment `P(q'_{1h}) ⊆ S^1_{θ,red}` is exactly the TeX statement, not the
trivial `⊆ S^1_{θ',red}`. -/

/-- **K06C.M3, category-B analytic input** (the genuine cross-parameter pole
transfer).  A primed final-tier pole `τ` is a pole of the unprimed observable,
hence lands in the unprimed reduced singular set.

The proof composes the K04B pole-transfer lemma
`lem_pole_transfer_of_real_tail_eq` with:

* holomorphy of both observables off their respective reduced singular sets
  (`observable_holomorphic` + `finalOmega_eq_compl_reducedSingularSet`);
* real-tail agreement of the two observables on `(0, ∞)`
  (`observable_positive_real_eq_probeOutput` on both sides, glued by
  `H.probeOutputEquality`);
* the cascade's `final_tier_blowup` (isolation of the primed singular set and
  blow-up of the primed observable at `τ`). -/
theorem step1PoleTransfer {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ') :
    ∀ p, p ∈ (step1TierCascadeData hr H).separatedProbe → ∀ h,
      (step1TierCascadeData hr H).T p h (step1TierCascadeData hr H).finalTierIndex ⊆
        reducedSingularSet (activeConstructedStratificationData (r := r) θ p.1.1 p.1.2) := by
  intro p hp h τ hτ
  obtain ⟨-, hIsol, c, -, hblow⟩ :=
    (step1TierCascadeAPI hr H).final_tier_blowup p hp h τ hτ
  have hDp : ActiveHeadSingularStratification hr θ' p.1.1 p.1.2
      (step1ActiveStratificationData hr H p) :=
    step1ActiveStratificationData_spec hr H p
  have hDθ : ActiveHeadSingularStratification hr θ p.1.1 p.1.2
      (activeConstructedStratificationData (r := r) θ p.1.1 p.1.2) :=
    activeConstructedStratificationData_singularStratification hr θ p.1.1 p.1.2
  have hEG : (step1TierCascadeData hr H).singularSet p h =
      reducedSingularSet (step1ActiveStratificationData hr H p) :=
    step1TierCascadeData_singularSet_eq_reducedSingularSet p h
  refine lem_pole_transfer_of_real_tail_eq
    (E_F := reducedSingularSet (activeConstructedStratificationData (r := r) θ p.1.1 p.1.2))
    (E_G := reducedSingularSet (step1ActiveStratificationData hr H p))
    (F := fun z => (activeConstructedStratificationData (r := r) θ p.1.1 p.1.2).observable z c)
    (G := fun z => (step1ActiveStratificationData hr H p).observable z c)
    (T0 := 0) (x0 := 1) (τ := τ)
    (reducedSingularSet_closed hDθ)
    (reducedSingularSet_countable hDθ)
    (reducedSingularSet_countable hDp)
    ?hF ?hG ?hx0 ?hz0 ?hfg ?hFcont ?hGisol ?hGblow
  case hF =>
    rw [← finalOmega_eq_compl_reducedSingularSet hDθ]
    exact hDθ.observable_holomorphic c
  case hG =>
    rw [← finalOmega_eq_compl_reducedSingularSet hDp]
    exact hDp.observable_holomorphic c
  case hx0 => norm_num
  case hz0 =>
    have h1nn : ((1 : ℝ) : ℂ) ∈ nonnegativeRealAxis :=
      positiveRealAxis_subset_nonnegativeRealAxis
        (ofReal_mem_positiveRealAxis (show (0 : ℝ) < 1 by norm_num))
    intro hmem
    rcases hmem with hmem | hmem
    · exact nonnegativeRealAxis_subset_finalOmega hDθ h1nn hmem
    · exact nonnegativeRealAxis_subset_finalOmega hDp h1nn hmem
  case hfg =>
    intro t ht
    have e1 := hDθ.observable_positive_real_eq_probeOutput t ht
    have e2 := hDp.observable_positive_real_eq_probeOutput t ht
    have e3 := H.probeOutputEquality p.1 t ht
    show (activeConstructedStratificationData (r := r) θ p.1.1 p.1.2).observable (t : ℂ) c
        = (step1ActiveStratificationData hr H p).observable (t : ℂ) c
    rw [e1, e2, e3]
  case hFcont =>
    intro hτF
    have hFan := hDθ.observable_holomorphic c
    rw [finalOmega_eq_compl_reducedSingularSet hDθ] at hFan
    exact (hFan τ hτF).continuousAt
  case hGisol =>
    rw [hEG] at hIsol
    exact hIsol
  case hGblow =>
    exact hblow

/-- **K06C.M3, category-A stratified accumulation collapse.**  The `m`-fold
cascade envelope of the unprimed reduced singular set collapses onto the
unprimed first reduced stratum `S^1_{θ,red}`.

Proof: `reducedSingularSet_accumulation_subset` (K04D) with `q = finalTierIndex
= m` and `L = m + 1`, followed by `partialUnion_one`. -/
theorem step1StratAccum {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ') :
    ∀ p, p ∈ (step1TierCascadeData hr H).separatedProbe →
      accIter (step1TierCascadeData hr H).finalTierIndex
          (reducedSingularSet (activeConstructedStratificationData (r := r) θ p.1.1 p.1.2))
        ⊆ (activeConstructedStratificationData (r := r) θ p.1.1 p.1.2).stratum 0 := by
  intro p _hp
  rw [step1TierCascadeData_finalTierIndex hr H]
  have hDθ : ActiveHeadSingularStratification hr θ p.1.1 p.1.2
      (activeConstructedStratificationData (r := r) θ p.1.1 p.1.2) :=
    activeConstructedStratificationData_singularStratification hr θ p.1.1 p.1.2
  have hsub := reducedSingularSet_accumulation_subset hDθ (show m ≤ m + 1 by omega)
  have hone : m + 1 - m = 1 := by omega
  rw [hone] at hsub
  refine hsub.trans ?_
  intro z hz
  obtain ⟨j, hj, hzj⟩ := hz
  have hj0 : j = 0 := by omega
  subst hj0
  exact hzj

/-- The concrete `ChainCascadeData` packaging for the Step-1 tier cascade, built
from the propagation analytic payloads (used only for
`firstPoleFinalTierClosureStatement`). -/
noncomputable def step1PoleTransferChainCascadeData {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ') :
    TierCascadeData.ChainCascadeData (step1TierCascadeData hr H) :=
  step1ChainCascadeData_of_payloads
    (step1TierPropagationAnalyticPayloads hr H)
    (step1ChainCascadeSetPayloads_of_propagation (step1TierPropagationAnalyticPayloads hr H))

/-- **K06C.M3 endpoint object.**  The concrete `PoleTransferEndpointData` for
`step1TierCascadeData hr H`, instantiating the generic builder
`poleTransferEndpointData_of_cascade` with the honest unprimed-`θ` analytic
inputs `step1PoleTransfer` (K04B) and `step1StratAccum` (K04D). -/
noncomputable def step1PoleTransferEndpointData {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ') :
    PoleTransferEndpointData (Step1SeparatedProbe H) (Fin k) ℂ :=
  poleTransferEndpointData_of_cascade
    (step1TierCascadeData hr H)
    (step1PoleTransferChainCascadeData hr H)
    (fun p => reducedSingularSet (activeConstructedStratificationData (r := r) θ p.1.1 p.1.2))
    (fun p => (activeConstructedStratificationData (r := r) θ p.1.1 p.1.2).stratum 0)
    (step1PoleTransfer hr H)
    (step1StratAccum hr H)

/-- **K06C.M3 (`lem:first-layer-pole-containment`), concrete.**  First-layer
pole containment for the Step-1 tier cascade: every separated probe's primed
first-layer pole set `P(q'_{1h})` sits inside the unprimed first reduced stratum
`S^1_{θ,red}(w, v)`.  This is the exact TeX endpoint feeding `prop:first-A`. -/
theorem step1FirstLayerPoleContainment {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ') :
    FirstLayerPoleContainmentStatement
      (step1PoleTransferEndpointData hr H).toFirstLayerPoleContainmentData :=
  (step1PoleTransferEndpointData hr H).firstLayerPoleContainment

/-! ## K06C.M4 — aggregate first-layer slope matching

From `step1FirstLayerPoleContainment` (`P(q'_{1h}) ⊆ S^1_{θ,red}(w,v)`) and the K04D
union-identity `mem_first_stratum_iff` we transfer the *primed* first-layer slopes onto
*unprimed*-active first-layer slopes.  Because a first-layer pole progression is nonempty
and its points all share the real part `-logScale r / slope`, containment forces, for every
primed head `h`, an unprimed active head `a` with `slope θ a p = slope θ' h p`.  Distinctness
of the primed slopes (`FirstLayerSlopeSeparation`) makes the induced primed→unprimed map
injective, hence — on `Fin k` — bijective; this yields the aggregate monic-product equality
and that **every** unprimed `θ`-head is active. -/

/-- **K06C.M4 slope-match (per primed head).**  For a separated probe, every primed
first-layer head `h` is matched by an unprimed-active first-layer head `a` with equal
first-layer slope. -/
theorem step1FirstLayerSlopeMatch {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet) (h : Fin k) :
    ∃ a : Fin k, a ∈ activeHeads θ (0 : Fin (m + 1)) ∧
      firstLayerSlope θ a p = firstLayerSlope θ' h p := by
  have hL : (0 : Nat) < m + 1 := Nat.succ_pos m
  have hsep : FirstLayerSlopeSeparation θ' p :=
    ((H.mem_separatedSet_iff p).mp hp).1
  -- Containment `P(q'_{1h}) ⊆ S^1_{θ,red}(w,v)` at this separated probe.
  have hcont := step1FirstLayerPoleContainment hr H ⟨p, hp⟩ (Set.mem_univ _) h
  -- The primed progression is nonempty; pick a pole.
  obtain ⟨τ₀, hτ₀⟩ :=
    affineSigmoidPoleSet_nonempty (logScale r) (firstLayerSlope θ' h p)
  have hτ₀' : τ₀ ∈ firstLayerPoleProgression r θ' p h := hτ₀
  have hmemS : τ₀ ∈ (activeConstructedStratificationData (r := r) θ p.1 p.2).stratum 0 :=
    hcont hτ₀'
  have hDθ := activeConstructedStratificationData_singularStratification hr θ p.1 p.2
  rw [mem_first_stratum_iff hDθ hL] at hmemS
  obtain ⟨a, haActive, haSlope, haMem⟩ := hmemS
  have hslopeθ : firstLayerSlope θ a p ≠ 0 := haSlope
  have hslopeθ' : firstLayerSlope θ' h p ≠ 0 := hsep.1 h
  have haMem' : τ₀ ∈ firstLayerPoleProgression r θ p a := haMem
  have hreθ : τ₀.re = firstLayerPoleRealPartLabel r θ p a :=
    firstLayerPoleProgression_re hslopeθ haMem'
  have hreθ' : τ₀.re = firstLayerPoleRealPartLabel r θ' p h :=
    firstLayerPoleProgression_re hslopeθ' hτ₀'
  refine ⟨a, haActive, ?_⟩
  have hlabels : -logScale r / firstLayerSlope θ a p
      = -logScale r / firstLayerSlope θ' h p := by
    have h1 : firstLayerPoleRealPartLabel r θ p a
        = firstLayerPoleRealPartLabel r θ' p h := hreθ.symm.trans hreθ'
    simpa [firstLayerPoleRealPartLabel] using h1
  rw [div_eq_div_iff hslopeθ hslopeθ'] at hlabels
  exact (mul_left_cancel₀ (neg_ne_zero.mpr (logScale_ne_zero_of_one_lt hr)) hlabels).symm

/-- **K06C.M4 matching bijection.**  The primed→unprimed first-layer slope match is a
permutation of `Fin k` sending each primed head to an unprimed-active head with equal slope.
Injectivity is forced by distinctness of the primed slopes; on `Fin k` injective ⇒ bijective. -/
theorem step1FirstLayerMatching {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet) :
    ∃ e : Equiv.Perm (Fin k),
      (∀ h : Fin k, firstLayerSlope θ (e h) p = firstLayerSlope θ' h p) ∧
        (∀ h : Fin k, e h ∈ activeHeads θ (0 : Fin (m + 1))) := by
  classical
  have hInj : Function.Injective (fun h : Fin k => firstLayerSlope θ' h p) :=
    ((H.mem_separatedSet_iff p).mp hp).1.2
  choose φ hφactive hφslope using fun h => step1FirstLayerSlopeMatch hr H hp h
  have hφinj : Function.Injective φ := by
    intro h g hhg
    have hslopes : firstLayerSlope θ' h p = firstLayerSlope θ' g p := by
      rw [← hφslope h, ← hφslope g, hhg]
    exact hInj hslopes
  have hφbij : Function.Bijective φ := Finite.injective_iff_bijective.mp hφinj
  exact ⟨Equiv.ofBijective φ hφbij, fun h => hφslope h, fun h => hφactive h⟩

/-- **K06C.M4 aggregate slope-product equality.**  At every separated probe the monic
first-layer slope products over unprimed and primed heads agree. -/
theorem step1FirstLayerSlopeProduct {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet) (t : ℝ) :
    ∏ a : Fin k, (t - firstLayerSlope θ a p)
      = ∏ h : Fin k, (t - firstLayerSlope θ' h p) := by
  obtain ⟨e, heslope, _⟩ := step1FirstLayerMatching hr H hp
  calc
    ∏ a : Fin k, (t - firstLayerSlope θ a p)
        = ∏ h : Fin k, (t - firstLayerSlope θ (e h) p) :=
          (Equiv.prod_comp e (fun a => t - firstLayerSlope θ a p)).symm
    _ = ∏ h : Fin k, (t - firstLayerSlope θ' h p) := by
          refine Finset.prod_congr rfl ?_
          intro h _
          rw [heslope h]

/-- **K06C.M4 all-active byproduct.**  Surjectivity of the matching bijection forces every
unprimed first-layer `θ`-head to be active, even though `θ` is not assumed regular. -/
theorem step1FirstLayer_allHeadsActive {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet) (a : Fin k) :
    a ∈ activeHeads θ (0 : Fin (m + 1)) := by
  obtain ⟨e, _, heactive⟩ := step1FirstLayerMatching hr H hp
  obtain ⟨h, rfl⟩ := e.surjective a
  exact heactive h

/-! ## K06C.M5 — `prop:first-A`, first-layer attention identification -/

/-- **K06C.M5 permutation extraction.**  The globalized unique attention permutation for
the first layer: a *target-to-source* `σ` with `attentionMatrix θ 0 (σ h) = attentionMatrix
θ' 0 h`.  Uses K06A Zariski density of the separated set, the M4 aggregate slope-product
equality, and injectivity of the primed first-layer attention family. -/
theorem step1FirstAttentionPermutation {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ') :
    ∃! σ : Equiv.Perm (Fin k),
      ∀ h : Fin k, attentionMatrix θ 0 (σ h) = attentionMatrix θ' 0 h := by
  refine global_labeling_algebraic (attentionMatrix θ 0) (attentionMatrix θ' 0)
    H.separatedSet
    (firstLayerAttention_injective_of_regular H.target_regular)
    (probeZariskiDense_of_zariskiDenseProbeSet H.separatedSet_properties.zariski_dense)
    ?_
  intro x hx t
  have hprod := step1FirstLayerSlopeProduct hr H hx t
  simpa only [firstLayerSlope, matrixBilin] using hprod

/-- **K06C.M5 identification data** for the first-layer attention family.  `unprimedActive a`
is `a ∈ activeHeads θ 0`, i.e. `V_{1a} ≠ 0`. -/
noncomputable def step1FirstLayerAttentionIdentificationData {m k d : Nat}
    (θ θ' : Params (m + 1) k d) :
    FirstLayerAttentionIdentificationData (Fin k)
      (Matrix (Fin d) (Fin d) ℝ) (Matrix (Fin d) (Fin d) ℝ) where
  unprimedAttention := attentionMatrix θ 0
  primedAttention := attentionMatrix θ' 0
  unprimedValue := valueMatrix θ 0
  primedValue := valueMatrix θ' 0
  unprimedActive a := a ∈ activeHeads θ (0 : Fin (m + 1))

/-- **K06C.M5 (`prop:first-A`) result object.**  The extracted target-to-source first-layer
permutation `σ` with `attentionMatrix θ 0 (σ h) = attentionMatrix θ' 0 h`, its uniqueness,
and matched unprimed activity `σ h ∈ activeHeads θ 0` (i.e. `V_{1,σ(h)} ≠ 0`). -/
noncomputable def step1FirstLayerAttentionIdentificationResult {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ') :
    FirstLayerAttentionIdentificationResult
      (step1FirstLayerAttentionIdentificationData θ θ') := by
  classical
  refine
    { sigma := (step1FirstAttentionPermutation hr H).choose
      attention_eq := ?_
      attention_unique := ?_
      matched_active := ?_ }
  · exact (step1FirstAttentionPermutation hr H).choose_spec.1
  · exact fun ρ hρ => (step1FirstAttentionPermutation hr H).choose_spec.2 ρ hρ
  · intro h
    obtain ⟨p₀, hp₀⟩ := H.separatedSet_properties.nonempty
    exact step1FirstLayer_allHeadsActive hr H hp₀ _

/-- **K06C.M5 (`prop:first-A`), Prop-valued.**  First-layer attention identification holds:
there is a target-to-source permutation matching the first-layer attention families with
matched unprimed activity. -/
theorem step1FirstAttentionIdentification {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ') :
    FirstLayerAttentionIdentificationStatement
      (step1FirstLayerAttentionIdentificationData θ θ') :=
  ⟨step1FirstLayerAttentionIdentificationResult hr H⟩

/-- **K06C.M6 export package — common first-layer gates.**

The single object consumed by K07A.  It carries the target-to-source first-layer
permutation `σ` (`attentionMatrix θ 0 (σ h) = attentionMatrix θ' 0 h`), together with the
downstream first-layer equalities that follow immediately from the attention match:

* `attention_eq` / `attention_unique` / `matched_active` — re-exposed K06C.M5
  (`prop:first-A`) conclusions (`matched_active` is the *unprimed* activity
  `V_{1,σ(h)} ≠ 0`);
* `slope_eq` — the probe slopes agree, `q'_{1,σ(h)}(p) = q'_{1,h}(p)`;
* `pi_eq` — the dial covectors agree, `π'_{σ(h)}(w,v) = π'_{h}(w,v)`. -/
structure Step1CommonFirstGates {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ') where
  sigma : Equiv.Perm (Fin k)
  attention_eq : ∀ h, attentionMatrix θ 0 (sigma h) = attentionMatrix θ' 0 h
  attention_unique :
    ∀ ρ : Equiv.Perm (Fin k),
      (∀ h, attentionMatrix θ 0 (ρ h) = attentionMatrix θ' 0 h) → ρ = sigma
  matched_active : ∀ h, sigma h ∈ activeHeads θ (0 : Fin (m + 1))
  slope_eq : ∀ h p, firstLayerSlope θ (sigma h) p = firstLayerSlope θ' h p
  pi_eq : ∀ h w v, dialCovector θ (sigma h) w v = dialCovector θ' h w v

/-- **K06C.M6 builder.**  Assembles the common-first-gates export from the proved
K06C.M5 result `step1FirstLayerAttentionIdentificationResult`.  Every field is a
one-line consequence of `R.attention_eq`. -/
noncomputable def step1CommonFirstGates {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r) (H : Step1StandingHypotheses r θ θ') :
    Step1CommonFirstGates hr H :=
  let R := step1FirstLayerAttentionIdentificationResult hr H
  { sigma := R.sigma
    attention_eq := R.attention_eq
    attention_unique := R.attention_unique
    matched_active := R.matched_active
    slope_eq := by
      intro h p
      have he : attentionMatrix θ 0 (R.sigma h) = attentionMatrix θ' 0 h := R.attention_eq h
      simp only [firstLayerSlope, he]
    pi_eq := by
      intro h w v
      have he : attentionMatrix θ 0 (R.sigma h) = attentionMatrix θ' 0 h := R.attention_eq h
      simp only [dialCovector, he] }

end TransformerIdentifiability.NLayer.KHead.Step1
