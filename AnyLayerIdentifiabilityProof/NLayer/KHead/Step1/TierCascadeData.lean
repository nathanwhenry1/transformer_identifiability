import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.ActiveStratification

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.KHead.Step1

universe uProbe uHead uCoord

/-!
# K-head Step 1 tier-cascade abstract API

Universe-polymorphic statement/data interface for the `06b-step1-tier-cascade`
packet: tier sets, the cascade-branch data, and Prop-valued interfaces for the
analytic statements.  This file carries no Step-1-specific instantiation; the
concrete bridge from K06A/K04D lives in `Step1/TierCascade.lean`.  Downstream
packets (e.g. K06C) can import this interface without pulling in the concrete
bridge.
-/

/-! ## Basic point-set notation -/

/-- The real axis inside `ℂ`. -/
def realAxis : Set ℂ :=
  Set.range fun x : ℝ => (x : ℂ)

/-- Open punctured disc `Dˣ(ξ, ρ)`.  The radius is real-valued, matching the TeX API. -/
def puncturedDisc (ξ : ℂ) (ρ : ℝ) : Set ℂ :=
  {τ | τ ≠ ξ ∧ dist τ ξ < ρ}

/-- Infinitely many points of `A` occur in every punctured disc around `ξ`. -/
def EveryPuncturedDiscInfinite (A : Set ℂ) (ξ : ℂ) : Prop :=
  ∀ ⦃ρ : ℝ⦄, 0 < ρ -> (A ∩ puncturedDisc ξ ρ).Infinite

/-- Infinite punctured-disc hits imply accumulation at the center. -/
theorem EveryPuncturedDiscInfinite.mem_acc {A : Set ℂ} {ξ : ℂ}
    (h : EveryPuncturedDiscInfinite A ξ) :
    ξ ∈ acc A := by
  have hclosure : ξ ∈ closure (A \ {ξ}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases (h hε).nonempty with ⟨z, hzA, hzpunctured⟩
    refine ⟨z, ⟨hzA, ?_⟩, ?_⟩
    · simpa using hzpunctured.1
    · simpa [dist_comm] using hzpunctured.2
  rw [acc, mem_derivedSet, accPt_iff_frequently_nhdsNE]
  exact (mem_closure_ne_iff_frequently_within (z := ξ) (s := A)).1 hclosure

/-- Filter form of punctured neighborhoods at a complex point. -/
noncomputable abbrev puncturedNhds (τ : ℂ) : Filter ℂ :=
  nhdsWithin τ ({τ}ᶜ : Set ℂ)

@[simp]
theorem zero_mem_realAxis : (0 : ℂ) ∈ realAxis := by
  exact ⟨0, by simp⟩

/-! ## Tier data and tier sets -/

/-- Core data used by the selected-head tier cascade.

The layer index is zero-based: `T p h 0` is the TeX set `T_1`, and
`stratum p h j` is the TeX stratum `S'^{j+1}` for the fixed separated probe and
selected first-layer head.  The fields `level`, `gate`, `selectedHead`, and
`dominanceThreshold` are bookkeeping API for later concrete workers; the tier
sets themselves only need the selected collision predicate and dominance
predicate.
-/
structure TierCascadeData (Probe : Type uProbe) (Head : Type uHead)
    (Coord : Type uCoord) where
  depth : Nat
  depth_pos : 0 < depth
  separatedProbe : Set Probe
  selectedHead : Probe -> Head -> Nat -> Head
  firstPoleSet : Probe -> Head -> Set ℂ
  omega : Probe -> Head -> Nat -> Set ℂ
  stratum : Probe -> Head -> Nat -> Set ℂ
  level : Probe -> Head -> Nat -> Head -> ℂ -> ℂ
  gate : Probe -> Head -> Nat -> Head -> ℂ -> ℂ
  dominanceThreshold : Probe -> Head -> Nat -> ℂ -> ℝ
  selectedOnlyCollision : Probe -> Head -> Nat -> ℂ -> Prop
  dominance : Probe -> Head -> Nat -> ℂ -> Prop
  selectedGatePole : Probe -> Head -> Nat -> ℂ -> Prop
  successorLevelPole : Probe -> Head -> Nat -> ℂ -> Prop
  siblingAvoidanceReady : Probe -> Head -> Nat -> ℂ -> Prop
  observableCoord : Probe -> Head -> Coord -> ℂ -> ℂ
  visibleCoordinate : Probe -> Head -> Coord -> Prop
  firstPole_subset_stratum :
    ∀ p h, firstPoleSet p h ⊆ stratum p h 0
  successor_collision_mem_stratum :
    ∀ p h j {τ : ℂ},
      τ ∈ omega p h (j + 1) ->
        selectedOnlyCollision p h (j + 1) τ ->
          τ ∈ stratum p h (j + 1)
  stratum_avoids_nonnegativeRealAxis :
    ∀ p h j {τ : ℂ}, τ ∈ stratum p h j -> τ ∉ nonnegativeRealAxis

namespace TierCascadeData

/-- `def:tier-sets`: zero-based tier tower for a fixed separated probe and chain head.

For successor tiers this records the TeX conditions: membership in the current
regular domain, selected-only collision, off-axis, and dominance. -/
def T {Probe : Type uProbe} {Head : Type uHead} {Coord : Type uCoord}
    (D : TierCascadeData Probe Head Coord) (p : Probe) (h : Head) :
    Nat -> Set ℂ
  | 0 => D.firstPoleSet p h
  | j + 1 =>
      {τ |
        τ ∈ D.omega p h (j + 1)
          ∧ D.selectedOnlyCollision p h (j + 1) τ
          ∧ τ ∉ nonnegativeRealAxis
          ∧ D.dominance p h (j + 1) τ}

@[simp]
theorem T_zero {Probe : Type uProbe} {Head : Type uHead} {Coord : Type uCoord}
    (D : TierCascadeData Probe Head Coord) (p : Probe) (h : Head) :
    D.T p h 0 = D.firstPoleSet p h :=
  rfl

@[simp]
theorem mem_T_zero {Probe : Type uProbe} {Head : Type uHead} {Coord : Type uCoord}
    (D : TierCascadeData Probe Head Coord) (p : Probe) (h : Head) {τ : ℂ} :
    τ ∈ D.T p h 0 ↔ τ ∈ D.firstPoleSet p h :=
  Iff.rfl

@[simp]
theorem mem_T_succ {Probe : Type uProbe} {Head : Type uHead} {Coord : Type uCoord}
    (D : TierCascadeData Probe Head Coord) (p : Probe) (h : Head)
    (j : Nat) {τ : ℂ} :
    τ ∈ D.T p h (j + 1) ↔
      τ ∈ D.omega p h (j + 1)
        ∧ D.selectedOnlyCollision p h (j + 1) τ
        ∧ τ ∉ nonnegativeRealAxis
        ∧ D.dominance p h (j + 1) τ :=
  Iff.rfl

/-- Singular set attached to the fixed selected branch, as the finite union of strata. -/
def singularSet {Probe : Type uProbe} {Head : Type uHead} {Coord : Type uCoord}
    (D : TierCascadeData Probe Head Coord) (p : Probe) (h : Head) : Set ℂ :=
  {τ | ∃ j, j < D.depth ∧ τ ∈ D.stratum p h j}

/-- The zero-based final tier index. -/
def finalTierIndex {Probe : Type uProbe} {Head : Type uHead} {Coord : Type uCoord}
    (D : TierCascadeData Probe Head Coord) : Nat :=
  D.depth - 1

theorem finalTierIndex_lt_depth {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord) :
    D.finalTierIndex < D.depth := by
  unfold finalTierIndex
  have hpos : 0 < D.depth := D.depth_pos
  omega

/-- The final tier has no successor tier inside the cascade depth. -/
theorem finalTierIndex_succ_not_lt_depth {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord) :
    ¬ D.finalTierIndex + 1 < D.depth := by
  unfold finalTierIndex
  have hpos : 0 < D.depth := D.depth_pos
  omega

/-! ## `lem:tier-in-stratum` -/

/-- `lem:tier-in-stratum`, as a reusable statement shape. -/
def TierInStratumStatement {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord) : Prop :=
  ∀ p h j, D.T p h j ⊆ D.stratum p h j

/-- Tier sets sit in their corresponding strata. -/
theorem tier_in_stratum {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord)
    {p : Probe} {h : Head} {j : Nat} {τ : ℂ} (hτ : τ ∈ D.T p h j) :
    τ ∈ D.stratum p h j := by
  cases j with
  | zero =>
      exact D.firstPole_subset_stratum p h hτ
  | succ j =>
      exact D.successor_collision_mem_stratum p h j hτ.1 hτ.2.1

/-- `lem:tier-in-stratum` packaged as a statement theorem. -/
theorem tierInStratumStatement {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord) :
    TierInStratumStatement D := by
  intro p h j τ hτ
  exact D.tier_in_stratum hτ

/-- Tier points are off the nonnegative real axis. -/
theorem tier_not_mem_nonnegativeRealAxis {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord)
    {p : Probe} {h : Head} {j : Nat} {τ : ℂ} (hτ : τ ∈ D.T p h j) :
    τ ∉ nonnegativeRealAxis :=
  D.stratum_avoids_nonnegativeRealAxis p h j (D.tier_in_stratum hτ)

/-- In particular, tier points are nonzero. -/
theorem tier_ne_zero {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord)
    {p : Probe} {h : Head} {j : Nat} {τ : ℂ} (hτ : τ ∈ D.T p h j) :
    τ ≠ 0 := by
  intro hzero
  exact D.tier_not_mem_nonnegativeRealAxis hτ
    (by simpa [hzero] using zero_mem_nonnegativeRealAxis)

/-! ## `lem:tier-local` -/

/-- Result interface for `lem:tier-local`.

This is deliberately a Prop-valued interface: concrete workers may fill these
fields from stratification, sigmoid-pole, dominance, and sibling-avoidance
lemmas without this scaffold asserting those analytic facts globally.
-/
structure TierLocalResult {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord)
    (p : Probe) (h : Head) (j : Nat) (τ : ℂ) : Prop where
  mem_stratum : τ ∈ D.stratum p h j
  punctured_isolated_stratum : IsPuncturedIsolated (D.stratum p h j) τ
  punctured_omega_succ :
    ∀ᶠ z in puncturedNhds τ, z ∈ D.omega p h (j + 1)
  selectedGatePole : D.selectedGatePole p h j τ
  successorSelectedLevelPole :
    j + 1 < D.depth -> D.successorLevelPole p h (j + 1) τ
  siblingAvoidanceReady :
    j + 1 < D.depth -> D.siblingAvoidanceReady p h (j + 1) τ

/-- Prop-valued statement corresponding to `lem:tier-local`. -/
def TierLocalStatement {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord) : Prop :=
  ∀ p, p ∈ D.separatedProbe ->
    ∀ h j τ, j < D.depth -> τ ∈ D.T p h j -> TierLocalResult D p h j τ

/-! ## `lem:tier-propagation` -/

/-- Pointwise result interface for `lem:tier-propagation`. -/
structure TierPropagationResult {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord)
    (p : Probe) (h : Head) (j : Nat) (τ : ℂ) : Prop where
  infinitely_many :
    EveryPuncturedDiscInfinite (D.T p h (j + 1)) τ
  mem_acc : τ ∈ acc (D.T p h (j + 1))

/-- Prop-valued statement corresponding to `lem:tier-propagation`. -/
def TierPropagationStatement {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord) : Prop :=
  ∀ p, p ∈ D.separatedProbe ->
    ∀ h j τ, j + 1 < D.depth -> τ ∈ D.T p h j ->
      TierPropagationResult D p h j τ

/-- The subset-to-accumulation form consumed by the chain cascade. -/
def TierPropagationSubsetStatement {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord) : Prop :=
  ∀ p, p ∈ D.separatedProbe ->
    ∀ h j, j + 1 < D.depth -> D.T p h j ⊆ acc (D.T p h (j + 1))

/-- K06C-facing first-pole closure statement derived from adjacent propagation. -/
def FirstPoleFinalTierClosureStatement {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord) : Prop :=
  ∀ p, p ∈ D.separatedProbe ->
    ∀ h, D.firstPoleSet p h ⊆ accIter D.finalTierIndex (D.T p h D.finalTierIndex)

/-- Extract the subset form from the pointwise propagation result interface. -/
theorem tierPropagation_subsetStatement {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} {D : TierCascadeData Probe Head Coord}
    (H : TierPropagationStatement D) :
    TierPropagationSubsetStatement D := by
  intro p hp h j hj τ hτ
  exact (H p hp h j τ hj hτ).mem_acc

/-! ## `lem:final-tier-blowup` -/

/-- Prop-valued statement corresponding to `lem:final-tier-blowup`. -/
def FinalTierBlowupStatement {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord) : Prop :=
  ∀ p, p ∈ D.separatedProbe ->
    ∀ h τ, τ ∈ D.T p h D.finalTierIndex ->
      τ ∈ D.stratum p h D.finalTierIndex
        ∧ IsPuncturedIsolated (D.singularSet p h) τ
        ∧ ∃ c : Coord,
          D.visibleCoordinate p h c
            ∧ BlowsUpAt (D.observableCoord p h c) τ

/-- The stratum-membership part of `lem:final-tier-blowup` is formal from
`lem:tier-in-stratum`. -/
theorem finalTier_mem_finalStratum {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord)
    {p : Probe} {h : Head} {τ : ℂ}
    (hτ : τ ∈ D.T p h D.finalTierIndex) :
    τ ∈ D.stratum p h D.finalTierIndex :=
  D.tier_in_stratum hτ

/-! ## `lem:chain-cascade` -/

/-- Formal adjacent-chain composition: if every tier accumulates on the next one,
then `q` adjacent steps place `T_j` inside `acc^q(T_{j+q})`. -/
theorem tier_subset_accIter_forward {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord)
    {p : Probe} {h : Head}
    (chain : ∀ j, j + 1 < D.depth -> D.T p h j ⊆ acc (D.T p h (j + 1))) :
    ∀ q j, j + q < D.depth -> D.T p h j ⊆ accIter q (D.T p h (j + q)) := by
  intro q
  induction q with
  | zero =>
      intro j _hj τ hτ
      simpa using hτ
  | succ q ih =>
      intro j hj τ hτ
      have hstep : j + 1 < D.depth := by omega
      have hnext : τ ∈ acc (D.T p h (j + 1)) :=
        chain j hstep hτ
      have hih :
          D.T p h (j + 1) ⊆ accIter q (D.T p h ((j + 1) + q)) :=
        ih (j + 1) (by omega)
      have hacc : τ ∈ acc (accIter q (D.T p h ((j + 1) + q))) :=
        acc_mono hih hnext
      simpa [accIter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hacc

/-- Formal inclusion of any tier into the final-tier accumulation envelope. -/
theorem tier_subset_final_accIter_of_chain {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord)
    {p : Probe} {h : Head}
    (chain : ∀ j, j + 1 < D.depth -> D.T p h j ⊆ acc (D.T p h (j + 1)))
    {j : Nat} (hj : j < D.depth) :
    D.T p h j ⊆ accIter (D.finalTierIndex - j) (D.T p h D.finalTierIndex) := by
  have hsum : j + (D.finalTierIndex - j) = D.finalTierIndex := by
    unfold finalTierIndex
    omega
  have hfinal_lt : j + (D.finalTierIndex - j) < D.depth := by
    simpa [hsum] using D.finalTierIndex_lt_depth
  have hforward :=
    D.tier_subset_accIter_forward (p := p) (h := h) chain
      (D.finalTierIndex - j) j hfinal_lt
  simpa [hsum] using hforward

/-- First-pole closure form consumed by the pole-transfer packet: propagation
places the first pole set in the iterated accumulation envelope of the final tier. -/
theorem firstPole_subset_final_accIter_of_propagation
    {Probe : Type uProbe} {Head : Type uHead} {Coord : Type uCoord}
    {D : TierCascadeData Probe Head Coord}
    (propagation : TierPropagationSubsetStatement D)
    {p : Probe} (hp : p ∈ D.separatedProbe) (h : Head) :
    D.firstPoleSet p h ⊆ accIter D.finalTierIndex (D.T p h D.finalTierIndex) := by
  have hclosure :
      D.T p h 0 ⊆
        accIter (D.finalTierIndex - 0) (D.T p h D.finalTierIndex) :=
    D.tier_subset_final_accIter_of_chain
      (p := p) (h := h)
      (fun j hj => propagation p hp h j hj)
      D.depth_pos
  simpa [Nat.sub_zero] using hclosure

/-- Adjacent propagation supplies the K06C-facing first-pole closure statement. -/
theorem firstPoleFinalTierClosureStatement_of_propagation
    {Probe : Type uProbe} {Head : Type uHead} {Coord : Type uCoord}
    {D : TierCascadeData Probe Head Coord}
    (propagation : TierPropagationSubsetStatement D) :
    FirstPoleFinalTierClosureStatement D := by
  intro p hp h
  exact firstPole_subset_final_accIter_of_propagation propagation hp h

/-- Pointwise propagation carries nonemptiness from one tier to its successor. -/
theorem tier_nonempty_succ_of_propagation {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} {D : TierCascadeData Probe Head Coord}
    (P : TierPropagationStatement D)
    {p : Probe} (hp : p ∈ D.separatedProbe) {h : Head} {j : Nat}
    (hj : j + 1 < D.depth) (hne : (D.T p h j).Nonempty) :
    (D.T p h (j + 1)).Nonempty := by
  rcases hne with ⟨τ, hτ⟩
  have hInf := (P p hp h j τ hj hτ).infinitely_many (by norm_num : (0 : ℝ) < 1)
  rcases hInf.nonempty with ⟨z, hz⟩
  exact ⟨z, hz.1⟩

/-- Adjacent pointwise propagation carries first-tier nonemptiness to the final tier. -/
theorem finalTier_nonempty_of_firstTier_nonempty_propagation
    {Probe : Type uProbe} {Head : Type uHead} {Coord : Type uCoord}
    {D : TierCascadeData Probe Head Coord}
    (P : TierPropagationStatement D)
    {p : Probe} (hp : p ∈ D.separatedProbe) (h : Head)
    (h0 : (D.T p h 0).Nonempty) :
    (D.T p h D.finalTierIndex).Nonempty := by
  have hnonempty : ∀ n, n < D.depth -> (D.T p h n).Nonempty := by
    intro n hn
    induction n with
    | zero =>
        exact h0
    | succ n ih =>
        exact tier_nonempty_succ_of_propagation P hp hn (ih (by omega))
  exact hnonempty D.finalTierIndex D.finalTierIndex_lt_depth

/-- Prop-valued statement corresponding to `lem:chain-cascade`. -/
def ChainCascadeStatement {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord) : Prop :=
  ∀ p, p ∈ D.separatedProbe ->
    ∀ h,
      (D.T p h 0).Nonempty
        ∧ (D.T p h 0).Infinite
        ∧ (∀ j, j < D.depth ->
            D.T p h j ⊆
              accIter (D.finalTierIndex - j) (D.T p h D.finalTierIndex))
        ∧ (D.T p h D.finalTierIndex).Nonempty

/-- Data sufficient to assemble the public chain-cascade statement without proving
the analytic propagation or final nonemptiness in this scaffold. -/
structure ChainCascadeData {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord) : Prop where
  firstTier_nonempty :
    ∀ p, p ∈ D.separatedProbe -> ∀ h, (D.T p h 0).Nonempty
  firstTier_infinite :
    ∀ p, p ∈ D.separatedProbe -> ∀ h, (D.T p h 0).Infinite
  propagation : TierPropagationSubsetStatement D
  finalTier_nonempty :
    ∀ p, p ∈ D.separatedProbe -> ∀ h, (D.T p h D.finalTierIndex).Nonempty

namespace ChainCascadeData

/-- Assemble `lem:chain-cascade` from packaged first-tier, propagation, and final-tier
nonemptiness interfaces. -/
theorem statement {Probe : Type uProbe} {Head : Type uHead} {Coord : Type uCoord}
    {D : TierCascadeData Probe Head Coord} (C : ChainCascadeData D) :
    ChainCascadeStatement D := by
  intro p hp h
  refine ⟨C.firstTier_nonempty p hp h, C.firstTier_infinite p hp h, ?_,
    C.finalTier_nonempty p hp h⟩
  intro j hj
  exact D.tier_subset_final_accIter_of_chain
    (fun i hi => C.propagation p hp h i hi) hj

/-- First-pole closure extracted directly from packaged chain-cascade data. -/
theorem firstPole_subset_final_accIter {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} {D : TierCascadeData Probe Head Coord}
    (C : ChainCascadeData D) {p : Probe} (hp : p ∈ D.separatedProbe) (h : Head) :
    D.firstPoleSet p h ⊆ accIter D.finalTierIndex (D.T p h D.finalTierIndex) :=
  firstPole_subset_final_accIter_of_propagation C.propagation hp h

/-- Packaged chain-cascade data supplies the K06C-facing first-pole closure statement. -/
theorem firstPoleFinalTierClosureStatement {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} {D : TierCascadeData Probe Head Coord}
    (C : ChainCascadeData D) :
    FirstPoleFinalTierClosureStatement D :=
  firstPoleFinalTierClosureStatement_of_propagation C.propagation

end ChainCascadeData

/-! ## Combined API package -/

/-- Public proof-hole-free API bundle for the `06b-step1-tier-cascade` packet. -/
structure TierCascadeAPI {Probe : Type uProbe} {Head : Type uHead}
    {Coord : Type uCoord} (D : TierCascadeData Probe Head Coord) : Prop where
  tier_local : TierLocalStatement D
  tier_propagation : TierPropagationStatement D
  final_tier_blowup : FinalTierBlowupStatement D
  chain_cascade : ChainCascadeStatement D

end TierCascadeData

end TransformerIdentifiability.NLayer.KHead.Step1
