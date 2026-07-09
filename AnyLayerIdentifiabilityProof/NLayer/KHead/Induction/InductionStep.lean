import AnyLayerIdentifiabilityProof.NLayer.KHead.Induction.PeelingExport
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.PoleTransfer
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.Hypotheses
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.SaturatedFirstValues

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.KHead

noncomputable section

/-!
# K03C.M5 wiring + K03A recursion driver — the depth-induction capstone

This module wires the already-proved pieces of the k-head identifiability proof
into a single induction step and, from it, a `Nat`-recursion depth driver.  The
whole depth induction is reduced to one honest boundary input, the K07C Step-2
first-layer value matching (`prop:first-V`).

## Boundaries (the only unproven inputs)

Everything below is discharged from proved lemmas *except*:

* `hV : firstLayerValuesMatchedForPeeling θ θ' (step1CommonFirstGates hr H).sigma`
  — the K07C value endpoint for the canonical Step-1 first-attention
  permutation.  It fixes only the *value* equalities for the single canonical
  permutation `(step1CommonFirstGates hr H).sigma`; it is not a restatement of
  the conclusion (which additionally carries attention matching + uniqueness +
  global equality).
* For the single step, `tailMatching : LayerwiseMatchingConclusion (Fin.tail θ)
  (Fin.tail θ')` — the tail induction hypothesis.  The `Nat`-recursion driver
  *eliminates* this hypothesis by recursing on depth.

## The quantified `hV`-family for the recursion (`LayerValuesMatchableFromAttention`)

The driver threads value matching at *every* depth by quantifying over layers and
over attention-matching permutations:

  `∀ l σ, (attention of θ at l matches θ' via σ) → (values of θ at l match θ' via σ)`.

This is exactly K07C's `prop:first-V` re-read at every layer, it is `Fin.tail`
hereditary (so it descends cleanly through the peeling), and — crucially — it is
*omega-independent*, which is what lets it thread through a recursion whose
sub-problem input sets are produced only during peeling.
-/

/-! ## Global-equality bridges (defeq twins) -/

/-- Bridge: Step-1's `GlobalTransformerEquality` is K03C's `TransformerEqualGlobally`.
Both unfold to `∀ X, transformer θ X = transformer θ' X` at sequence length
`seqLength r`. -/
theorem transformerEqualGlobally_of_globalTransformerEquality {r m k d : Nat}
    {θ θ' : Params m k d} (h : Step1.GlobalTransformerEquality r θ θ') :
    TransformerEqualGlobally (r := r) θ θ' :=
  fun X => h X

/-- Bridge: Step-1's `GlobalTransformerEquality` is K08's
`TransformerAgreementEverywhere` at `T = seqLength r`. -/
theorem transformerAgreementEverywhere_of_globalTransformerEquality {r m k d : Nat}
    {θ θ' : Params m k d} (h : Step1.GlobalTransformerEquality r θ θ') :
    TransformerAgreementEverywhere (T := seqLength r) θ θ' :=
  fun X => h X

/-! ## Standing hypotheses built from the invariant ingredients -/

/-- Assemble the Step-1 standing hypotheses `Step1StandingHypotheses r θ θ'` for a
depth-`m+2` pair from the invariant ingredients: recursive genericity of the
target `θ'`, a nonempty open input set, and open-set transformer equality.

* `target_regular` / `target_cascade` come from the target's `CurrentGenericClauses`;
* `chains` are extracted from the cascade certificate;
* `global_equality` is the open-set-to-global output `lem_open_set_to_global`
  (the analytic continuation core), so no global equality is *assumed*. -/
noncomputable def standingHypothesesOfOpenSet {m k d r : Nat} (hr : 1 < r)
    {θ θ' : Params (m + 2) k d}
    (hgen : RecursiveGeneric r (m + 2) k d θ')
    {omega : Set (NetworkInput r d)}
    (homega : NonemptyOpenInputSet omega)
    (heq : TransformerEqualOn (r := r) θ θ' omega) :
    Step1.Step1StandingHypotheses r θ θ' where
  later_depth_pos := Nat.succ_pos m
  seq_pos := by omega
  target_regular := (recursiveGeneric_current hgen).regular
  target_cascade := (recursiveGeneric_current hgen).cascade
  chains :=
    Step1.step1ChainChoicesOfCascadeCertificate (recursiveGeneric_current hgen).cascade
  global_equality :=
    (lem_open_set_to_global (by omega) θ θ' omega homega heq).global_equal

/-! ## The shared peeling primitive -/

/-- Run one Step-3 peeling step from standing hypotheses `H` and the K07C value
endpoint `hV`.

This is the single primitive shared by the induction step and the depth driver.
It assembles `PeelingStepInputs` — `first_layer` via the proved same-`σ` builder
`firstLayerPeelingData_of_valuesMatched` (its only unproven input is `hV`),
`local_open_layer` via the proved `lem_local_open_layer`, `global_eq` via the
standing global equality — and applies the proved `prop_peeling_step`. -/
noncomputable def peelingResultOfStanding {m k d r : Nat} (hr : 1 < r)
    {θ θ' : Params (m + 2) k d}
    (hgen : RecursiveGeneric r (m + 2) k d θ')
    (H : Step1.Step1StandingHypotheses r θ θ')
    (hV : firstLayerValuesMatchedForPeeling θ θ'
      (Step1.step1CommonFirstGates hr H).sigma) :
    PeelingStepResult r θ θ' :=
  Classical.choice
    (prop_peeling_step r θ θ'
      { target_generic := hgen
        global_eq := transformerAgreementEverywhere_of_globalTransformerEquality H.global_equality
        first_layer := firstLayerPeelingData_of_valuesMatched hr H hV
        local_open_layer := lem_local_open_layer })

/-! ## TASK 1 — the single induction step (conditional reduction) -/

/-- **K03C.M5 single-step wiring (depth `m+2`).**

From the invariant ingredients (`1 < r`, recursive genericity, a nonempty open
input set, open-set transformer equality), the honest K07C boundary `hV`, and the
tail induction hypothesis `tailMatching`, produce the C1–C4 tail conclusion.

Every ingredient other than `hV` and `tailMatching` is discharged from proved
lemmas:
* `hglobal := standingHypothesesOfOpenSet …` (via `lem_open_set_to_global`);
* the peeling output `P` via `peelingResultOfStanding` (proved
  `prop_peeling_step` + `firstLayerPeelingData_of_valuesMatched` + proved
  `lem_local_open_layer`);
* `D := firstLayerTailReductionData_of_peelingStepResult P` (proved adapter);
* `huniq0 := P.reduced.peeling.attention_unique` (proved first-attention
  uniqueness);
* the final assembly `openSetInductionInvariantTailConclusion_of_data` (proved
  core).

Thus `hV` and `tailMatching` are the only unproven inputs; the wiring does real
work (peel the first layer, reduce to the tail, reassemble). -/
noncomputable def openSetInductionInvariantTailConclusion_step {m k d r : Nat} (hr : 1 < r)
    {θ θ' : Params (m + 2) k d}
    (hgen : RecursiveGeneric r (m + 2) k d θ')
    {omega : Set (NetworkInput r d)}
    (homega : NonemptyOpenInputSet omega)
    (heq : TransformerEqualOn (r := r) θ θ' omega)
    (hV : firstLayerValuesMatchedForPeeling θ θ'
      (Step1.step1CommonFirstGates hr (standingHypothesesOfOpenSet hr hgen homega heq)).sigma)
    (tailMatching : LayerwiseMatchingConclusion (Fin.tail θ) (Fin.tail θ')) :
    OpenSetInductionInvariantTailConclusion r θ θ' :=
  let H := standingHypothesesOfOpenSet hr hgen homega heq
  let P := peelingResultOfStanding hr hgen H hV
  openSetInductionInvariantTailConclusion_of_data (by omega)
    (transformerEqualGlobally_of_globalTransformerEquality H.global_equality)
    (firstLayerTailReductionData_of_peelingStepResult P)
    P.reduced.peeling.attention_unique
    tailMatching

/-! ## TASK 2 — the quantified `hV`-family and the depth-recursion driver -/

/-- **The `hV`-family for the depth recursion (K07C, quantified).**

At every layer `l`, any first-layer-attention-matching permutation `σ` also
matches the values.  This is the honest K07C `prop:first-V` content, read at
every layer, stated with no reference to any input set (hence hereditary and
threadable through a recursion whose sub-problem input sets appear only during
peeling). -/
def LayerValuesMatchableFromAttention {L k d : Nat} (θ θ' : Params L k d) : Prop :=
  ∀ (l : Fin L) (sigma : Equiv.Perm (Fin k)),
    (∀ h, attentionMatrix θ l (sigma h) = attentionMatrix θ' l h) →
    (∀ h, valueMatrix θ l (sigma h) = valueMatrix θ' l h)

/-- The `hV`-family restricts to the tail (drop layer `0`). -/
theorem LayerValuesMatchableFromAttention.tail {L k d : Nat}
    {θ θ' : Params (L + 1) k d}
    (h : LayerValuesMatchableFromAttention θ θ') :
    LayerValuesMatchableFromAttention (Fin.tail θ) (Fin.tail θ') := by
  intro l sigma hatt h0
  have hatt' : ∀ hh : Fin k,
      attentionMatrix θ l.succ (sigma hh) = attentionMatrix θ' l.succ hh := by
    intro hh
    simpa [Fin.tail] using hatt hh
  simpa [Fin.tail] using h l.succ sigma hatt' h0

/-- Extract the first-layer K07C value endpoint `hV` for the canonical Step-1
first-attention permutation out of the quantified family. -/
theorem firstLayerValuesMatchedForPeeling_of_family {m k d r : Nat} (hr : 1 < r)
    {θ θ' : Params (m + 2) k d}
    (H : Step1.Step1StandingHypotheses r θ θ')
    (hVfam : LayerValuesMatchableFromAttention θ θ') :
    firstLayerValuesMatchedForPeeling θ θ' (Step1.step1CommonFirstGates hr H).sigma :=
  hVfam 0 (Step1.step1CommonFirstGates hr H).sigma
    (Step1.step1CommonFirstGates hr H).attention_eq

/-- **K03A depth-recursion driver.**

By `Nat` recursion on the depth `n`, produce the C1–C3 open-set invariant
conclusion for every depth `n + 1` from:
* `1 < r`, recursive genericity of the target, a nonempty open input set, open-set
  transformer equality — the ordinary invariant ingredients; and
* the single quantified `hV`-family `LayerValuesMatchableFromAttention θ θ'`
  (the K07C boundary, threaded at every depth).

* Base (`n = 0`, depth one): the proved unconditional base case
  `OpenSetInductionInvariantConclusion.depth_one`.
* Step (`n + 1`, depth `n + 2`): peel the first layer via `peelingResultOfStanding`
  (its `hV` supplied from the family by `firstLayerValuesMatchedForPeeling_of_family`),
  recurse on the reduced tail sub-problem — whose input set is the peeled
  `OmegaTail` and whose family is `hVfam.tail` — and reassemble with the proved
  core `openSetInductionInvariantTailConclusion_of_data`, keeping the `.base`
  component. -/
noncomputable def openSetInductionInvariantConclusion_driver {k d r : Nat} (hr : 1 < r)
    (hd : 2 ≤ d) :
    ∀ (n : Nat) (θ θ' : Params (n + 1) k d),
      RecursiveGeneric r (n + 1) k d θ' →
      ∀ (omega : Set (NetworkInput r d)),
        NonemptyOpenInputSet omega →
        TransformerEqualOn (r := r) θ θ' omega →
        OpenSetInductionInvariantConclusion r θ θ'
  | 0, _θ, _θ', hgen, _omega, homega, heq =>
      OpenSetInductionInvariantConclusion.depth_one hr hgen homega heq
  | n + 1, θ, θ', hgen, _omega, homega, heq =>
      let H := standingHypothesesOfOpenSet hr hgen homega heq
      let hV :
          firstLayerValuesMatchedForPeeling θ θ' (Step1.step1CommonFirstGates hr H).sigma :=
        prop_first_V_of_standing hr H hgen hd
      let P := peelingResultOfStanding hr hgen H hV
      let tailConcl :=
        openSetInductionInvariantConclusion_driver hr hd n (Fin.tail θ) (Fin.tail θ')
          (recursiveGeneric_tail hgen) P.reduced.OmegaTail
          ⟨P.reduced.omegaTail_open, P.reduced.omegaTail_nonempty⟩
          (transformerEqualOn_of_agreementOn P.reduced.tail_eq_on_unrelabelled)
      (openSetInductionInvariantTailConclusion_of_data (by omega)
        (transformerEqualGlobally_of_globalTransformerEquality H.global_equality)
        (firstLayerTailReductionData_of_peelingStepResult P)
        P.reduced.peeling.attention_unique
        tailConcl.matching).base

/-- **K03A driver (all depths, C1–C3).**  The recursion above, packaged with
implicit depth arguments: for every depth `m + 1`, the invariant ingredients plus
the quantified `hV`-family give the C1–C3 conclusion, with no tail hypothesis. -/
noncomputable def openSetInductionInvariant_of_valuesMatchable {m k d r : Nat} (hr : 1 < r)
    {θ θ' : Params (m + 1) k d}
    (hgen : RecursiveGeneric r (m + 1) k d θ')
    {omega : Set (NetworkInput r d)}
    (homega : NonemptyOpenInputSet omega)
    (heq : TransformerEqualOn (r := r) θ θ' omega)
    (hd : 2 ≤ d) :
    OpenSetInductionInvariantConclusion r θ θ' :=
  openSetInductionInvariantConclusion_driver hr hd m θ θ' hgen omega homega heq

/-- **K03A driver (depths `m + 2`, C1–C4 tail form).**  Same hypotheses as the
C1–C3 driver, delivering the full tail conclusion (base + first-layer
tail-reduction) for depth at least two.  Peels once, obtains the tail matching
from the C1–C3 driver on the reduced tail, and reassembles with the proved core. -/
noncomputable def openSetInductionInvariantTail_of_valuesMatchable {m k d r : Nat} (hr : 1 < r)
    {θ θ' : Params (m + 2) k d}
    (hgen : RecursiveGeneric r (m + 2) k d θ')
    {omega : Set (NetworkInput r d)}
    (homega : NonemptyOpenInputSet omega)
    (heq : TransformerEqualOn (r := r) θ θ' omega)
    (hd : 2 ≤ d) :
    OpenSetInductionInvariantTailConclusion r θ θ' :=
  let H := standingHypothesesOfOpenSet hr hgen homega heq
  let hV :
      firstLayerValuesMatchedForPeeling θ θ' (Step1.step1CommonFirstGates hr H).sigma :=
    prop_first_V_of_standing hr H hgen hd
  let P := peelingResultOfStanding hr hgen H hV
  let tailConcl :=
    openSetInductionInvariantConclusion_driver hr hd m (Fin.tail θ) (Fin.tail θ')
      (recursiveGeneric_tail hgen) P.reduced.OmegaTail
      ⟨P.reduced.omegaTail_open, P.reduced.omegaTail_nonempty⟩
      (transformerEqualOn_of_agreementOn P.reduced.tail_eq_on_unrelabelled)
  openSetInductionInvariantTailConclusion_of_data (by omega)
    (transformerEqualGlobally_of_globalTransformerEquality H.global_equality)
    (firstLayerTailReductionData_of_peelingStepResult P)
    P.reduced.peeling.attention_unique
    tailConcl.matching

/-! ## Connection to the bundled statement surfaces -/

/-- The dimension-gate descent `d_*(m+1, k) ≤ d_*(m+2, k)`.  The driver does not
need it (genericity, not a bare gate, carries the dimension facts through the
recursion); it is recorded for the bundled statement surfaces, whose
`dimension_gate` field lives at the current depth. -/
theorem dStar_succ_le {m k : Nat} : dStar (m + 1) k ≤ dStar (m + 2) k := by
  have hmul : k * (m + 1) ≤ k * (m + 2) := Nat.mul_le_mul (le_refl k) (by omega)
  have h : k * (m + 1) + 1 ≤ k * (m + 2) + 1 := by omega
  simp only [dStar]
  exact max_le_max le_rfl h

/-- **`thm-open-induction-invariant.S` (C1–C3), discharged from the `hV`-family.**
Consuming the full bundled hypothesis package (including its `dimension_gate`),
the driver delivers the invariant conclusion for depth `n + 1`. -/
noncomputable def thm_open_induction_invariant_of_valuesMatchable {dStar : DimensionThreshold}
    {k d r : Nat} {n : Nat}
    {θ θ' : Params (n + 1) k d} {omega : Set (NetworkInput r d)}
    (hd : 2 ≤ d)
    (H : OpenSetInductionInvariantHypotheses dStar r θ θ' omega) :
    OpenSetInductionInvariantConclusion r θ θ' :=
  openSetInductionInvariant_of_valuesMatchable (by have := H.rate_ge_two; omega)
    H.target_generic H.nonemptyOpen H.equal_on hd

/-- **`thm-open-induction-invariant-tail.S` (C1–C4), discharged from the
`hV`-family.**  Same, in the C4 tail form for depth at least two. -/
noncomputable def thm_open_induction_invariant_tail_of_valuesMatchable
    {dStar : DimensionThreshold} {k d r : Nat} {n : Nat}
    {θ θ' : Params (n + 2) k d} {omega : Set (NetworkInput r d)}
    (hd : 2 ≤ d)
    (H : OpenSetInductionInvariantHypotheses dStar r θ θ' omega) :
    OpenSetInductionInvariantTailConclusion r θ θ' :=
  openSetInductionInvariantTail_of_valuesMatchable (by have := H.rate_ge_two; omega)
    H.target_generic H.nonemptyOpen H.equal_on hd

end

end TransformerIdentifiability.NLayer.KHead
