import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.TierCascade
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.TierLocal
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.FinalBlowup

/-!
# K06B.C9 — concrete Step-1 tier-cascade API endpoint

This file performs the thin final assembly of packet K06B: it instantiates the
three reduced analytic payloads consumed by
`step1TierCascadeAPI_of_reduced_payloads` and produces the public concrete 06b
endpoint `step1TierCascadeAPI`.

* Payload 1 (`Step1TierLocalNormalFormPayloads`) is built from the two tier-local
  producers of `TierLocal.lean` and converted via `.to_analyticPayloads`.
* Payload 2 (`Step1TierPropagationAnalyticPayloads`) reuses the canonical
  sibling-avoidance producer and the dominance-persistence producer.
* Payload 3 (`Step1FinalTierVisibleBlowupPayloads`) is the already-proved
  `step1FinalTierVisibleBlowupPayloads`.
-/

namespace TransformerIdentifiability.NLayer.KHead.Step1

/-- The TeX-shaped tier-local normal-form payloads (Payload 1), assembled from the
two `_of_tier` producers of `TierLocal.lean`. -/
noncomputable def step1TierLocalNormalFormPayloads {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') :
    Step1TierLocalNormalFormPayloads hr H where
  successorPoleNormalForm_of_tier := fun p h j τ hj hτ hsucc =>
    step1SuccessorPoleNormalForm_of_tier p h hj hτ hsucc
  canonicalSiblingAvoidanceResult_of_tier := fun p h j τ hj hτ hsucc =>
    step1CanonicalSiblingAvoidanceResult_of_tierMembership p h hj hτ hsucc

/-- The analytic tier-propagation payloads (Payload 2): canonical sibling
avoidance plus radius-form dominance persistence. -/
noncomputable def step1TierPropagationAnalyticPayloads {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') :
    Step1TierPropagationAnalyticPayloads hr H where
  canonicalSiblingAvoidanceResult_of_tier := fun p h j τ hj hτ hsucc =>
    step1CanonicalSiblingAvoidanceResult_of_tierMembership p h hj hτ hsucc
  dominancePersistence_of_tier := fun p h j τ hj hτ hsucc =>
    step1DominancePersistence_of_tier (p := p) (h := h) hj hτ hsucc

/-- **K06B.C9 — the concrete Step-1 tier-cascade API endpoint.**  Assembled from
the three reduced analytic payloads via `step1TierCascadeAPI_of_reduced_payloads`. -/
theorem step1TierCascadeAPI {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r θ θ') :
    TierCascadeData.TierCascadeAPI (step1TierCascadeData hr H) :=
  step1TierCascadeAPI_of_reduced_payloads (hr := hr)
    (step1TierLocalNormalFormPayloads hr H).to_analyticPayloads
    (step1TierPropagationAnalyticPayloads hr H)
    (step1FinalTierVisibleBlowupPayloads hr H)

end TransformerIdentifiability.NLayer.KHead.Step1
