import AnyLayerIdentifiabilityProof.NLayer.KHead.Core

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K-head dimension threshold (shared home for `dStar`)

`d_*(m,k) = max {2, k*m + 1}` was previously declared in both
`Induction/Peeling.lean` and `IdentifiabilityMain.lean` under the same namespace
`TransformerIdentifiability.NLayer.KHead`, which blocked co-importing the peeling
capstone (`Induction/InductionStep.lean`, via `Peeling`) into the main-theorem
bridge (`IdentifiabilityMain.lean`).  This is the same class of collision already
resolved for `relabelFirstLayer` and `consLayerPerm` (now living once in
`Induction/Relabel.lean`).  `dStar` and its basic Nat lemmas now live here, and
both files import this single canonical home.
-/

/-- TeX `d_*(m,k) = max {2, k*m + 1}`. -/
def dStar (m k : Nat) : Nat :=
  max 2 (k * m + 1)

theorem two_le_dStar (m k : Nat) : 2 ≤ dStar m k :=
  le_max_left _ _

end TransformerIdentifiability.NLayer.KHead
