import AnyLayerIdentifiabilityProof.NLayer.KHead.Core

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.KHead

/-!
# Canonical first-layer relabeling

This file is the single canonical home for the first-layer paired relabeling
used by the Step 3 peeling (`Induction/Peeling.lean`) and the induction invariant
(`Induction/Invariant.lean`).  Both files previously declared their own
`relabelFirstLayer` (plus `_zero`, `_succ`, and a tail-invariance lemma) in the
same namespace `TransformerIdentifiability.NLayer.KHead`, which made importing
both into a single module (the K08 → K03C adapter) impossible.  The declarations
now live here once and are shared by both files.
-/

noncomputable section

/-- Paired relabeling of the first layer by a target-to-source permutation.

At first-layer head `h`, the relabeled parameter stores the original head
`sigma h`.  Deeper layers are left unchanged. -/
def relabelFirstLayer {m k d : Nat} (theta : Params (m + 1) k d)
    (sigma : Equiv.Perm (Fin k)) : Params (m + 1) k d :=
  fun l h => if l = 0 then theta 0 (sigma h) else theta l h

@[simp]
theorem relabelFirstLayer_zero {m k d : Nat} (theta : Params (m + 1) k d)
    (sigma : Equiv.Perm (Fin k)) (h : Fin k) :
    relabelFirstLayer theta sigma 0 h = theta 0 (sigma h) := by
  simp [relabelFirstLayer]

@[simp]
theorem relabelFirstLayer_succ {m k d : Nat} (theta : Params (m + 1) k d)
    (sigma : Equiv.Perm (Fin k)) (l : Fin m) (h : Fin k) :
    relabelFirstLayer theta sigma l.succ h = theta l.succ h := by
  simp [relabelFirstLayer]

/-- First-layer relabeling leaves the tail tuple unchanged. -/
@[simp]
theorem relabelFirstLayer_tail {m k d : Nat} (theta : Params (m + 1) k d)
    (sigma : Equiv.Perm (Fin k)) :
    Fin.tail (relabelFirstLayer theta sigma) = Fin.tail theta := by
  funext l h
  simp [Fin.tail]

/-! ## Canonical `consLayerPerm` for layerwise permutation tuples

`consLayerPerm` prepends a first-layer permutation onto a tail tuple of
permutations.  Like `relabelFirstLayer`, it was previously declared separately in
both `Induction/Peeling.lean` and `Induction/Invariant.lean` (same namespace,
same name), which made co-importing the two modules impossible.  It now lives
here once and is shared by both.  The tail-tuple argument is stated with the raw
function type `Fin m → Equiv.Perm (Fin k)`, definitionally equal to the
`LayerPermutations m k` abbreviation used in `Induction/Invariant.lean`. -/

/-- Add the first-layer permutation in front of a tail tuple of permutations. -/
def consLayerPerm {m k : Nat} (sigma0 : Equiv.Perm (Fin k))
    (tailSigma : Fin m → Equiv.Perm (Fin k)) :
    Fin (m + 1) → Equiv.Perm (Fin k) :=
  Fin.cases sigma0 tailSigma

@[simp]
theorem consLayerPerm_zero {m k : Nat} (sigma0 : Equiv.Perm (Fin k))
    (tailSigma : Fin m → Equiv.Perm (Fin k)) :
    consLayerPerm sigma0 tailSigma 0 = sigma0 :=
  rfl

@[simp]
theorem consLayerPerm_succ {m k : Nat} (sigma0 : Equiv.Perm (Fin k))
    (tailSigma : Fin m → Equiv.Perm (Fin k)) (l : Fin m) :
    consLayerPerm sigma0 tailSigma l.succ = tailSigma l :=
  rfl

end

end TransformerIdentifiability.NLayer.KHead
