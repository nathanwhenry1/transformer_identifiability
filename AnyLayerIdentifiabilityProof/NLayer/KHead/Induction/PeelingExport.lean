import AnyLayerIdentifiabilityProof.NLayer.KHead.Induction.Peeling
import AnyLayerIdentifiabilityProof.NLayer.KHead.Induction.Invariant

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.KHead

noncomputable section

/-!
# K08.M6 — reduced-tail export from peeling (K08) into the induction invariant (K03C)

This adapter converts a Step-3 peeling output
(`PeelingStepResult`, K08 / `Induction/Peeling.lean`) into the C4 tail-reduction
package consumed by the open-set induction invariant
(`FirstLayerTailReductionData`, K03C / `Induction/Invariant.lean`).

Both `Peeling.lean` and `Invariant.lean` are imported together; the previously
duplicated `relabelFirstLayer` now lives in `Induction/Relabel.lean`, so the two
files coimport without clashing.

The two endpoints line up cleanly:

* **Depth reindex.** K08 states `PeelingStepResult` at `Params (m + 1) k d`; K03C
  states `FirstLayerTailReductionData` at `Params (m + 2) k d`.  For a pair
  `θ θ' : Params (m + 2) k d`, elaboration unifies K08's depth parameter to
  `m + 1`, so its tail lives at depth `m + 1` and its `target_tail_generic`
  reads `RecursiveGeneric r (m + 1) k d (tailParams θ')`, definitionally the
  `RecursiveGeneric r (m + 1) k d (Fin.tail θ')` that K03C asks for
  (`tailParams = Fin.tail`).

* **Predicate bridge (endgame bridge #5).** K08's `TransformerAgreementOn`
  (generic sequence length `T`) and K03C's `TransformerEqualOn`
  (`T = seqLength r`, i.e. `NetworkInput r d`) are, at `T = seqLength r`, the
  same proposition: both say `∀ X ∈ Ω, transformer θ₁ X = transformer θ₂ X`
  (set membership `X ∈ Ω` unfolds to the application `Ω X`).  We record the
  one-line bridge `transformerEqualOn_of_agreementOn` explicitly.
-/

/-- **Endgame bridge #5.** At sequence length `T = seqLength r`, K08's
`TransformerAgreementOn` and K03C's `TransformerEqualOn` are the same statement.
The two definitions unfold to `∀ X ∈ Ω, transformer θ X = transformer θ' X`; the
only cosmetic difference is `X ∈ Ω` (set membership) versus `Ω X` (application),
which are definitionally equal for `Set`. -/
theorem transformerEqualOn_of_agreementOn {r m k d : Nat}
    {theta theta' : Params m k d} {omega : Set (NetworkInput r d)}
    (h : TransformerAgreementOn (T := seqLength r) theta theta' omega) :
    TransformerEqualOn (r := r) theta theta' omega :=
  fun X hX => h X hX

/-- **K08.M6 export adapter.**

Turn a single Step-3 peeling output `PeelingStepResult r θ θ'` (K08) into the C4
tail-reduction package `FirstLayerTailReductionData r θ θ' σ` (K03C), where
`σ = P.reduced.peeling.sigma` is the first-layer permutation extracted by
peeling.

Every field of the target is supplied directly from the peeling output; no
local-open / reduced-tail argument is rebuilt:

* `omega_tail`, openness, nonemptiness come from `P.reduced`;
* `target_tail_generic := P.target_tail_generic`
  (`RecursiveGeneric r (m + 1) k d (tailParams θ')`, defeq to the `Fin.tail`
  form);
* `first_layer_equal := P.reduced.peeling.relabeled_firstLayer_head_eq`;
* the tail equality is the *unchanged source tail* comparison
  `P.reduced.tail_eq_on_unrelabelled` (K08 already discharges the first-layer
  relabeling on the tail), pushed through the predicate bridge above.  The
  constructor `of_source_tail_equal_on` re-installs the `relabelFirstLayer`
  wrapper via `relabelFirstLayer_tail`.
-/
def firstLayerTailReductionData_of_peelingStepResult
    {m k d r : Nat} {theta theta' : Params (m + 2) k d}
    (P : PeelingStepResult r theta theta') :
    FirstLayerTailReductionData r theta theta' P.reduced.peeling.sigma :=
  FirstLayerTailReductionData.of_source_tail_equal_on
    (hopen := P.reduced.omegaTail_open)
    (hnonempty := P.reduced.omegaTail_nonempty)
    (htarget := P.target_tail_generic)
    (hfirst := P.reduced.peeling.relabeled_firstLayer_head_eq)
    (htail := transformerEqualOn_of_agreementOn P.reduced.tail_eq_on_unrelabelled)

end

end TransformerIdentifiability.NLayer.KHead
