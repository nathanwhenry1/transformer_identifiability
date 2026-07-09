# Identifiability of attention-only transformers with k heads per layer

Consider an `L`-layer attention-only transformer with causal masking, `k` attention
heads per layer, and additive skip connections. Each layer `ℓ` acts on a `d × T`
activation matrix `X` by

```
X ↦ X + ∑_{h=1}^{k} V_{ℓ,h} · X · softmax_causal(Xᵀ · A_{ℓ,h} · X),
```

so the network is determined by its parameters `θ = (V_{ℓ,h}, A_{ℓ,h})`, a point of
`((ℝ^{d×d})²)^{L·k}`.

**Question.** To what extent is `θ` determined by the input-output map `X ↦ TF_θ(X)`?
The head sum is symmetric, so relabelling the `k` heads of any layer leaves the network
unchanged: for `k ≥ 2`, `θ` can be recovered at best up to a per-layer permutation of
its heads.

## Result formalized here

For depth `L ≥ 1`, heads `k ≥ 1`, context multiplicity `r ≥ 2` (sequence length
`r + 1`), and dimension `d ≥ d*(L, k) = max(2, k·L + 1)`, there is an explicit
Lebesgue-null set `N` of parameters — a finite union of proper algebraic subsets, cut
out by explicit polynomial nonvanishing conditions — such that every `θ'` outside `N`
is identified, among *all* parameters and up to a per-layer permutation of its heads,
by the input-output map of its network. That is, if `TF_θ(X) = TF_{θ'}(X)` for all
inputs `X`, then there are permutations `σ_ℓ ∈ S_k` with `θ_{ℓ,h} = θ'_{ℓ,σ_ℓ(h)}` for
every layer `ℓ` and head `h`.

The converse is also formalized: parameters agreeing up to per-layer head permutations
compute the same network on every input, so the per-layer head permutations are exactly
the symmetry group of the realization map. The dimension threshold is linear in `L` and
`k`; for `k = 1` it reads `d ≥ L + 1`.

The exact Lean targets are `TransformerIdentifiability.identifiability_perm` (forward)
and `TransformerIdentifiability.transformerK_eq_of_permute` (converse); the all-depth
k-head core is `TransformerIdentifiability.NLayer.KHead.thm_main_statement_holds`. The
single-head theorem `TransformerIdentifiability.identifiability`, on which this
development builds, is included as well.

The proof is by induction on depth: complex-analytic continuation in an
inverse-temperature variable identifies the innermost attention matrices — now `k`
competing Laurent branches per tier, matched head-by-head through a dominance and
window-avoidance analysis of the pole arcs — up to a head permutation; saturated limits
of the attention gates and a structural trichotomy recover the value matrices, and a
peeling step relabels the matched heads and descends to depth `L − 1`.
