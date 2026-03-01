# d=1 Local Blocker: `Lambda`-Slice Route (Working Plan)

This note records a concrete alternative route for
`deferred_eventually_forward_eq_nhds_d1_holo` in
`PermutationFlow.lean`.

## 1. Target

At fixed prepared data `(w0, Γ, U)`:

- `w ∈ U -> w ∈ FT`,
- `w ∈ U -> Γ·(σ·w) ∈ FT`,

prove eventually near `w0`:

- `F(Γ·(σ·w)) = F(w)`.

## 2. Why midpoint/back-witness are not enough

Already formalized:

1. Midpoint branch `π * swap = σ` is obstructed in d=1.
2. Exact local back-witness `Λ·(σ·w)=w` is nongeneric in `n=2`.

So a viable route should avoid requiring either of those as local generic
conditions.

## 3. Slice formulation

For fixed `w`, define the index slice:

- `S_w := {Λ : CLG(1) | Λ·(σ·w) ∈ FT}`.

And define:

- `H(Λ, w) := F(Λ·(σ·w)) - F(w)`.

Preparedness gives `Γ ∈ S_w` for all `w ∈ U`.

If one can show (for `w` near `w0`) that `H(Λ, w)=0` at one anchor `Λ` in
`S_w`, then an invariance/connectedness propagation in `Λ` is a plausible path
to `H(Γ, w)=0`.

## 4. Existing ingredients

From current code:

1. `S_w` nonempty whenever `w ∈ permForwardOverlapSet`.
2. d=1 slice connectedness/preconnectedness infrastructure exists in
   `IndexSetD1.lean`.
3. Complex-Lorentz invariance machinery for FT-side evaluations is already in
   `PermutationFlow.lean`.

## 5. Missing formal ingredient

A local **slice anchor theorem** is still missing:

- for `w` near `w0`, produce some `Λ_anchor(w) ∈ S_w` with
  `F(Λ_anchor(w)·(σ·w)) = F(w)`.

Current hypotheses do not supply this directly.

This is the precise place where a new d=1 local gluing theorem is needed.

## 6. Practical coding implication

Until a slice-anchor theorem is formalized, the blocker remains:

- `deferred_eventually_forward_eq_nhds_d1_holo`.

But future work should target that one missing anchor mechanism rather than
revisiting midpoint implication neighborhoods or generic exact back-witness
existence.

## 7. Code status (2026-03-01)

Implemented in `PermutationFlow.lean`:

1. `forward_eq_of_slice_anchor_d1`
2. `eventually_forward_eq_nhds_of_eventually_slice_anchor_d1`

And `deferred_eventually_forward_eq_nhds_d1_holo` now ends with a single
explicit missing local anchor-existence step feeding this wrapper.

## 8. New IH-route infrastructure (2026-03-01)

To support the architectural route "IH on ET overlap + composition + identity
propagation", `PermutationFlow.lean` now includes:

1. `extendF_perm_eq_mul_on_overlap_intersection`
2. `extendF_perm_eq_on_connected_overlap_of_open_anchor`

These are not yet wired into the d=1 nontrivial branch replacement, but they
give the exact compositional and propagation primitives needed for that
refactor.
