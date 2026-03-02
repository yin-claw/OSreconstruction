# d=1, n=2 Blocker Audit (No Assumption Smuggling)

Last updated: 2026-03-02 (late)

Order lock in force:
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/WORK_ORDER_LOCK.md`.

This note isolates the current blocker concern:

- `blocker_eventually_forward_eq_on_prepared_nhds_d1_adjSwap_deferred`

specialized to:

- `d = 1`, `n = 2`, `tau = swap(0,1)`.

As of 2026-03-02, the production blocker statement has been narrowed to the
adjacent-swap case only (no arbitrary-permutation local blocker in this slot).
There is also an explicit derived existential wrapper:

- `blocker_eventually_slice_anchor_on_prepared_nhds_d1_adjSwap_n2`

and an explicit deterministic wrapper:

- `blocker_eventually_forward_eq_on_prepared_nhds_d1_adjSwap_n2`.
- `blocker_eventually_extendF_base_eq_on_prepared_nhds_d1_adjSwap_n2`.

so the `n=2` theorem can be attacked directly.

Canonical `swap(0,1)` wrappers are now available (same file) to avoid
`i/hi` plumbing in small-`n` proofs:

- `blocker_eventually_extendF_base_eq_on_prepared_nhds_d1_swap01_n2`
- `blocker_eventually_forward_eq_on_prepared_nhds_d1_swap01_n2`
- `blocker_eventually_slice_anchor_on_prepared_nhds_d1_swap01_n2`
- `blocker_eventually_extendF_base_eq_iff_forward_eq_on_prepared_nhds_d1_swap01_n2`

The goal is to verify whether the theorem is correctly asserted under the
current hypotheses, before generalizing to `n=3` and `n>=4`.

## 0. Production split status (`PermutationFlowBlockers.lean`)

The core deferred theorem

- `blocker_eventually_slice_anchor_on_prepared_nhds_d1_nontrivial`

is now explicitly split by size in its proof skeleton:

- branch A: `n = 2` (primary target),
- branch B: `n = 3`,
- branch C: `4 ≤ n`.

This removes ambiguity about what is being deferred and enforces the work order:
we can focus on branch A without mixing in `n=3`/`n>=4` geometry.

In the current code, branch A (`n=2`) is reduced to a two-step anchor split:

- proved geometric nonemptiness with an anchor already in `FT`:
  `blocker_adjSwapExtendedOverlap_nonempty_d1_swap01_n2`,
- proved geometric preparation from a fixed anchor:
  `blocker_exists_prepared_nhds_at_anchor_adjSwap_d1_swap01_n2`,
- proved prepared-domain fixed-witness obstruction:
  `blocker_not_eventually_unswapped_forward_on_prepared_nhds_at_anchor_adjSwap_d1_swap01_n2`,
- proved prepared-neighborhood deterministic base theorem:
  `blocker_eventuallyExtendFBaseEq_on_prepared_nhds_at_anchor_adjSwap_d1_swap01_n2`,
- via explicit proved reducer:
  `blocker_eventuallyExtendFBaseEq_on_prepared_nhds_at_anchor_adjSwap_d1_swap01_n2_reduce`,
- and proved converse bridge plus iff packaging:
  `blocker_eventuallyEq_on_adjSwapExtendedOverlap_nhds_at_transformed_anchor_d1_swap01_n2_of_base`,
  `blocker_eventuallyExtendFBaseEq_iff_eventuallyEq_at_transformed_anchor_adjSwap_d1_swap01_n2`,
- with deferred transformed-anchor ET-overlap local core:
  `blocker_eventuallyEq_on_adjSwapExtendedOverlap_nhds_at_transformed_anchor_d1_swap01_n2_deferred`,
- proved transformed-anchor ET-overlap local theorem:
  `blocker_eventuallyEq_on_adjSwapExtendedOverlap_nhds_at_transformed_anchor_d1_swap01_n2`,
- proved reduction of that deterministic theorem to local ET-overlap equality at
  transformed anchor `y0 = Γ·(swap·z0)`:
  `blocker_eventuallyExtendFBaseEq_on_prepared_nhds_at_anchor_adjSwap_d1_swap01_n2_of_eventuallyEq_at_transformed_anchor`,
- proved existential local slice-anchor wrapper from that deterministic theorem:
  `blocker_eventuallySliceAnchor_on_prepared_nhds_at_anchor_adjSwap_d1_swap01_n2`.

The former existential wrapper

- `blocker_eventuallyEq_anchor_adjSwap_d1_swap01_n2`

is now derived with no `sorry` from those ingredients.

Also now proved (no `sorry`):

- `blocker_eventuallyForwardEq_on_prepared_nhds_at_anchor_adjSwap_d1_swap01_n2`,
- `blocker_eventuallyEq_on_prepared_nhds_at_anchor_adjSwap_d1_swap01_n2`,

where:

- forward equality is derived directly from the deferred deterministic base
  equality core by Lorentz/`extendF` transport, and
- local `extendF` equality is then derived from local forward equality.

and a canonical permutation normalization lemma

- `fin2_perm_ne_one_eq_swap01`

The global overlap theorem

- `blocker_extendF_perm_overlap_d1_swap01_n2`

is now proved (gluing shell closed) from:

1. connectedness transfer (`seed -> forward-overlap -> adjSwap ET-overlap`)
2. identity-theorem propagation (`extendF_perm_eq_on_connectedDomain_of_openSubset`)
3. the deferred prepared-neighborhood slice-anchor theorem above (via wrappers,
   then local forward and `extendF` conversions).

Also proved as explicit infrastructure (no `sorry`):

- `blocker_eventually_extendF_base_eq_on_prepared_nhds_d1_nontrivial_n2_of_global_overlap`,
- `blocker_eventuallyExtendFBaseEq_on_prepared_nhds_at_anchor_adjSwap_d1_swap01_n2_of_global_overlap`.

These package the exact deterministic local base equality that follows once
global `extendF` overlap invariance is available.

The transformed-anchor reduction above is independent from global overlap and
makes the local analytic target explicit: it is enough to know local ET-overlap
equality near `Γ·(swap·z0)` to recover the prepared-neighborhood base identity
near `z0`.

The arbitrary nontrivial-`τ` form

- `blocker_extendF_perm_overlap_d1_n2`

is derived by rewriting `τ = swap(0,1)`. Then the local
prepared-neighborhood conclusion is proved from global overlap identity
(with fixed witness `Γ`) by a short `extendF`/Lorentz-invariance chain.

The remaining non-`n=2` local branches are now isolated as separate deferred
core lemmas in `PermutationFlowBlockers.lean`:

- `blocker_eventually_slice_anchor_on_prepared_nhds_d1_nontrivial_n3_core`
- `blocker_eventually_slice_anchor_on_prepared_nhds_d1_nontrivial_nge4_core`

So the main nontrivial dispatcher theorem no longer has inline branch sorrys.

Implementation note:

- `PermutationFlowBlockers.lean` now imports
  `OSReconstruction.ComplexLieGroups.AdjacentOverlapWitness` to close the
  anchor nonemptiness subgoal directly in production code.
- avoid importing `OverlapAnchor` in blockers, since it introduces a
  `permExtendedOverlapSet` name collision with private definitions in
  `PermutationFlow.lean`.

## 1. Exact n=2 content

Under:

- holomorphy on `FT`,
- restricted Lorentz invariance on `FT`,
- boundary-value continuity (`hF_bv`),
- local commutativity on real spacelike points (`hF_local`),
- prepared neighborhood assumptions:
  - `w ∈ permForwardOverlapSet tau` on `U`,
  - fixed witness `Gamma` with `Gamma·(tau·w) ∈ FT` on `U`,

show:

- near anchor `w0`, existential local slice-anchor data
  `∃ Λ0, Λ0·(tau·w) ∈ FT ∧ F(Λ0·(tau·w)) = F(w)` eventually on `U`.

Equivalent derived forms used in downstream wrappers:

- near anchor `w0`, local base identity
  `extendF(tau·w) = F(w)` eventually on `U`.

- near anchor `w0`, fixed-witness local equality
  `F(Gamma·(tau·w)) = F(w)` eventually on `U`.

- near anchor `w0`, for each prepared `w`, there exists `Lambda0` with
  - `Lambda0·(tau·w) ∈ FT`,
  - `F(Lambda0·(tau·w)) = F(w)`.

Public blocker-level equivalence lemmas now available:

- `blocker_eventually_slice_anchor_iff_extendF_base_eq_on_prepared_nhds_d1_adjSwap`
- `blocker_eventually_slice_anchor_iff_forward_eq_on_prepared_nhds_d1_adjSwap`
- `blocker_eventually_extendF_base_eq_iff_forward_eq_on_prepared_nhds_d1_adjSwap`

`n=2` wrappers are now available for each equivalence, including canonical
`swap(0,1)` forms:

- `blocker_eventually_slice_anchor_iff_extendF_base_eq_on_prepared_nhds_d1_adjSwap_n2`
- `blocker_eventually_slice_anchor_iff_extendF_base_eq_on_prepared_nhds_d1_swap01_n2`
- `blocker_eventually_slice_anchor_iff_forward_eq_on_prepared_nhds_d1_adjSwap_n2`
- `blocker_eventually_slice_anchor_iff_forward_eq_on_prepared_nhds_d1_swap01_n2`
- `blocker_eventually_extendF_base_eq_iff_forward_eq_on_prepared_nhds_d1_adjSwap_n2`
- `blocker_eventually_extendF_base_eq_iff_forward_eq_on_prepared_nhds_d1_swap01_n2`

### Coordinate-explicit reading (`d=1,n=2`)

Write a configuration as `w = (z0, z1)` with each `zk = (tk, xk) ∈ ℂ^2`
(time, space components). For `tau = swap(0,1)`:

- `tau·w = (z1, z0)`.
- `w ∈ FT` means:
  - `Im(t0, x0) ∈ V_+^0`,
  - `Im((t1, x1) - (t0, x0)) ∈ V_+^0`.
- `w ∈ permForwardOverlapSet tau` means:
  - `w ∈ FT`,
  - `tau·w ∈ ET` (there exists some complex Lorentz element sending
    `tau·w` into `FT`).
- Prepared-domain hypothesis with fixed `Gamma` means:
  - for every `w ∈ U`, `w ∈ FT` and `tau·w ∈ ET`,
  - and additionally `Gamma·(tau·w) ∈ FT`.

So the active local theorem asks to show, near `w0` within `U`:

- `∃ Λ0, Λ0·(tau·w) ∈ FT ∧ F(Λ0·(tau·w)) = F(w)`,

equivalently near `w0` within `U`:

- `extendF(tau·w) = F(w)`,
- `F(Gamma·(tau·w)) = F(w)`.

## 2. Why this is nontrivial already for n=2

From `w ∈ permForwardOverlapSet tau` we get:

- `w ∈ FT`,
- `tau·w ∈ ET`,
- hence existence of *some* `Lambda_w` with `Lambda_w·(tau·w) ∈ FT`.

What is missing is the value identity:

- `F(Lambda_w·(tau·w)) = F(w)`.

This is not immediate from `hU_good`; the fixed witness `Gamma` only gives
`Gamma·(tau·w) ∈ FT`, not equality of values to `F(w)`.

## 3. Present formal status in repo

There is a dedicated n=2 proof-idea file:

- `test/proofideas_hswap_d1.lean`

which compiles but still contains sorrys in the core route. Its current route
uses an additional hypothesis:

- real translation invariance of `F` (`TranslationInvariant`),

to reduce two-point configurations to a single-difference function `W`.

So at present:

- no completed proof exists for `d=1, n=2` from the current production
  hypothesis list alone;
- no formal counterexample has been implemented either.

## 4. Key risk to resolve first

The risk is exactly:

- current theorem statement may be too strong without an extra structural
  hypothesis (e.g. translation invariance), or
- translation invariance is implicitly encoded elsewhere in the model and needs
  to be made explicit in the proof route.

## 5. Immediate proof-first plan (n=2 only)

1. Freeze n=2 target theorem in a dedicated lemma (production or test), with
   current hypotheses only.
2. Attempt direct derivation from existing EOW/adjacency infrastructure.
3. If blocked, produce either:
   - a formal derivation that translation invariance is required, or
   - a formal counterexample candidate to the current stronger claim.
4. Only after n=2 is settled, lift the pattern to n=3.

## 5b. Current concrete attack route

With the new canonical wrappers, the immediate target can be kept in one line:

- `blocker_eventually_extendF_base_eq_on_prepared_nhds_d1_swap01_n2`.

Equivalent operational form:

- `blocker_eventually_forward_eq_on_prepared_nhds_d1_swap01_n2`.

Equivalent iff bridge:

- `blocker_eventually_extendF_base_eq_iff_forward_eq_on_prepared_nhds_d1_swap01_n2`.

This reduces proof search noise by removing `Fin` index transport and forcing
all work onto the core local analytic/geometric content.

New helper infrastructure (local, coordinate-oriented):

- [`D1N2Invariants.lean`](/Users/xiyin/OSReconstruction/OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/D1N2Invariants.lean)
  now exports:
  - `forwardTube_d1_n2_iff`,
  - `mem_adjSwapExtendedOverlapSet_d1_swap01_n2_iff`,
  - `mem_permForwardOverlapSet_d1_swap01_n2_iff`,
  - `no_common_forwardizer_d1_swap01_n2`,
  - `prepared_unswapped_not_forward_d1_swap01_n2`,
  in addition to the Minkowski bilinear/arithmetic lemmas.

These are intended to keep the remaining local theorem in explicit `n=2`
normal form during further proof search.

Operational consequence of the new obstruction lemmas:

- the same fixed Lorentz element cannot simultaneously forwardize both `w` and
  `swap(0,1)·w` in `d=1,n=2`,
- therefore any attempted local proof route for the blocker that requires
  eventual unswapped-forward membership for the prepared fixed witness is
  structurally invalid in this branch.

## 6. Anti-smuggling rule

No new assumption should be inserted into production statements unless one of
the following is formally established:

- the current statement is false as written, or
- the added assumption is already derivable/implicit in the existing model.

## 7. New proved reduction and dead-end classification (2026-03-01)

In `PermutationFlow.lean`, a new proved helper now isolates the n=2 local step:

- `eventually_slice_anchor_on_prepared_nhds_d1_adjSwap_n2_of_eventually_unswapped_forward`

Content:

- if on a prepared adjacent-swap neighborhood we additionally know eventual
  unswapped-forward membership
  `Γ·w ∈ FT` near `w0`,
- then the full slice-anchor conclusion follows (choose `Λ0 = Γ`) via:
  - adjacent-swap overlap equality (`eow_adj_swap_on_overlap`) on
    `z = Γ·w`, and
  - complex Lorentz invariance for `F`.

However, this route is now formally classified as a dead end:

- `PermutationFlow.lean` also proves
  `not_eventually_unswapped_forward_on_prepared_nhds_d1_adjSwap_n2`.
- stronger pointwise form now proved:
  `not_unswapped_forward_on_prepared_d1_adjSwap_n2`
  (`w ∈ U -> Γ·w ∉ FT`).
- stronger route-independent form now proved:
  `not_exists_common_forwardizer_d1_adjSwap_n2`
  (for any `w`, no single `Λ` can put both `Λ·w` and `Λ·(swap·w)` in `FT`).
- neighborhood form also proved:
  `not_eventually_common_forwardizer_nhds_d1_adjSwap_n2`
  (for any anchor-neighborhood pair with `w0 ∈ U`, this common-forwardizer
  property cannot even hold eventually near `w0`).
- Under the same prepared hypotheses (with `w0 ∈ U`), eventual `Γ·w ∈ FT`
  is impossible in `n=2`, because it would force both `z` and `swap·z` in `FT`
  at the anchor (`z = Γ·w0`), contradicting
  `adjSwap_not_mem_forwardTube_d1`.

So this sufficient criterion is mathematically correct but non-usable for
closing the actual blocker.

## 8. Geometric warning (now formalized in tests)

`Γ·(swap·w) ∈ FT` does **not** imply `Γ·w ∈ FT` even at a single point.

In `test/witness_test.lean`:

- `testWitness_in_FT` proves `w ∈ FT`,
- `testWitness_swap_in_ET` proves `swap·w ∈ ET`,
- `boosted_swapped_in_FT` proves `Γ·(swap·w) ∈ FT` for a concrete `Γ`,
- `boosted_unswapped_not_FT` proves `Γ·w ∉ FT` for the same `w, Γ`.

So the new reduction to eventual unswapped-forward membership is meaningful:
that property is genuinely additional geometry, not automatic from prepared
domain hypotheses.

## 9. Exact local reformulation (proved in production)

`PermutationFlow.lean` now proves:

- `eventually_slice_anchor_iff_eventually_extendF_base_eq_on_prepared_d1`.
- `eventually_slice_anchor_iff_eventually_forward_eq_on_prepared_d1`.

On a prepared neighborhood (`w ∈ U -> Γ·(tau·w) ∈ FT`), the blocker conclusion

- eventual `∃ Λ0, Λ0·(tau·w) ∈ FT ∧ F(Λ0·(tau·w)) = F(w)`

is equivalent to

- eventual deterministic base equality
  `extendF(tau·w) = F(w)`,
and equivalently to
- eventual fixed-witness equality
  `F(Γ·(tau·w)) = F(w)`.

Production simplification:

- `deferred_eventually_forward_eq_on_prepared_nhds_d1` now uses this direct
  slice-anchor ↔ fixed-`Γ` equivalence, rather than routing through an
  intermediate local `extendF` step.

So the `n=2` blocker can now be attacked as a pure local base-equality problem,
without carrying the existential slice-anchor witness in the target statement.

## 10. EOW caveat in current production route

Current `Adjacency.lean` implementation detail:

- `eow_adj_swap_extension_holo_only` builds a piecewise extension on
  `FT ∪ swap·FT` by disjoint-union holomorphicity.
- `eow_adj_swap_extension` is currently just this `holo_only` theorem.
- therefore `eow_adj_swap_on_overlap` only gives equality on
  `FT ∩ swap·FT`.

For `d=1,n=2`, this overlap is empty by adjacent-swap obstruction, so this
specific theorem path is vacuous in the blocker regime. In other words:

- the production theorem named `eow_adj_swap_on_overlap` is correct, but it is
  not the boundary-to-interior continuation mechanism needed to close the
  prepared-neighborhood blocker.

Consequence for blocker work:

- direct attempts to close the blocker by reusing `eow_adj_swap_on_overlap`
  without additional local-analytic input will not succeed in `d=1,n=2`.

## 11. Current derivability assessment

With the current production hypotheses only
(`hF_holo`, `hF_lorentz`, `hF_bv`, `hF_local`, prepared `hU_good`):

- no completed derivation of the local blocker theorem is known;
- no formal counterexample is implemented yet.

What is established is a precise equivalence class of local targets (Section 9).
So adding one of the following as an extra local input is mathematically
equivalent at this stage:

- eventual local slice-anchor pack,
- eventual local base identity `extendF(tau·w) = F(w)`,
- eventual local fixed-witness equality `F(Gamma·(tau·w)) = F(w)`.

Hence the blocker is genuinely the local gluing assertion itself, not a
statement-shape artifact.

Additional one-way reduction now formalized in production blockers file:

- `blocker_forward_eq_on_prepared_d1_adjSwap_of_global_extendF_overlap`
- `blocker_eventually_forward_eq_on_prepared_nhds_d1_adjSwap_of_global_extendF_overlap`

Meaning: if one already has global adjacent-swap ET-overlap invariance for
`extendF`, then the local prepared-neighborhood equality follows immediately.
This confirms the blocker sits strictly "below" global `hSwap` in strength.

## 12. n=2 reduction now in compact blocker file

To match the current compact `PermutationFlowBlockers.lean`, the following
direct n=2 reduction is now available:

- `blocker_eventually_slice_anchor_on_prepared_nhds_d1_nontrivial_n2_of_global_overlap`

It states:

- assume `d=1,n=2`,
- assume prepared-domain hypotheses,
- and assume global ET-overlap identity
  `extendF(τ·z) = extendF(z)` on `ET ∩ τ⁻¹·ET`.

Then:

- the local nontrivial blocker conclusion follows immediately (eventually on the
  prepared neighborhood) with witness choice `Λ₀ = Γ`.

This gives an explicit step-1 target split:

1. local theorem is now reduced to global overlap identity for `n=2`,
2. remaining burden is proving that global overlap identity from current
   hypothesis list.
