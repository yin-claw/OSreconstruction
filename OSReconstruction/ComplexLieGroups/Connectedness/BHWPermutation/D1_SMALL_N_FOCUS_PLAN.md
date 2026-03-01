# d=1 Small-n Focus Plan (`n=2,3`)

Last updated: 2026-03-01

This note isolates the current near-term proof objective:

- fully settle `d=1` small-`n` behavior (`n=2,3`) in theorem form,
- then use the observed shape to guide the general-`n` closure.

## Why this focus

Current deferred `d=1` items in `PermutationFlow.lean`:

1. `deferred_isConnected_permOrbitSeedSet_d1`
2. `deferred_eventually_slice_anchor_on_prepared_nhds_d1`
3. `deferred_d1_forward_triple_nonempty_nge4` (this one is `n>=4` only)

Small-`n` work can avoid (3) entirely and reduce cognitive load.

## Already closed for small n

### n=2

- `deferred_d1_leftAdj_anchor_nonempty` handles the `n=2` nontrivial branch by
  finite permutation case split contradiction (no deferred geometry call).
- Wrapper exposed:
  - `d1_leftAdj_anchor_nonempty_n2`.

### n=3

- nontrivial forward-triple branch is constructive via:
  - `D1N3Witnesses.lean`
  - the four exported witness theorems:
    - `d1_n3_forward_triple_nonempty_i0_pairA`
    - `d1_n3_forward_triple_nonempty_i0_pairB`
    - `d1_n3_forward_triple_nonempty_i1_pairA`
    - `d1_n3_forward_triple_nonempty_i1_pairB`
- integrated into:
  - `deferred_d1_forward_triple_nonempty_nontrivial` (`n=3` branch).
- wrappers exposed:
  - `d1_forward_triple_nonempty_nontrivial_n3`
  - `d1_ET_triple_nonempty_nontrivial_n3`
  - `d1_leftAdj_anchor_nonempty_n3`.

## Remaining small-n blockers

Even with the above, global `d=1` closure still depends on:

1. `deferred_isConnected_permOrbitSeedSet_d1` (all `n`, including `2,3`)
2. `deferred_eventually_slice_anchor_on_prepared_nhds_d1` (all `n`, including `2,3`)

So the small-`n` target is to prove dedicated `n=2,3` versions of these two
items and wire them as explicit lemmas.

## Concrete target lemmas (recommended)

1. `d1_seedConnected_n2`:
   `IsConnected (permOrbitSeedSet (d := 1) 2 σ)` for all `σ`.
2. `d1_seedConnected_n3`:
   `IsConnected (permOrbitSeedSet (d := 1) 3 σ)` for all `σ`.
3. `d1_adjSwap_forward_open_anchor_n2`:
   specialized version of the local gluing input at `n=2`.
4. `d1_adjSwap_forward_open_anchor_n3`:
   specialized version at `n=3`.

If these are proved, we can add a local theorem:

- `d1_extendF_perm_overlap_small_n` for `n ≤ 3`,

independent of the `n>=4` branch.

## Method constraints

1. No midpoint-route assumptions.
   Midpoint implication has formal counterexamples in test files.
2. Reuse existing EOW and connected-overlap infrastructure.
3. Keep `n>=4` branch untouched while proving `n=2,3`.

## Critical obstruction (real-witness route)

Recent probe files in `test/` make one point explicit:

- `test/d1_no_real_witness_swap_n2_probe.lean` proves
  `no_real_adjacent_spacelike_witness_swap_n2`.

Meaning for `d=1, n=2`:

- there is no real `x` with both `realEmbed x ∈ ET` and
  `realEmbed (swap·x) ∈ ET` (hence no real spacelike adjacent witness either).

Practical consequence:

- do not expect to close small-`n` `hSwap` through the
  `Adjacency.extendF_adjSwap_eq_of_connected_forwardOverlap` real-witness
  hypothesis in `d=1`;
- focus should remain on the complex-anchor / overlap-gluing route.

## Revised attack plan (after sign-obstruction checks)

1. Keep `deferred_d1_adjSwap_forward_open_anchor` as the primary non-connective
   target.
   Update: this wrapper is now proved; the remaining local non-connective target
   is `deferred_eventually_slice_anchor_on_prepared_nhds_d1`.
2. Avoid introducing any new real-witness assumptions in `d=1`.
3. For `n=2,3`, build closure through complex anchor data only:
   - anchor extraction from forward-overlap connectedness,
   - local eventual equality near a complex anchor,
   - `exists_forward_open_anchor_of_eventuallyEq_local`,
   - then global propagation by existing identity-theorem infrastructure.
4. Keep midpoint implication branches disabled; they are formally refuted and
   should not re-enter the proof path.

## Validation checklist

After each edit:

- `lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean`
- ensure no new axioms/sorrys are introduced.
