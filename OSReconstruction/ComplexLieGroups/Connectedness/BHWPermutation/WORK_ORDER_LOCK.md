# Work Order Lock (Mandatory)

Last updated: 2026-03-02

This file is a hard execution lock for current BHWPermutation work.
The agent must follow this order exactly and must not re-prioritize.

## Locked order

1. `d=1, n=2` first:
  - Primary target:
    `blocker_eventually_forward_eq_on_prepared_nhds_d1_adjSwap_deferred`
  - Required path forward:
    Lorentz invariant-function route on `FT_{1,2}` via
    `(Q₀,Q₁,P,S)` factorization and swap action
    `(Q₀,Q₁,P,S) ↦ (Q₁,Q₀,P,-S)`.
  - Work through explicit `n=2` wrappers first when useful:
    - `blocker_eventually_forward_eq_on_prepared_nhds_d1_adjSwap_n2`
    - `blocker_eventually_extendF_base_eq_on_prepared_nhds_d1_swap01_n2`
2. `d=1, n=3` second:
   - Same local blocker shape specialized to `n=3`.
   - Reuse the pattern learned from `n=2`.
3. Only after (1) and (2) are settled:
   - `n>=4` branches,
   - general `d=1` global closure,
   - `d>=2` connectedness cleanup/refinement.

## Hard prohibitions before steps (1) and (2) complete

1. No switching focus to `n>=4` proof construction.
2. No switching focus to general connectedness/decomposition work except
   minimal dependencies required by the active small-`n` step.
3. No architecture detours that do not directly advance the active step in
   the locked order.
4. No adoption of new axioms.
5. For `d=1,n=2`, proof work MUST follow the Lorentz-invariant route in
   `D1N2LorentzInvariantRoute.lean`; do not switch to non-route strategies.
6. For `d=1,n=2`, use Lorentz invariant-function arguments as the primary
   analytic path (model/factorization/swap-kernel), not midpoint or
   real-witness substitutes.

## Session protocol

At session start, agent must explicitly state:

- current lock step (`n=2` or `n=3`),
- active target theorem name,
- why the next edit is required for that target.

Before any substantial exploration/edit outside the active step, agent must:

- stop,
- record the reason in the "Deviation Log" below,
- return to the active locked step.

## Completion criteria

Step 1 (`n=2`) is complete only when either:

1. theorem is fully proved from current production hypotheses, or
2. a formal impossibility/insufficiency statement is proved in Lean with a
   precise missing hypothesis identified.

Step 2 (`n=3`) uses the same completion rule.

No transition to step 3 is allowed before both step 1 and step 2 are marked
"complete" in this file.

## Progress board

- Step 1 (`d=1,n=2` local blocker): IN_PROGRESS
  - Current active theorem: `blocker_d1N2InvariantModel_core_deferred`
  - `blocker_d1N2ForwardSwapEq_on_FT_deferred` is an alias wrapper to this
    forward result, and `blocker_d1N2ForwardSwapEq_on_FT_core_deferred` now
    reduces to the invariant-model theorem via
    `d1_n2_forward_swap_eq_of_invariantModel`.
- Step 2 (`d=1,n=3` local blocker): PENDING
- Step 3 (`n>=4` and global cleanup): LOCKED

## Deviation log

- 2026-03-01: Added lock file after observed drift to global blocker analysis.
- 2026-03-02: Removed circular dependency in the `d=1,n=2` chain
  (`forward-swap -> model -> kernel-swap -> forward-swap`) by making
  `blocker_d1N2ForwardSwapEq_on_FT_deferred` derive from the invariant-model
  theorem and leaving `blocker_d1N2InvariantKernelSwapRule_deferred` as the
  sole deferred analytic step in this subchain.
- 2026-03-02: Normalized the chain to a single explicit deferred core
  `blocker_d1N2ForwardSwapEq_on_FT_core_deferred`; forward/kernelswap wrappers
  now reduce to this theorem (no hidden local `sorry` in wrappers).
- 2026-03-02: Re-locked the `d=1,n=2` chain so the sole local deferred step is
  Lorentz-invariant:
  `blocker_d1N2InvariantModel_core_deferred`.
  The forward-core theorem is now proved from it via
  `d1_n2_forward_swap_eq_of_invariantModel`.
