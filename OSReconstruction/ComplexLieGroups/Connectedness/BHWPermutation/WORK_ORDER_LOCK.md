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
  - Primary reference note for this route:
    `INVARIANT_FUNCTION_PROOF_D1_N2.md` (best local proof file).
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
  - Current active theorem:
    `blocker_d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_source_invariantOnly_core_deferred`
  - Exact remaining deferred lemma (single local analytic `sorry`):
    `blocker_d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_invariantQuadric_core_deferred`
    with fully invariant statement:
    for quadric tuples `(q0,q1,p,s)` with paired light-cone witness conditions
    `d1N2InvariantLightConeWitness q0 q1 p s` and
    `d1N2InvariantLightConeWitness q1 q0 p (-s)`, prove
    `f q0 q1 p s - f q1 q0 p (-s) = 0`.
    The theorem body is now explicitly reduced to:
    1. the paired-witness form via
       `d1N2InvariantKernelDiffZeroOnForwardizableQuadric_iff_sectionWitnessDiffZero`,
    2. then the light-cone witness form via
       `d1N2InvariantKernelDiffZeroOnLightConeWitness_iff_forwardizableDiffZero`.
    Here `d1N2InvariantSectionWitnessPair` is currently the paired light-cone
    witness condition (both original and swapped tuples witnessed in `FT_{1,2}`).
    So the single remaining internal analytic subgoal is this paired-witness
    diff-zero statement inside the active theorem.
    The source wrapper theorem above is now `sorry`-free and aliases this
    invariant-only lemma.
    The former realizable-form theorem
    `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`
    is now a proved wrapper via
    `d1N2InvariantRealizable_iff_lightConeWitness`.
    The witness theorem
    `blocker_d1N2ForwardSwapEq_witness_fromSource_invariantOnly_core_deferred`
    is now a proved wrapper derived from this invariant-only core via
    factorization + `d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable`.
    The forwardizable invariant-kernel theorem
    `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred`
    is now a proved wrapper from this active theorem via
    `d1N2InvariantRealizable_pair_of_forwardizable`.
    Non-vacuity is now explicit in code:
    `d1N2InvariantRealizable_pair_nonempty` and
    `d1N2InvariantForwardizableSwap_nonempty` are proved.
    Paired light-cone witness non-vacuity is now explicit:
    `d1N2InvariantLightConeWitness_pair_nonempty`.
    New exact bridge:
    `d1N2InvariantForwardizableSwap_iff_lightConeWitness_pair`.
    New paired-witness bridge:
    `d1N2InvariantForwardizableSwap_iff_sectionWitness_pair`.
    New condition equivalence:
    `d1N2InvariantKernelDiffZeroOnLightConeWitness_iff_forwardizableDiffZero`.
    New section-form condition equivalence:
    `d1N2InvariantKernelDiffZeroOnForwardizableQuadric_iff_sectionWitnessDiffZero`.
    The theorem
    `blocker_d1N2Source_swappedInvariantForwardEq_invariantOnly_core_deferred`
    is now a proved wrapper via
    `d1N2Source_swappedInvariantForwardEq_iff_forwardBaseEq`.
    The realizable-pair kernel theorem
    `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariantOnly_core_deferred`
    is now proved from the swapped-invariant wrapper theorem by unpacking
    realizability witnesses
    and rewriting with `hf_onFT`.
    Theorems now proved as wrappers from that realizable-pair theorem:
    `blocker_d1N2ForwardBaseOpenAnchor_source_invariant_core_main_deferred`
    (via `d1N2ForwardBaseOpenAnchor_source_of_pairSwap`) and
    `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_main_deferred`.
    Current in-code reduction now also proves
    `blocker_d1N2Source_swappedInvariantForwardEq_core_deferred`
    via factorization plus the realizable-pair theorem above.
    The wrapper theorem
    `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_deferred`
    is now a direct alias to the realizable-pair main theorem (now sorry-free).
    Then
    `blocker_d1N2ForwardBaseOpenAnchor_source_core_deferred`
    is proved from factorization + realizable-pair symmetry + forward bridge.
    The former invariant realizable-pair theorem
    `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_core_deferred`
    is now proved by wrappers once this anchor package is available.
  - `blocker_d1N2InvariantQuadricModel_core_deferred` is now proved by:
    1. factorization (`blocker_d1N2InvariantFactorization_core_deferred`),
    2. symmetric extension of a source kernel from realizable tuples to all
       quadric tuples, and
    3. the active realizable-pair involution theorem above.
  - `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_core_deferred`
    is now proved directly from the active theorem above via
    `d1N2InvariantRealizable_pair_of_forwardizable`.
  - Equivalence helper now proved:
    `d1N2InvariantKernelPairSwapOnRealizable_iff_forwardizableDiffZero`.
  - Additional exact bridge now proved (for fixed `hf_onFT`):
    `d1N2ForwardSwapEq_onFT_iff_invariantKernelPairSwapOnRealizable`,
    with directional wrappers
    `d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable` and
    `d1N2InvariantKernelPairSwapOnRealizable_of_forwardSwapEq`.
  - Connectivity bridge now proved:
    `d1N2_isConnected_adjSwapForwardOverlapSet_of_seedConnectedBlocker`,
    reducing the `n=2` adjacent forward-overlap connectedness obligation to
    the existing deferred seed connectedness theorem.
  - Complex-anchor propagation bridge now proved:
    `d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_openAnchor`.
    This removes the need for a real ET-overlap witness in the n=2 bridge once
    an open anchor subset in `permForwardOverlapSet` is available.
  - Exact source-level reduction now proved:
    `d1N2InvariantKernelPairSwapOnRealizable_source_iff_openAnchor`.
    So for `d=1,n=2` source data, the active theorem is formally equivalent to
    existence of a nonempty complex-open forward-base anchor.
    The source-side direction is factored as:
    `d1N2ForwardBaseOpenAnchor_source_of_pairSwap`.
  - Dependency audit (2026-03-02):
    all pre-1307 invariant algebra/bridge lemmas are `sorry`-free except the
    deferred connectedness branch (`blocker_isConnected_permSeedSet_d1_nontrivial`).
    The non-circular bridge
    `d1N2InvariantKernelPairSwapOnRealizable_source_of_connectedOpenAnchor`
    is already `sorry`-free; the unresolved implication remains:
    source data `hsource` implies complex open-anchor existence
    (equivalently, the forward-swap core in the active theorem body).
    Added explicit connected-overlap equivalence:
    `d1N2InvariantKernelPairSwapOnRealizable_source_iff_openAnchor_of_connectedForwardOverlap`
    (also `sorry`-free).
  - `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_core_deferred`
    is now a proved wrapper to the active source-invariant core theorem.
  - `blocker_d1N2InvariantKernelSwapOnForwardizable_source_core_deferred`
    is now a proved wrapper (`sub_eq_zero`) around the active diff-zero theorem.
  - `blocker_d1N2LocalForwardEqNhd_core_deferred` is now proved by reduction to:
    1. factorization (`blocker_d1N2InvariantFactorization_core_deferred`),
    2. source-core forwardizable diff-zero theorem above, and
    3. `d1N2ForwardSwapEq_iff_invariantKernelDiffZeroOnForwardizableQuadric`.
  - `blocker_d1N2InvariantModel_core_deferred` is now a proved wrapper that
    combines:
    1. `blocker_d1N2InvariantFactorization_core_deferred`,
    2. forwardizable-core extraction, and
    3. `blocker_d1N2InvariantKernelSwap_core_of_forwardizableQuadricDiffZero`.
  - Formal insufficiency (proved in Lean):
    `d1N2InvariantKernelSource_not_sufficient_for_quadricDiffZero`
    shows `source + hf_onFT` does not force full-quadric involution for an
    arbitrary representative `f`.
  - Strengthened non-circular bridge now proved:
    `d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_realWitness`
    derives `FT` forward-swap equality from existing EOW/identity machinery,
    given explicit geometric inputs
    (`connected adjSwap forward-overlap + real spacelike overlap witness`).
  - Added invariant-route chart/Jacobian scaffolding in
    `D1N2LorentzInvariantRoute.lean`:
    `d1N2RealConfig` and closed-form real invariant formulas
    (`d1Q0R_realConfig`, `d1Q1R_realConfig`, `d1P01R_realConfig`,
    `d1S01R_realConfig`), explicit chart-level spacelike identity
    (`d1_adj_spacelike_expr_realConfig`), and explicit nonzero Jacobian minor
    witness at `d1N2RealProbePoint`
    (`d1N2InvariantJacobianMinorAtProbe_det_ne_zero`).
  - Added production probe obstruction:
    `d1N2InvariantRealizable_swappedProbe_not`, proving the swapped probe tuple
    `(-9,-1,-3,0)` is not realizable by any `FT_{1,2}` point.
    This blocks naive probe-point propagation arguments and keeps the active
    closure path on the invariant-only realizable domain.
  - Added production real-witness obstruction module:
    `D1N2RealWitnessObstruction.lean`, including
    `d1N2_no_real_et_pair_swap` and
    `d1N2_no_real_adjacent_spacelike_witness_swap`.
    Integrated into blockers via
    `d1N2ForwardSwapEOWGeometryPackage_false`, formally proving the
    `d=1,n=2` EOW real-witness package is inconsistent.
  - Added fixed-gauge chart obstruction in
    `D1N2LorentzInvariantRoute.lean`:
    `d1_not_re_gt_one_and_inv_re_gt_one` and
    `d1N2InvariantSectionDomain_not_swapClosed`.
    This proves the `v0 = I` section chart can never be simultaneously valid
    for both original and swap-side section parameters, so a single-chart
    section argument cannot close the active theorem by itself.
  - Added complementary dual section chart infrastructure in
    `D1N2LorentzInvariantRoute.lean`:
    `d1N2InvariantSectionDual`,
    `d1InvariantQuad_invariantSectionDual`,
    `d1N2InvariantSectionDualDomain`,
    `d1N2InvariantSectionDualDomain_probe`,
    `d1N2InvariantSectionDualPoint_mem_forwardTube_of_domain`.
    This is the first production multi-chart step toward closing the active
    invariant-only analytic core without leaving Lorentz-invariant coordinates.
  - Added explicit non-coverage witness for the two fixed gauges
    (`v0 = I`, `u0 = I`):
    `d1N2InvariantSectionPairDomains_not_cover_explicit_lightConeWitness_pair`.
    This proves there exists a tuple with both
    `d1N2InvariantLightConeWitness q0 q1 p s` and
    `d1N2InvariantLightConeWitness q1 q0 p (-s)` while both
    `d1N2InvariantSectionDomain (-q0) (-p) s` and
    `d1N2InvariantSectionDualDomain (-q0) (-p) s` fail.
    So the current two fixed-gauge charts are not a complete cover of the
    active doubly-witnessed locus.
  - Added explicit mixed-chart overlap probe:
    `d1N2InvariantSectionDomain_mixedComplexProbe`,
    `d1N2InvariantSectionDualDomain_mixedComplexProbe`,
    `d1N2InvariantSectionMixedDomains_quadricProbe`.
    This gives a concrete nonempty quadric tuple where the original side is
    captured by the `v0 = I` chart and the swapped side by the dual `u0 = I`
    chart.
  - Added mixed-domain packaging and FT-membership wrappers:
    `d1N2InvariantSectionMixedDomain`,
    `d1N2InvariantSectionMixedDomain_nonempty`,
    `d1N2InvariantSectionPoint_mem_forwardTube_of_mixedDomain`,
    `d1N2InvariantSectionDualSwapPoint_mem_forwardTube_of_mixedDomain`.
  - Added scalar light-cone realizability equivalence:
    `d1N2ConfigOfLightCone`,
    `d1N2ConfigOfLightCone_mem_forwardTube_iff`,
    `d1N2InvariantLightConeWitness`,
    `d1N2InvariantLightConeWitness_iff_exists_forwardInvariants`
    (route file), plus
    `d1N2InvariantRealizable_iff_lightConeWitness`
    (blocker file). This rewrites realizability into explicit `u/v` scalar
    constraints for invariant-route proofs.
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
- 2026-03-02: Extracted the unresolved analytic core into
  `blocker_d1N2InvariantKernelDiffZeroOnQuadric_core_deferred` and rewired
  wrappers so `blocker_d1N2InvariantModel_core_deferred` is sorry-free.
  Downstream `d=1,n=2` wrapper theorems now reduce through this quadric core.
- 2026-03-02: Replaced the false over-strong core
  (`source + hf_onFT -> full quadric diff-zero`) with the forwardizable target
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_core_deferred`.
  The full-quadric insufficiency is now explicitly tracked by
  `d1N2InvariantKernelSource_not_sufficient_for_quadricDiffZero`.
- 2026-03-02: Added exact equivalence theorem
  `d1N2ForwardSwapEq_iff_invariantKernelDiffZeroOnForwardizableQuadric`:
  for fixed `hf_onFT`, the remaining forwardizable invariant-kernel core is
  equivalent to forward-swap equality on `FT_{1,2}`.
- 2026-03-02: Added witness-form reduction
  `d1N2InvariantKernelDiffZeroOnForwardizableQuadric_iff_witnessForm` and
  realizability helper `d1N2InvariantRealizable_pair_of_forwardizable`, making
  the remaining n=2 analytic `sorry` content explicit in both invariant and
  `(z, Γ)` forms.
- 2026-03-02: Reduced the active core `sorry` to a single pointwise subgoal via
  `d1N2ForwardSwapEq_onFT_of_pointwiseSliceAnchor`: extract one anchor witness
  `Λ₀` with equality for each forwardizable `z`, then propagate to all witnesses
  by complex Lorentz invariance.
- 2026-03-02: Extracted that pointwise subgoal as the explicit deferred theorem
  `blocker_d1N2PointwiseSliceAnchor_core_deferred`; the former theorem
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_core_deferred` is
  now a proved wrapper
  (`pointwise-anchor -> forward-swap -> invariant diff-zero`).
- 2026-03-02: Refined one step further to a neighborhood-form local core
  `blocker_d1N2LocalSliceAnchorNhd_core_deferred`. The pointwise theorem
  `blocker_d1N2PointwiseSliceAnchor_core_deferred` is now proved by constructing
  an open prepared neighborhood around a single witness `(z, Γ)` and extracting
  the anchor at `z` from eventual local data.
- 2026-03-02: Converted the local n=2 core to an equivalent fixed-witness form
  `blocker_d1N2LocalForwardEqNhd_core_deferred` (`eventually F(Γ·swap·w)=F(w)`).
  The slice-anchor neighborhood theorem is now a proved wrapper via
  `d1N2EventuallySliceAnchor_iff_eventuallyForwardEq_fixedWitness`.
- 2026-03-02: Eliminated the local-core `sorry` by deriving
  `blocker_d1N2LocalForwardEqNhd_core_deferred` from the forward/kernel
  equivalence plus factorization. The sole remaining `d=1,n=2` deferred analytic
  statement is now the invariant-source core:
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_core_deferred`.
- 2026-03-02: Refactored the remaining `d=1,n=2` analytic `sorry` into the
  invariant-equality statement
  `blocker_d1N2InvariantKernelSwapOnForwardizable_source_core_deferred`.
  The diff-zero theorem
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_core_deferred`
  is now a proved wrapper via `sub_eq_zero`.
- 2026-03-02: Relocated the remaining `d=1,n=2` analytic `sorry` from the
  coordinate-level forward-swap subgoal to an invariant-only source lemma:
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_core_deferred`.
  Theorems
  `blocker_d1N2InvariantKernelSwapOnForwardizable_source_core_deferred` and
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_core_deferred`
  are now proved wrappers.
- 2026-03-02: Added proved strengthened EOW bridge
  `d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_realWitness`,
  making the non-circular route explicit: if one supplies connectedness of
  `adjSwapForwardOverlapSet (d=1,n=2)` plus one real spacelike ET-overlap
  witness, forward-swap equality on `FT_{1,2}` follows and feeds into the
  invariant diff-zero core via existing equivalence lemmas.
- 2026-03-02: Refactored the remaining n=2 `sorry` out of the source theorem:
  introduced deferred invariant quadric-model core
  `blocker_d1N2InvariantQuadricModel_core_deferred` and proved
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_core_deferred`
  by a non-circular transfer lemma between kernels agreeing on `FT_{1,2}`.
- 2026-03-02: Further refactored the single n=2 analytic `sorry` to the
  realizable-pair invariant statement
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_core_deferred`.
  Theorem `blocker_d1N2InvariantQuadricModel_core_deferred` is now proved by
  symmetric extension from realizable tuples, and
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_core_deferred`
  is proved directly from realizable-pair reduction lemmas.
- 2026-03-02: Added exact forward/core equivalence on fixed factorization data:
  `d1N2ForwardSwapEq_onFT_iff_invariantKernelPairSwapOnRealizable`, plus both
  directional wrappers. This pins the remaining deferred theorem exactly to the
  forward-swap analytic statement for the same `F,f,hf_onFT`.
- 2026-03-02: Added proved n=2 connectivity conversion
  `d1N2_isConnected_adjSwapForwardOverlapSet_of_seedConnectedBlocker`,
  so `adjSwapForwardOverlapSet` connectedness is now available from the
  existing seed-connectedness blocker theorem without restating the conversion.
- 2026-03-02: Added proved complex-anchor bridge
  `d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_openAnchor`.
  This isolates the remaining n=2 analytic burden to constructing a nonempty
  complex-open anchor subset of `permForwardOverlapSet` where
  `extendF(swap·w)=F(w)` holds.
- 2026-03-02: Refactored the active n=2 analytic `sorry` into
  `blocker_d1N2ForwardBaseOpenAnchor_source_core_deferred`.
  The theorem
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_core_deferred`
  is now a proved wrapper via forward-swap and realizable-pair bridges.
- 2026-03-02: Refined the body of
  `blocker_d1N2ForwardBaseOpenAnchor_source_core_deferred` so all non-geometric
  steps are proved by existing EOW/open-anchor infrastructure; the remaining
  local `sorry` is now an explicit geometric witness existence subgoal
  (`x0` real spacelike with both swap-related embeddings in `ExtendedTube 1 2`).
- 2026-03-02: Added exact source-level equivalence
  `d1N2InvariantKernelPairSwapOnRealizable_source_iff_openAnchor` and extracted
  the source-side anchor constructor
  `d1N2ForwardBaseOpenAnchor_source_of_pairSwap`.
  This makes the active blocker mathematically explicit as a pure open-anchor
  existence obligation under source assumptions.
- 2026-03-02: Re-centered the active `d=1,n=2` `sorry` on the invariant route:
  added deferred theorem
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_deferred`
  and proved
  `blocker_d1N2ForwardBaseOpenAnchor_source_core_deferred` as a wrapper from
  factorization + invariant realizable-pair symmetry + forward/realizable
  bridge (no geometric witness subgoal left in that theorem).
- 2026-03-02: Refined once more to a primitive invariant source theorem:
  introduced deferred
  `blocker_d1N2Source_swappedInvariantForwardEq_core_deferred`
  (`z,y ∈ FT` + swapped invariant-quad relation implies `F y = F z`).
  Theorem
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_deferred`
  is now proved as a wrapper using `hf_onFT`.
- 2026-03-02: Moved the remaining local `sorry` from the open-anchor wrapper
  back to an invariant-only realizable-pair theorem:
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariantOnly_core_deferred`.
  Theorems
  `blocker_d1N2ForwardBaseOpenAnchor_source_invariant_core_main_deferred` and
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_main_deferred`
  are now proved wrappers from that invariant-only core.
- 2026-03-02: Rebuilt stale `PermutationFlowBlockers` artifacts and ran a
  declaration-level axiom dependency scan. Result:
  `d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_openAnchor` and
  `d1N2InvariantKernelPairSwapOnRealizable_source_of_connectedOpenAnchor` are
  already `sorry`-free; the active unresolved piece is still exactly the
  source swapped-invariant forward-equality implication at
  `blocker_d1N2Source_swappedInvariantForwardEq_invariantOnly_core_deferred`.
- 2026-03-02: Refactored the remaining local analytic `sorry` into the
  source-level swapped-invariant forward theorem
  `blocker_d1N2Source_swappedInvariantForwardEq_invariantOnly_core_deferred`.
  The realizable-pair kernel theorem
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariantOnly_core_deferred`
  is now proved from realizability witnesses plus `hf_onFT` (no local `sorry`).
- 2026-03-02: Added exact reduction
  `d1N2Source_swappedInvariantForwardEq_iff_forwardBaseEq` and moved the
  remaining analytic `sorry` into
  `blocker_d1N2ForwardBaseEq_source_invariantOnly_core_deferred`
  (`z ∈ FT`, `swap·z ∈ ET` ⇒ `extendF(swap·z)=F z`).
  The swapped-invariant theorem is now a proved wrapper via this equivalence.
- 2026-03-02: Added proved package bridge
  `d1N2ForwardBaseEq_of_EOWGeometryPackage`:
  under `d1N2ForwardSwapEOWGeometryPackage`, source assumptions now imply the
  exact active core statement
  `blocker_d1N2ForwardBaseEq_source_invariantOnly_core_deferred`.
  So the residual gap is reduced to constructing the geometry package from
  source-side inputs in the locked `d=1,n=2` route.
- 2026-03-02: Added proved complex-anchor bridge
  `d1N2ForwardBaseEq_of_connectedForwardOverlap_and_openAnchor`:
  connected adjacent forward-overlap plus a nonempty complex-open base anchor
  now implies the exact active core statement. This aligns the remaining
  `d=1,n=2` closure work with the complex-open-anchor route.
- 2026-03-02: Flipped the local dependency to keep the deferred point in
  invariant coordinates:
  - `blocker_d1N2ForwardBaseEq_source_invariantOnly_core_deferred` is now proved
    from factorization + invariant realizable-pair symmetry +
    `d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable`.
  - the active `d=1,n=2` analytic deferred content is the realizable-pair
    invariant source core.
- 2026-03-02: Added exact source-level equivalence
  `d1N2InvariantKernelPairSwapOnRealizable_source_iff_swappedInvariantForwardEq`
  (via explicit-field bridge
  `d1N2InvariantKernelPairSwapOnRealizable_of_sourceField_iff_swappedInvariantForwardEq`).
  This makes the active deferred theorem exactly equivalent to the sourced
  swapped-invariant forward statement `F y = F z` under
  `d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z)`.
- 2026-03-02: Refactored the active invariant `sorry` into explicit
  swap-difference form:
  - new deferred theorem:
    `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`
    (`f q0 q1 p s - f q1 q0 p (-s) = 0` on realizable swap-pairs),
  - `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariantOnly_core_deferred`
    is now a proved wrapper by `sub_eq_zero`.
- 2026-03-02: Restored the deferred boundary so the active `sorry` is exactly
  the invariant-only diff-zero statement:
  `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`.
  The sourced swapped-invariant FT statement is now a proved wrapper via
  `d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_swappedInvariantForwardEq`.
  Added proved orbit-constancy helpers:
  `d1N2Field_eq_of_sameInvariantQuad_onFT`,
  `d1N2InvariantKernelSource_eq_of_sameInvariantQuad_onFT`.
- 2026-03-02: Added exact source-form equivalence
  `d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_forwardSwapEq_onFT`,
  so the active invariant-only diff-zero blocker is now explicitly equivalent to
  forward-swap equality on `FT_{1,2}` for the sourced field
  `Classical.choose hsource`.
- 2026-03-02: Added exact source-form equivalence
  `d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_pointwiseSliceAnchor`,
  so the active invariant-only diff-zero blocker is also explicitly equivalent to
  pointwise slice-anchor existence for the sourced field on `FT_{1,2}`.
- 2026-03-02: Added proved source wrapper
  `blocker_d1N2PointwiseSliceAnchor_fromSource_invariantOnly_core_deferred`,
  extracting pointwise slice-anchor existence from the active diff-zero blocker
  via the exact equivalence above.
- 2026-03-02: Added exact source-form equivalence
  `d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_openAnchor`,
  identifying the same active blocker with existence of a nonempty complex-open
  anchor subset where `extendF(swap·w)=F(w)`.
- 2026-03-02: Re-expressed the active theorem body
  `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`
  in the open-anchor form (via the equivalence above), so the remaining `sorry`
  subgoal now matches the locked complex-open-anchor route exactly.
- 2026-03-02: Extracted the remaining `d=1,n=2` analytic `sorry` into the
  invariant-only theorem
  `blocker_d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_invariantQuadric_core_deferred`.
  The source theorem
  `blocker_d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_source_invariantOnly_core_deferred`
  is now a proved wrapper, keeping the deferred statement purely in Lorentz
  invariants (`q0,q1,p,s` + witness predicates).
- 2026-03-02: Extended `D1N2LorentzInvariantRoute.lean` with additional
  invariant-function analytic scaffolding used by
  `INVARIANT_FUNCTION_PROOF_D1_N2.md`:
  - explicit complex chart formulas
    (`d1N2ComplexConfig`, `d1Q0_complexConfig`, `d1Q1_complexConfig`,
    `d1P01_complexConfig`, `d1S01_complexConfig`,
    `d1InvariantQuad_complexConfig`, `d1InvariantQuad_complexConfig_swap`),
  - explicit chart-level quadric identity
    `d1InvariantQuad_complexConfig_on_quadric`,
  - complex Jacobian minor companion and determinant nonvanishing
    (`d1N2InvariantJacobianMinorAtProbeC`,
    `d1N2InvariantJacobianMinorAtProbeC_det`,
    `d1N2InvariantJacobianMinorAtProbeC_det_ne_zero`),
  - determinant-to-independence consequences for both real/complex minors
    (`d1N2InvariantJacobianMinorAtProbe_linearIndependent_rows`,
    `d1N2InvariantJacobianMinorAtProbeC_linearIndependent_rows`).
  File-level Lean checks pass for
  `D1N2LorentzInvariantRoute.lean` and `PermutationFlowBlockers.lean`
  (remaining `sorry`s unchanged in blockers file).
- 2026-03-02: Added second-round invariant-route algebra scaffolding in
  `D1N2LorentzInvariantRoute.lean`:
  - chart bridge `d1N2ComplexConfig_realCast`,
  - symbolic Jacobian minor family
    `d1N2InvariantJacobianMinorC a b c d` with closed determinant formula
    `d1N2InvariantJacobianMinorC_det`,
  - probe identification
    `d1N2InvariantJacobianMinorC_atProbe` feeding the existing probe
    determinant/nonvanishing lemmas.
  Lean checks remain green for
  `D1N2LorentzInvariantRoute.lean` and
  `PermutationFlowBlockers.lean` (same `sorry` set as before).
- 2026-03-02: Added generic nonvanishing criterion for the symbolic complex
  Jacobian minor:
  `d1N2InvariantJacobianMinorC_det_ne_zero_of`
  (conditions `a ≠ 0` and `a*c - b*d ≠ 0`), to support the local full-rank
  branch of the invariant-image openness argument around the probe.
- 2026-03-02: Added symbolic real Jacobian minor companion and aligned probe
  determinant proof through it:
  - `d1N2InvariantJacobianMinorR`,
    `d1N2InvariantJacobianMinorR_det`,
    `d1N2InvariantJacobianMinorR_det_ne_zero_of`,
    `d1N2InvariantJacobianMinorR_atProbe`,
  - `d1N2InvariantJacobianMinorAtProbe_det` now factors through the symbolic
    formula rather than only `norm_num` on a hard-coded matrix.
- 2026-03-02: Added real/complex compatibility lemmas for the symbolic Jacobian
  minor:
  - matrix-level compatibility on real parameters:
    `d1N2InvariantJacobianMinorC_ofReal`,
  - determinant-level compatibility:
    `d1N2InvariantJacobianMinorC_det_ofReal`.
- 2026-03-02: Refactored the active analytic frontier in
  `PermutationFlowBlockers.lean`:
  - new dedicated deferred theorem
    `blocker_d1N2OpenAnchor_source_invariantAnalytic_core_deferred`
    carries the only `sorry` for the `d=1,n=2` analytic source-to-anchor step,
  - `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`
    is now a proved wrapper via
    `d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_openAnchor`.

## External comparison notes

- 2026-03-02 (Mike branch status comparison):
  reviewed
  `https://github.com/mrdouglasny/OSreconstruction-1/blob/main/OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/STATUS.md`.
  That status reports:
  - `BHW.bargmann_hall_wightman_theorem` with zero `sorry`s,
  - two project axioms: `kakSet_dense` and `hExtPerm_of_d1`,
  - d>=2 connectedness routed through dense KAK image (`kakSet_dense`).
  Local branch check at the same date:
  - `#print axioms BHW.bargmann_hall_wightman_theorem` gives
    `[propext, sorryAx, Classical.choice, Quot.sound]`,
  - local BHWPermutation files still contain deferred theorems (`sorry`).
  Interpretation for this lock:
  - Mike’s branch replaces key proof gaps with explicit project axioms,
  - this lock remains on the no-new-axiom, `d=1,n=2` invariant-function route,
    with active target
    `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`
    (the pair-swap theorem is now a proved `sub_eq_zero` wrapper).

- 2026-03-02 (plan adjustment): moved the single unresolved `sorry` back onto
  the invariant-only core theorem
  `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`.
  The open-anchor theorem
  `blocker_d1N2OpenAnchor_source_invariantAnalytic_core_deferred` is now a
  proved wrapper via
  `d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_openAnchor`.
  This keeps the frontier aligned with the locked invariant-function route and
  avoids treating open-anchor construction as the primary deferred statement.

- 2026-03-02 (documentation correction): for this branch, adding a separate
  translation-invariance hypothesis is **not** treated as a complexity reducer
  for the active `d=1,n=2` blocker. The active theorem is already posed in
  invariant coordinates with realizability hypotheses, and work remains locked
  to the invariant-function route (no translation-invariance detour).
- 2026-03-02 (state correction): in current Lean code, the single active
  deferred theorem for the `d=1,n=2` invariant route is
  `blocker_d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_invariantQuadric_core_deferred`,
  while the source/realisable/open-anchor theorems are proved wrappers through
  the existing exact equivalence chain.
- 2026-03-02 (convention clarification):
  in this local blocker file, `d1N2InvariantKernelSource` is a 2-slot
  configuration source package (`Fin 2 → ...`) and does not include a separate
  translation-invariance field. This does not contradict Wightman
  n-point-to-(n-1)-difference conventions elsewhere; it just fixes the current
  local theorem interface.
- 2026-03-02 (route guardrail):
  the `d=1,n=2` real-witness EOW package path is treated as obstructed in this
  branch; see test-level sign-obstruction files
  `test/d1_no_real_witness_swap_n2_probe.lean` and
  `test/d1_real_witness_sign_obstruction_test.lean`.
  Active closure target remains the invariant-function diff-zero core, not
  construction of `d1N2ForwardSwapEOWGeometryPackage`.
- 2026-03-02 (state refinement):
  added exact reduction
  `d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_source_iff_swappedInvariantForwardEq`.
  The active light-cone theorem is now reduced in-code to one sourced
  swapped-invariant forward-equality subgoal (`F y = F z` under the swapped
  invariant-quad relation).
- 2026-03-02 (chart-coverage refinement):
  added
  `d1N2InvariantSectionPairDomains_not_cover_explicit_lightConeWitness_pair`,
  giving an explicit doubly-light-cone-witness tuple outside both fixed-gauge
  section domains (`v0 = I` and `u0 = I`). This rules out closing the active
  blocker by a two-fixed-chart-only argument.
- 2026-03-03 (variable-chart route implementation):
  implemented variable-parameter section infrastructure in
  `D1N2LorentzInvariantRoute.lean`:
  - `d1N2SectionOrig`, `d1N2SectionSwap`,
  - fiber/paired-domain defs
    (`d1N2SectionOrigFiberDomain`, `d1N2SectionSwapFiberDomain`,
    `d1N2SectionPairedDomain`),
  - paired difference helper
    (`d1N2SectionPairDiff`, `d1N2SectionPairDiff_differentiableOn`),
  - quadric section identities
    (`d1InvariantQuad_sectionOrig`, `d1InvariantQuad_sectionSwap`),
  - reconstruction lemmas
    (`d1N2SectionOrig_eq_of_forward`,
     `d1N2SectionSwap_eq_of_forward_invariants`).
  Added in `PermutationFlowBlockers/Core.lean`:
  - hypothesis package
    `d1N2PairedChartAnchorConnected`,
  - conditional closure theorem
    `d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_of_pairedChartAnchorConnected`.
  Rewired in `PermutationFlowBlockers/Tail.lean`:
  - active light-cone theorem
    `blocker_d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_invariantQuadric_core_deferred`
    is now proved from the conditional closure theorem plus a dedicated source
    extraction theorem,
  - the remaining `d=1,n=2` analytic `sorry` is now isolated as
    `blocker_d1N2PairedChartAnchorConnected_fromSource_deferred`.
- 2026-03-03 (documentation correction):
  previous notes mentioning dual/mixed fixed-gauge chart lemmas are stale for
  the current local code snapshot; the production Lean file currently carries
  the variable-parameter chart route above.
- 2026-03-03 (blocker placement correction):
  added the converse bridge in `PermutationFlowBlockers/Core.lean`:
  `d1N2PairedChartAnchorConnected_of_lightConeWitnessDiffZero`
  (`light-cone diff-zero ⇒ paired-chart anchor`).
  Rewired `PermutationFlowBlockers/Tail.lean` so:
  1. the single `d=1,n=2` analytic `sorry` is again on the invariant theorem
     `blocker_d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_invariantQuadric_core_deferred`,
  2. `blocker_d1N2PairedChartAnchorConnected_fromSource_deferred` is now a
  proved wrapper from that invariant theorem via the new converse bridge.
- 2026-03-03 (exact frontier equivalence):
  added
  `d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_iff_pairedChartAnchorConnected`
  in `PermutationFlowBlockers/Core.lean`, giving a bidirectional equivalence:
  - light-cone witness diff-zero on invariants
    `↔`
  - paired variable-chart anchor connectedness of the sourced field.
  Then simplified
  `blocker_d1N2PairedChartAnchorConnected_fromSource_deferred`
  to use the `.1` direction of this exact equivalence.
