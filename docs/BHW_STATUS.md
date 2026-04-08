# BHW Status (Canonical)

Last updated: 2026-04-08

This file is the canonical root/docs status for the Bargmann-Hall-Wightman
connectedness/permutation blocker lane.

## 0. Scope and non-scope

Scope correction (2026-04-08): this file is canonical for the
`ComplexLieGroups` connectedness/permutation lane, but it is **not** by itself
the full live theorem-2 locality ledger.

Later Lean work should read the lanes as follows:

- **This file owns:** the checked-present `ComplexLieGroups` file split, the two
  remaining `ComplexLieGroups` blocker theorems, and the exact theorem-2 handoff
  boundary from BHW/adjacency geometry into Wick-rotation boundary-value work.
- **This file does not own:** the full theorem-2 frontier transcript, the
  flattened-regular boundary-continuity package, the canonical-shift recovery
  package, or the final boundary-value frontier theorem. Those belong to
  `docs/theorem2_locality_blueprint.md` and the Wick-rotation docs.

So this note should no longer be read as if “the BHW blocker” were one opaque
final theorem. The handoff is now a multi-file contract with explicit theorem
slots.

## 1. Checked production file inventory for the BHW lane

The following repo-relative production paths were checked against the current
clone and are the exact files later Lean work should open:

- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlocker.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/BHWExtension.lean`
- `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean`

Path-discipline correction:
shortened descriptions like “the BHW file”, “PermutationFlow”, or
“BoundaryValueLimits” are acceptable only as shorthand for the exact paths
above. They should not be treated as permission to relocate theorem-2 work into
nearby umbrella files.

## 2. Checked-present theorem surfaces vs planned theorem slots

### 2.1 Checked-present theorem surfaces already in the tree

These are real checked-present hooks, not doc inventions:

- `Adjacency.lean :: exists_real_open_nhds_adjSwap`
- `Adjacency.lean :: extendF_adjSwap_eq_on_realOpen`
- `AdjacencyDistributional.lean :: extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`
- `AdjacencyDistributional.lean :: extendF_adjSwap_eq_on_realOpen_of_distributional_local_commutativity`
- `BHWExtension.lean :: W_analytic_swap_boundary_pairing_eq`
- `BHWExtension.lean :: analytic_boundary_local_commutativity_of_boundary_continuous`
- `ForwardTubeDistributions.lean :: boundary_function_continuous_forwardTube_of_flatRegular`
- `ForwardTubeDistributions.lean :: boundary_value_recovery_forwardTube_of_flatRegular`
- `ForwardTubeDistributions.lean :: boundary_value_recovery_forwardTube_of_flatRegular_from_bv`
- `OSToWightmanBoundaryValues.lean :: bvt_F_swapCanonical_pairing`
- `OSToWightmanBoundaryValuesComparison.lean :: bv_local_commutativity_transfer_of_swap_pairing`

### 2.2 Planned theorem-slot names not yet present in the tree

These names are documentation-level theorem slots only. Later implementation
work should treat them as missing packages to build, not as existing lemmas to
search for:

- `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`
- `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`
- `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
- `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
- `bvt_F_swapCanonical_pairing_of_adjacent_chain`

Contract correction:
`W_analytic_swap_boundary_pairing_eq` is a checked theorem surface, but it is
**not** the theorem-2 closure surface on the live route, because for
`W := bvt_W OS lgc` it asks for the global locality input
`IsLocallyCommutativeWeak d W`. So later Lean work must not try to “finish
BHW” by directly instantiating that theorem and calling theorem 2 done.

## 3. Exact theorem-2 handoff contract through the BHW lane

The current theorem-2 handoff boundary is now fixed enough for direct Lean
execution order.

### 3.1 File ownership

1. `Adjacency.lean`
   - owns the lower real-open-edge / neighborhood geometry,
   - especially the checked local package `exists_real_open_nhds_adjSwap`.
2. `AdjacencyDistributional.lean`
   - owns the lower adjacent-swap distributional pairing route,
   - especially the checked surface
     `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`.
3. `BHWExtension.lean`
   - is the statement home for the planned adjacent-only substitute consumer
     `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`,
   - and then for the theorem-2-facing wrapper
     `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`.
4. `ForwardTubeDistributions.lean`
   - owns the flattened-regular continuity and boundary-recovery supplier lane,
   - not the BHW geometry itself.
5. `OSToWightmanBoundaryValueLimits.lean`
   - owns only the theorem-2 canonical-shift / adjacent-chain support layer,
   - namely the planned package
     `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
     -> `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
     -> `bvt_F_swapCanonical_pairing_of_adjacent_chain`.
6. `OSToWightmanBoundaryValues.lean`
   - owns only the final frontier consumer
     `bvt_F_swapCanonical_pairing`.

### 3.2 Proof-transcript order that later Lean work should follow

The theorem-2/BHW transcript is now explicitly:

1. use `Adjacency.lean :: exists_real_open_nhds_adjSwap` to choose the local
   real open edge for the adjacent swap and package the support-side ET data;
2. use the checked pointwise/open-edge adjacent-swap equalities from
   `Adjacency.lean` / `AdjacencyDistributional.lean` to obtain the lower
   adjacent-swap comparison on that chosen edge;
3. prove the planned adjacent-only substitute consumer
   `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` in
   `BHWExtension.lean`;
4. specialize that to the theorem-2 boundary functional as the planned wrapper
   `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`;
5. independently use
   `ForwardTubeDistributions.lean :: boundary_function_continuous_forwardTube_of_flatRegular`
   and
   `ForwardTubeDistributions.lean :: boundary_value_recovery_forwardTube_of_flatRegular_from_bv`
   to build the theorem-2 canonical boundary-pairing recovery package;
6. only then enter `OSToWightmanBoundaryValueLimits.lean` for
   `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
   -> `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
   -> `bvt_F_swapCanonical_pairing_of_adjacent_chain`;
7. only after those support theorems exist should
   `OSToWightmanBoundaryValues.lean :: bvt_F_swapCanonical_pairing` become a
   thin final consumer;
8. then `OSToWightmanBoundaryValuesComparison.lean ::
   bv_local_commutativity_transfer_of_swap_pairing` transfers that result to
   the public locality axiom.

Implementation warning:
later Lean work should **not** collapse steps 3-7 into one closing theorem, and
should **not** reopen the CLG geometry under `PermutationFlow.lean` or the
umbrella barrel `BHWPermutation.lean` once the route has reached the
boundary-pairing/canonical-shift layers.

## 4. Active `ComplexLieGroups` blockers

Current `ComplexLieGroups` direct `sorry` dependence is isolated in:

1. `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlocker.lean`
   - `blocker_isConnected_permSeedSet_nontrivial`
   - `blocker_iterated_eow_hExtPerm_d1_nontrivial`

These are the only remaining direct `sorry` lines under
`OSReconstruction/ComplexLieGroups` in the current checked tree.

## 5. Current branch split inside `PermutationFlow`

In the nontrivial branch of
`BHWPermutation/PermutationFlow.lean :: iterated_eow_permutation_extension`
(`σ ≠ 1`, `n ≥ 2`):

1. `d = 0`
   - already discharged by contradiction.
2. `d ≥ 2`
   - already implemented via the Jost-witness / connectedness route,
   - the remaining missing input is only
     `blocker_isConnected_permSeedSet_nontrivial`.
3. `d = 1`
   - still deferred explicitly through
     `blocker_iterated_eow_hExtPerm_d1_nontrivial`.

This branch split is local status for the CLG blocker lane. It should not be
misread as the complete theorem-2 blocker ledger.

## 6. What is still unresolved vs what is no longer allowed to drift

Still unresolved at doc level:

- the planned adjacent-only substitute consumer in `BHWExtension.lean` is not
  yet implemented;
- the theorem-2-specific wrapper above it is not yet implemented;
- the canonical-shift support package in
  `OSToWightmanBoundaryValueLimits.lean` is still planned rather than checked.

No longer allowed to drift across docs:

1. theorem 2 does **not** wait on the full nontrivial-permutation endgame in
   `PermutationFlowBlocker.lean`;
2. theorem 2 does **not** close by directly instantiating
   `W_analytic_swap_boundary_pairing_eq`;
3. the BHW lane stops at the adjacent-only raw-boundary handoff and does not
   own the later canonical-shift or frontier-consumer layers;
4. the final theorem-2 proof order is raw-boundary handoff first, canonical
   recovery second, adjacent-chain reduction third, frontier consumer fourth.

## 7. Where to read next

1. Root execution plan:
   - `docs/development_plan_systematic.md`
2. Full theorem-2 locality blueprint / theorem-slot contract:
   - `docs/theorem2_locality_blueprint.md`
3. Local line-oriented blocker status:
   - `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/BLOCKER_STATUS.md`
