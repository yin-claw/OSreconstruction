# Wightman TODO: OS Reconstruction Priority Queue

Last updated: 2026-03-16

This file tracks the active blocker picture on the OS reconstruction path.
Policy lock: no wrappers, no useless lemmas, no code bloat; close `sorry`s with substantial mathematical proofs.

## Live Sorry Census

Count convention: direct tactic holes only (`^[[:space:]]*sorry([[:space:]]|$)`).

| Scope | Direct `sorry` lines |
|-------|----------------------:|
| `OSReconstruction/Wightman` | 20 |
| `OSReconstruction/SCV` | 2 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 36 |
| **Whole project** | **60** |

Count cross-checked on 2026-04-10 with:
```bash
find OSReconstruction -name '*.lean' -print0 \
  | xargs -0 grep -nE '^[[:space:]]*sorry([[:space:]]|$)'
```
with bucket totals recomputed from the matching file paths.

Tracked production tree currently contains six explicit axioms:
- `schwartz_nuclear_extension` in `Wightman/WightmanAxioms.lean`
- `exists_continuousMultilinear_ofSeparatelyContinuous` in
  `Wightman/WightmanAxioms.lean`
- `vladimirov_tillmann` in `SCV/VladimirovTillmann.lean`
- `distributional_cluster_lifts_to_tube` in `SCV/VladimirovTillmann.lean`
- `tube_boundaryValueData_of_polyGrowth` in `SCV/TubeBoundaryValues.lean`
- `reduced_bargmann_hall_wightman_of_input` in
  `Wightman/Reconstruction/WickRotation/BHWReducedExtension.lean`

## Current Root Blockers

## Priority Split In `Main.lean`

There are two different lanes and they should not be conflated:

1. Analyticity / Wick-rotation lane:
   - `wightman_to_os`
   - `os_to_wightman`
   - critical files:
     `Wightman/Reconstruction/WickRotation/OSToWightmanSemigroup.lean`,
     `Wightman/Reconstruction/WickRotation/OSToWightman.lean`,
     `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`,
     `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`,
     `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
   - shared dependencies: `SCV/*`, `BHWExtension`, `BHWTranslation`, `ForwardTubeLorentz`, `SchwingerAxioms`

2. Operator / GNS lane:
   - `wightman_reconstruction`
   - `wightman_uniqueness`
   - critical files: `Reconstruction/GNSHilbertSpace.lean`, `Reconstruction/Main.lean`, `vNA/Unbounded/StoneTheorem.lean`

Policy:
- while the active target is OS analyticity, do not drift into Stone/self-adjoint-generator work unless it directly unblocks the split `OSToWightman*` lane
- `StoneTheorem` is not needed for the analyticity chain
- Stone is needed later for the reconstructed `spectrum_condition` / `vacuum_unique` operator-theoretic branches

### 1. `WickRotation/OSToWightman*` split lane (8)

Doc-level contract note:
- theorem 2 / 3 / 4 route authority lives in
  `docs/theorem2_locality_blueprint.md`,
  `docs/theorem3_os_route_blueprint.md`, and
  `docs/theorem4_cluster_blueprint.md`
- for theorem 3 specifically,
  `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
  contains the exported private theorem `bvt_W_positive`, but the actual live
  implementation seam is the Section-4.3 transport package in
  `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`; the
  checked `singleSplit_xiShift` scalar holomorphic / `t -> 0+` supplier layer
  lives separately in
  `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`
  and must not be collapsed back into the frontier shell.

Active upstream blockers:
- `OSToWightman.lean` (1):
  - `schwinger_continuation_base_step`
- theorem-2 locality frontier:
  - implementation locus:
    `OSToWightmanBoundaryValues.lean :: bvt_F_swapCanonical_pairing`
  - hard doc-level gap: primary Route-B open-edge / ET-support geometry
    package plus the flattened regular continuity constructor for `bvt_F`
  - Route A via `ForwardJostSet` remains blocked-only fallback, not the
    primary theorem surface
- theorem-3 positivity package:
  - implementation locus:
    `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
  - checked-present supplier/consumer contract there is now frozen as:
    `identity_theorem_right_halfplane` (`OSToWightmanPositivity.lean:48`)
    -> `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` (`:110`) only on
       the Stage-A entry seam `os1TransportOneVar ->
       os1TransportOneVar_eq_zero_iff`;
    the checked general Hilbert-target/equality package
       `positiveTimeBorchersVector` (`:1461`) together with
       `positiveTimeBorchersVector_inner_eq` (`:1467`) and
       `positiveTimeBorchersVector_norm_sq_eq` (`:1480`) first enters only at
       `bvt_transport_to_osHilbert_onImage`, not earlier in Stage A/B;
    the later single-component specialization
       `euclideanPositiveTimeSingleVector` (`:1523`) together with checked norm
       supplier `euclideanPositiveTimeSingleVector_norm_sq_eq` (`:1530`) is
       downstream of that Stage-C transport map and may only re-enter after the
       general transport target has already been fixed;
    `positiveTimeBorchersVector_dense` (`:1506`) first enters only at
       `bvt_W_positive_of_transportImage_density`, not as an earlier transport
       input or a theorem to rediscover inside the missing Section-4.3 package
  - checked auxiliary supplier file:
    `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`
    owns only the `singleSplit_xiShift` scalar holomorphic object plus its
    `t -> 0+` limit-transfer theorems; it is a supplier layer consumed by the
    Section-4.3 package, not the theorem-3 closure file. The local theorem
    surfaces there are now frozen more literally so later Lean work does not
    have to rediscover which rows are objects, which are helpers, and which are
    actual terminal consumers:
    `:260 :: bvt_singleSplit_xiShiftHolomorphicValue`
    -> `:273 :: differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue`
    -> `:290 :: bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
    -> supplier-only Schwinger leg `:314 :: bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`
    -> supplier-only Schwinger limit `:350 :: tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
    -> deprecated bridge `:388 :: tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift` (historical/quarantined only; no live theorem-3/theorem-4 consumer)
    -> helper-only uniqueness lemma `:494 :: eqOn_rightHalfPlane_of_ofReal_eq`
    -> uniqueness packaging `:536 :: bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
    -> sole live terminal theorem `:446 :: tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`.
    Consumer order is frozen by first use rather than source order: the Stage-A
    transport entry sees only the scalar object / positive-real shell (`:260`
    and `:290`); any optional right-half-plane uniqueness detour may use only
    `:494 -> :536`; and the first theorem-3 terminal consumer is exactly `:446`.
    No Section-4.3 slot may treat `:314`, `:350`, or `:388` as admissible end
    surfaces.
  - exported wrapper:
    `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean :: bvt_W_positive`
  - still-missing work: the fully split Section-4.3 transport-image / closure
    theorem package from the blueprint remains planned theorem-slot work, not
    landed production theorem names in the current file; the active execution
    order is now fixed more sharply as
    `partialFourierSpatial_fun`
    -> `partialFourierSpatial_timeSliceSchwartz`
    -> `partialFourierSpatial_timeSlice_hasPaleyWienerExtension`
    -> `partialFourierSpatial_timeSliceCanonicalExtension`
    -> `os1TransportOneVar`
    -> `os1TransportOneVar_eq_zero_iff`
    -> `os1TransportComponent`
    -> `os1TransportComponent_eq_zero_iff`
    -> `BvtTransportImageSequence`
    -> `bvt_transport_to_osHilbert_onImage_wellDefined`
    -> `bvt_transport_to_osHilbert_onImage`
    -> `lemma42_matrix_element_time_interchange`
    -> `bvt_wightmanInner_eq_transport_norm_sq_onImage`
    -> `bvt_W_positive_of_transportImage_density`
    with the internal Stage-C transcript frozen as: representative choice for
    `bvt_transport_to_osHilbert_onImage_wellDefined` -> subtract two chosen
    preimage families -> kernel-zero discharge in the exact order
    `os1TransportOneVar_eq_zero_iff -> os1TransportComponent_eq_zero_iff` ->
    form `bvt_transport_to_osHilbert_onImage` landing in
    `positiveTimeBorchersVector` -> run
    `lemma42_matrix_element_time_interchange` -> recognize the norm via
    `positiveTimeBorchersVector_norm_sq_eq` -> only then close by
    `bvt_W_positive_of_transportImage_density`
  - on-image well-definedness must appear as its own theorem slot
    `bvt_transport_to_osHilbert_onImage_wellDefined`, and that slot must
    consume the explicit kernel-zero slots
    `os1TransportOneVar_eq_zero_iff` and `os1TransportComponent_eq_zero_iff`;
    later Lean work should not treat a vague injectivity slogan as an accepted
    replacement for those theorem surfaces
  - the closure point is also now frozen more sharply: the transformed-image
    quadratic identity is not yet the implementation endgame by itself. The
    Section-4.3 package must pass through the explicit Lemma-4.2 adapter
    `lemma42_matrix_element_time_interchange` before
    `bvt_wightmanInner_eq_transport_norm_sq_onImage`, and the actual
    implementation-side closure theorem is
    `bvt_W_positive_of_transportImage_density`, with
    `OSToWightmanBoundaryValues.lean :: bvt_W_positive` treated only as the
    exported frontier wrapper.
  - theorem-4 dependency contract: theorem 4 should consume corrected
    one-factor transport statements extracted from the eventual Section-4.3
    transport package, not the false same-shell factor identities from older
    cluster notes
- `OSToWightmanBoundaryValues.lean` transfer / consumer layer:
  - `bv_translation_invariance_transfer`
  - `bv_lorentz_covariance_transfer`
  - `bv_local_commutativity_transfer`
  - `bv_positive_definiteness_transfer`
  - `bv_hermiticity_transfer`
  - `bvt_cluster`
- `OSToWightmanBoundaryValuesBase.lean` boundary-data layer:
  - public theorem surfaces:
    - `boundary_values_tempered`
    - `bvt_F_holomorphic`
    - `bvt_boundary_values`
  - checked-private in-file packaging theorems:
    - `forwardTube_boundaryValueData_of_polyGrowth`
    - `full_analytic_continuation_boundaryValueData`

Current status:
- the fake intermediate Bochner path is off the active chain
- the active continuation chain goes through the honest OS quotient/Hilbert semigroup already built in `OSToWightmanSemigroup.lean`
- `OSLinearGrowthCondition` is already used upstream to prove polynomial growth of time-shift matrix elements and hence contraction of the Euclidean semigroup
- the positive-time spectral-power continuity input is now landed in `vNA/Bochner/SemigroupRoots.lean`
- `Wightman/SchwartzTensorProduct.lean` now contains genuine insertion operators (`productTensorUpdateCLM`, `prependFieldCLMLeft/Right`) for the Schwartz kernel-extension lane
- the real remaining work is still:
  - `schwinger_continuation_base_step` in `OSToWightman.lean`
  - the still-missing flattened-growth / flat-regular constructor package for
    theorem 2 in `ForwardTubeDistributions.lean`
  - the six transfer theorems in `OSToWightmanBoundaryValues.lean`
  - `bvt_cluster` in `OSToWightmanBoundaryValues.lean`

Immediate sharpened subgaps:
- For `schwinger_continuation_base_step`: the next active target is the original 2-point Schwinger case, i.e. one difference variable after translation reduction. This must be stated on the honest Schwinger-side domain (`ZeroDiagonalSchwartz d 2` or an explicitly admissible Euclidean subspace promoted into it), not on ambient full Schwartz space.
- For `schwinger_continuation_base_step`: no more active effort on the original 1-point case; it is mathematically trivial from translation invariance and not a blocker.
- For `schwinger_continuation_base_step`: the honest remaining choice is between a concrete Schwinger-side two-point/difference-variable reduction and, only if forced later, a deeper Schwartz kernel-extension theorem. The tensor insertion maps do not close the blocker by themselves.
- For theorem 2 / `bvt_F_swapCanonical_pairing`: the current implementation target is not another continuation theorem. The hard gap is the explicit Route-B real-open-edge support package feeding the checked raw-boundary adjacent-swap lane, together with the flattened regular constructor package needed to obtain `bvt_F` boundary continuity on the raw real trace. The docs now record one extra theorem-surface caution: the public BHW wrapper `WickRotation/BHWExtension.lean :: W_analytic_swap_boundary_pairing_eq` itself asks for `hLC : IsLocallyCommutativeWeak d W`, so taking `W := bvt_W OS lgc` would be circular on theorem 2. A direct source check shows the lower theorem `AdjacencyDistributional.lean :: extendF_adjSwap_pairing_eq_of_distributional_local_commutativity` still asks for the same `IsLocallyCommutativeWeak` input. So the raw-boundary closure shape is now fixed more sharply: theorem 2 should introduce the explicitly named adjacent-only substitute consumer theorem `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` on the `AdjacencyDistributional.lean` / `BHWExtension.lean` seam. Its statement home is `BHWExtension.lean`, any lower helper lemmas belong in `AdjacencyDistributional.lean`, and its proof transcript is now fixed as: pointwise `analytic_boundary_local_commutativity_of_boundary_continuous` on the chosen Route-B edge -> compact-support integrand equality -> pairing equality. The docs no longer leave open a second endorsed route that first proves the stronger full-global theorem `IsLocallyCommutativeWeak d (bvt_W OS lgc)`.
- Theorem-2 checked production-locus split: the frontier theorem itself lives in
  `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`,
  the downstream consumer already lives in
  `.../OSToWightmanBoundaryValuesComparison.lean`, the canonical-shift closure
  layer belongs in `.../OSToWightmanBoundaryValueLimits.lean`, the flattened-
  regular continuity supplier belongs in
  `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`,
  the swap/locality suppliers live in `.../BHWExtension.lean` plus the checked
  BHW-permutation umbrella / adjacent-swap support stack
  `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation.lean` /
  `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean` /
  `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean`,
  and the analytic/geometry suppliers live in
  `OSReconstruction/Wightman/Reconstruction/AnalyticContinuation.lean` plus
  `OSReconstruction/ComplexLieGroups/JostPoints.lean`.
- Theorem-2 doc-level package order is now explicit: Route-B real-open-edge
  choice -> swapped-edge ET support -> `bvt_F_hasFlatRegularRepr` ->
  `bvt_F_boundary_continuous_at_real_support` -> close the adjacent-only raw-
  boundary theorem through the substitute consumer
  `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` -> package
  that closure as `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` ->
  separate adjacent canonical-shift adapter theorem with frozen local order
  `raw-boundary wrapper -> swapped-side canonical recovery -> unswapped-side
  canonical recovery -> transitivity/symmetry` -> separate adjacent-chain
  reducer from a general `swap i j` frontier statement to adjacent
  transpositions only, with no reopening of the raw-boundary or recovery
  theorems inside that reducer.
  The checked public wrapper `W_analytic_swap_boundary_pairing_eq` remains the
  downstream/public comparison shape, not the theorem-2 raw-boundary closure
  theorem itself. The lower pointwise theorem
  `analytic_boundary_local_commutativity_of_boundary_continuous` remains
  supplier-only and is not a co-primary theorem-2 closing surface. Also keep
  the adjacent-chain reducer contract separate from any pseudocode-internal
  helper names: schematic names like `adjacentSwapFactorization` and
  `AdjacentCanonicalSwapPairingStepHolds` are not checked repo surfaces and
  should not be treated as frozen theorem slots.
- Theorem-2 checked-tree discipline is now stricter too: distinguish the
  checked-present theorem surfaces already in the repo
  (`W_analytic_swap_boundary_pairing_eq`,
  `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`,
  `analytic_boundary_local_commutativity_of_boundary_continuous`,
  `boundary_function_continuous_forwardTube_of_flatRegular`,
  `bvt_F_holomorphic`, `bvt_boundary_values`,
  `bv_local_commutativity_transfer_of_swap_pairing`) from the doc-planned
  missing package names (`choose_real_open_edge_for_adjacent_swap`,
  `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`,
  `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`,
  `bvt_F_swapCanonical_pairing_of_adjacent_chain`, etc.). Those latter names
  are implementation targets, not hidden helpers to rediscover. More sharply,
  the public wrapper `W_analytic_swap_boundary_pairing_eq` and the lower
  distributional theorem below it are no longer interchangeable in the docs:
  both still carry the global `IsLocallyCommutativeWeak` input, so the
  endorsed theorem-2 raw-boundary slot is now the adjacent-only substitute
  consumer theorem on the `AdjacencyDistributional.lean` / `BHWExtension.lean`
  seam. The docs no longer allow an "adjacent" theorem-slot name that silently
  asks for the stronger full-global theorem surface, and they no longer leave
  the full-global route as a co-endorsed theorem-2 closure shape.
- The theorem-2 continuity subpackage is now sharper as well. The checked
  public holomorphic and unflattened boundary-distribution suppliers already
  exist in `OSToWightmanBoundaryValuesBase.lean` (`bvt_F_holomorphic`,
  `bvt_boundary_values`), and the designated source-to-slot map is now fixed:
  `bvt_F_holomorphic -> bvt_F_flattened_holomorphic`,
  `bvt_boundary_values -> bvt_F_flattened_distribution_boundary`, while
  `boundary_values_tempered` remains the broader public existence theorem and
  not the designated source object for that flattened boundary-distribution
  slot. The checked upstream public growth source is
  `OSToWightman.lean :: full_analytic_continuation_with_symmetry_growth`, and
  the live checked extraction pattern is now explicit too: the unflattened
  growth package used by the boundary-data layer is the tail field
  `(full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.2.2.2.2.2`
  after the holomorphy / Euclidean / permutation / translation /
  canonical-star components. Inside `OSToWightmanBoundaryValuesBase.lean`, the current tree then packages
  those inputs through the checked-private theorems
  `forwardTube_boundaryValueData_of_polyGrowth` and
  `full_analytic_continuation_boundaryValueData`, with
  `boundary_values_tempered` as the public boundary-value output. More
  sharply, the current tree already exports the exact unflattened growth field
  for the chosen `bvt_F` witness
  (`∃ C_bd N, 0 < C_bd ∧ ∀ z ∈ ForwardTube d n, ‖bvt_F z‖ ≤ ...`), and the
  private theorem
  `OSToWightmanBoundaryValuesBase.lean ::
  full_analytic_continuation_boundaryValueData` already unpacks that field on
  the OS-side boundary-data lane. The honest open theorem package is therefore
  only the flattened polynomial-growth transport plus the new regular
  constructor `flatRegular_of_boundary_distribution_and_polyGrowth`, not a
  vague need to invent all regular-input pieces from scratch. The active
  flattened-input theorem-slot names are now fixed at
  `bvt_F_flattened_holomorphic`, `bvt_F_flattened_distribution_boundary`, and
  `bvt_F_flattened_growth`; stale flipped names `flattened_bvt_F_*` should not
  be reused in follow-up docs or Lean work.
- The theorem-2 endgame above the adjacent raw-boundary theorem is also now
  narrower than older notes suggested. The checked tree already has
  `ForwardTubeDistributions.lean ::
  boundary_value_recovery_forwardTube_of_flatRegular` and
  `boundary_value_recovery_forwardTube_of_flatRegular_from_bv`, so the
  remaining adapter gap is not a vague pair of raw/canonical rewrite lemmas.
  It is the theorem-2-specific canonical pairing recovery specialization
  `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` at
  `canonicalForwardConeDirection`, followed by the separate gluing theorem
  `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`, and only
  then the still-separate general `swap i j` adjacent-chain reducer.
- More explicitly, that specialization must consume the already-exported
  boundary-functional package from
  `OSToWightmanBoundaryValuesBase.lean`: `bvt_W` for the boundary functional,
  `bvt_W_continuous` for continuity, and `bvt_boundary_values` for the
  `nhdsWithin 0 (Set.Ioi 0)` boundary-value theorem. Do not leave the theorem-2
  adapter docs talking as if a new boundary functional `T` still needs to be
  invented.
- Theorem-2 file-locus ownership inside
  `OSToWightmanBoundaryValueLimits.lean` is now sharper too: the checked file
  currently packages theorem-3 `singleSplit_xiShift` / `t → 0+` limit results,
  so theorem-2 support there must be added as a sibling subsection in the exact
  local order
  `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
  -> `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
  -> `bvt_F_swapCanonical_pairing_of_adjacent_chain`.
  That subsection begins only after the raw-boundary theorem
  `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` has already been
  proved on the `BHWExtension.lean` side via
  `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`; it does not
  own the raw-boundary closure theorem itself. The first theorem should be
  treated as the direct specialization of
  `boundary_value_recovery_forwardTube_of_flatRegular_from_bv` at `bvt_W`,
  `bvt_W_continuous`, `bvt_boundary_values`, and
  `canonicalForwardConeDirection`; the second theorem should then glue that
  already-closed adjacent raw-boundary equality to the specialization on both
  sides before the separate general-swap reducer is proved.
- More explicitly, theorem 2 is now bound to the unique package chain
  `choose_real_open_edge_for_adjacent_swap`
  -> `swapped_support_lies_in_swapped_open_edge`
  -> `swapped_open_edge_embeds_in_extendedTube`
  -> `bvt_F_hasFlatRegularRepr`
  -> `bvt_F_boundary_continuous_at_real_support`
  -> `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`
  -> `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
  -> `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
  -> `bvt_F_swapCanonical_pairing_of_adjacent_chain`
  -> `bvt_F_swapCanonical_pairing`.
  Any forward-Jost upgrade route is blocked-only fallback unless an exact
  production theorem first closes it.
- The theorem-2 route contract is also fixed slot-by-slot now:
  - `choose_real_open_edge_for_adjacent_swap` must consume checked
    `exists_real_open_nhds_adjSwap` plus theorem-2 support inclusion and export
    the chosen real-edge / swapped-edge package;
  - `bvt_F_hasFlatRegularRepr` must consume checked `bvt_F_holomorphic`,
    `bvt_boundary_values`, and the explicit growth field already packaged on
    the boundary-data lane, then export the flat-regular witness used by both
    continuity and canonical recovery;
  - `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` is the
    actual non-circular adjacent raw-boundary closure theorem; it consumes the
    Route-B edge package plus `bvt_F_boundary_continuous_at_real_support` and
    checked `analytic_boundary_local_commutativity_of_boundary_continuous`, and
    only then may `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`
    repackage it for the theorem-2 boundary-pairing lane;
  - `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` must consume the
    flat-regular witness together with checked
    `boundary_value_recovery_forwardTube_of_flatRegular_from_bv` specialized at
    `bvt_W`, `bvt_W_continuous`, `bvt_boundary_values`, and
    `canonicalForwardConeDirection`;
  - `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` now has a
    frozen local proof transcript: call
    `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` first, then apply
    `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` on the swapped
    (`g`) side, then on the unswapped (`f`) side, and only then close by
    transitivity/symmetry;
  - `bvt_F_swapCanonical_pairing_of_adjacent_chain` is a separate finite-
    composition reducer above that theorem and may consume only the adjacent
    canonical theorem plus explicit adjacent-step factorization data, not the
    raw-boundary theorem or boundary-recovery specialization directly, before
    the frontier theorem closes.
- Theorem-2 file-locus contract is now explicit at the package level too:
  Route-B ET-support geometry theorems belong under the checked
  BHW-permutation adjacent-swap support subfile layer, not in the umbrella
  `.../BHWPermutation.lean` by default; `.../Adjacency.lean` is the default
  home for lower pointwise/open-edge suppliers, while
  `.../AdjacencyDistributional.lean` is the checked distributional pairing
  surface they must feed. More sharply, the checked tree already exposes
  `Adjacency.lean :: exists_real_open_nhds_adjSwap` as the lower local
  compactness/open-neighborhood supplier, so the theorem-2-facing wrapper
  `choose_real_open_edge_for_adjacent_swap` should be implemented as a support-
  inclusion package on top of that theorem rather than as a fresh rediscovery
  of the Route-B open-edge proof. The wrapper split is now fixed too:
  `choose_real_open_edge_for_adjacent_swap` = compact-support finite-cover
  packaging above `exists_real_open_nhds_adjSwap`;
  `swapped_support_lies_in_swapped_open_edge` = support transport only via the
  swap identity `g x = f (x ∘ swap)`;
  `swapped_open_edge_embeds_in_extendedTube` = ET transport only from the
  chosen edge to the swapped preimage edge. The raw-boundary wrapper theorem
  belongs with the BHW-extension boundary-pairing layer, the canonical-shift
  adapter and the general-swap adjacent-chain reducer
  `bvt_F_swapCanonical_pairing_of_adjacent_chain` belong in
  `.../OSToWightmanBoundaryValueLimits.lean`, and the frontier theorem in
  `.../OSToWightmanBoundaryValues.lean` should remain a thin final consumer.
  Checked-file caution: `.../OSToWightmanBoundaryValueLimits.lean` is present
  in the current tree, but it still contains only theorem-3-side
  `singleSplit_xiShift` / positive-time limit results. So the theorem-2
  canonical-direction recovery package there is still missing support work and
  must be introduced under separate theorem names and a separate local
  subsection, not by treating the existing `singleSplit_xiShift` shell as if
  it already closed theorem 2.
- The theorem-2 endgame pseudocode should now be read literally on that same
  Route-B package: `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` should open
  with `choose_real_open_edge_for_adjacent_swap`, then pass through
  `swapped_support_lies_in_swapped_open_edge` and
  `swapped_open_edge_embeds_in_extendedTube`, rather than switching back to a
  Route-A-style forward-Jost support closure at the last step.
- Route-B theorem-slot naming is now part of the doc contract too: later
  locality notes may add subordinate local-cover helper lemmas for the compact
  support / openness argument, but they should still close back onto the same
  top-level package names
  `choose_real_open_edge_for_adjacent_swap`,
  `swapped_support_lies_in_swapped_open_edge`, and
  `swapped_open_edge_embeds_in_extendedTube` rather than introducing a second
  competing theorem-slot vocabulary for the same geometry layer.
- For `boundary_values_tempered`: the generic DCT/integrability/tempered-boundary package is now in `SCV/LaplaceSchwartz.lean`; the genuine missing content is deriving the two growth hypotheses `hpoly` and `hunif` from the OS input.
- For theorem 4 / `bvt_cluster`: the next doc-level target after the corrected bridge theorem
  `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
  is the explicit public adapter package
  `canonical_cluster_integrand_eq_singleSplit_integrand -> canonical_translate_factor_eq_singleSplit_translate_factor -> singleSplit_core_rewrites_to_canonical_shell -> canonical_shell_limit_of_rewrite -> bvt_cluster_canonical_from_positiveTime_core`.
  The contract is now sharper than a slot-name list:
  `canonical_cluster_integrand_eq_singleSplit_integrand` may consume only the
  checked canonical-direction inputs
  `canonicalForwardConeDirection` / `canonicalForwardConeDirection_mem` plus the
  repaired base-core shell statement; `canonical_translate_factor_eq_singleSplit_translate_factor`
  may consume only `translateSchwartzNPoint` plus that same canonical-direction
  surface and the translated-shell statement shape of private
  `bvt_F_clusterCanonicalEventually_translate`; and only
  `canonical_shell_limit_of_rewrite` may consume only the checked
  `OSToWightmanBoundaryValueLimits.lean` scalar-holomorphic package, after the
  earlier two adapter rewrites have already rebuilt the exact canonical-shell
  statement shape. So `canonical_shell_limit_of_rewrite` is a pure
  limit-transport slot, not a mixed rewrite/transport theorem. The
  direct theorem-4 inputs are now source-checked at exact anchors:
  `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` (line 273),
  `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq` (line 290),
  `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`
  (line 446), and `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
  (line 536). The object `bvt_singleSplit_xiShiftHolomorphicValue` itself
  (line 260) is only the underlying scalar holomorphic function, not an extra
  adapter theorem step. The shell-level adapter row right above that limit
  slot is now frozen more explicitly too: `singleSplit_core_rewrites_to_canonical_shell`
  is not allowed to say only “rewrite the integrand and translated factor”. It
  must run as a literal five-step shell-local transcript on the exact frontier
  shell at `OSToWightmanBoundaryValues.lean:398`: first freeze the full
  quantifier block `(n, m, f, g, ε, a, t)`; second rewrite only the analytic
  kernel
  `bvt_F OS lgc (n + m) (fun k μ => ↑(x k μ) + t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)`
  via `canonical_cluster_integrand_eq_singleSplit_integrand`; third rewrite
  only the translated test-function factor
  `((f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x)` via
  `canonical_translate_factor_eq_singleSplit_translate_factor`; fourth verify
  that the eventual/limit quantifier block is unchanged and the shell now
  matches the ordered-positive-time single-split statement verbatim; fifth and
  only then apply `bvt_cluster_positiveTime_singleSplit_core`. The internal
  order of the later pure limit slot is frozen as
  `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
  -> optional right-half-plane uniqueness only via
  `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` +
  `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
  -> final Wightman-target `t -> 0+` transport only via
  `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`.
  Read that as a literal local theorem-construction order, not just a proof
  hint: `canonical_shell_limit_of_rewrite` must begin from the shell statement
  already exported by `singleSplit_core_rewrites_to_canonical_shell`, keep that
  shell fixed while introducing the scalar holomorphic object, and then perform
  only the three allowed moves above. It may not reopen the canonical-kernel
  rewrite, the translated-factor rewrite, or the base-core application. Dually,
  `bvt_cluster_canonical_from_positiveTime_core` is not a second transport
  theorem: it is only the public restatement of that already-fixed eventual
  canonical-shell statement, with no direct `BoundaryValueLimits.lean`
  imports and no leftover shell normalization, uniqueness, or limit work.
  The Schwinger-target theorems
  `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`
  (line 314) and
  `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
  (line 350) remain supplier-only lower legs, the lower helper
  `eqOn_rightHalfPlane_of_ofReal_eq` (line 494) stays quarantined beneath
  `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`, and the live
  consumer boundary is source-checked as `OSToWightmanBoundaryValueLimits.lean`
  `:388/:446/:494/:536`: the deprecated bridge
  `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
  at `:388` is historical/quarantined only with no direct theorem-4 consumer,
  while `:446` is the sole allowed terminal limit theorem on this lane. This
  forbids later Lean work from smuggling extra limit
  transport into the earlier rewrite theorems or from hiding the
  translated-shell statement shape inside the final frontier `sorry`.
  The first still-missing theorem-4 work is even earlier, though: the positivity-side
  bookkeeping package may not be hidden inside `cluster_left_factor_transport`.
  The left-factor lane is now frozen as a literal post-extraction transcript:
  (1) begin only from the already-packaged extraction lemmas
  `zeroDegree_right_single_wightman_extracts_factor` and
  `zeroDegree_right_single_os_extracts_factor`, so the checked suppliers
  `OSReconstruction/Wightman/Reconstruction/Core.lean:393 ::
  WightmanInnerProduct_right_single` and
  `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean:466 ::
  OSInnerProduct_right_single` plus the degree-`0` normalization / cast-cleanup
  queue have already been consumed upstream; (2) import the theorem-3 transport
  comparison only through the unique surviving `m = 0` slot
  `zero_degree_component_comparison_for_normalized_right_vector`; (3)
  substitute the extracted Wightman and OS left-factor formulas into that
  `m = 0` comparison shell; (4) close `cluster_left_factor_transport` without
  reopening witness manufacture, scalar normalization, right-single algebra, or
  any hidden helper theorem. So `cluster_left_factor_transport` itself is not
  allowed to import `WightmanInnerProduct_right_single`,
  `OSInnerProduct_right_single`, `conjTensorProduct_degreeZeroUnit_eq`,
  `osConjTensorProduct_degreeZeroUnit_eq`, or
  `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq` directly; all of that
  work must already be packaged below it.
  The initial Lean execution order is now fixed as
  `normalizedZeroDegreeRightVector -> normalizedZeroDegreeRightVector_bound / ..._funcs_zero / ..._funcs_pos -> conjTensorProduct_degreeZeroUnit_eq -> osConjTensorProduct_degreeZeroUnit_eq -> ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq -> zeroDegree_right_single_wightman_extracts_factor -> zeroDegree_right_single_os_extracts_factor -> zero_degree_component_comparison_for_normalized_right_vector -> cluster_left_factor_transport -> cluster_right_factor_transport`.
  Read that queue as a literal theorem-creation census, not a slogan:
  - **12-slot positivity/extraction package** in
    `OSToWightmanPositivity.lean`:
    `normalizedZeroDegreeRightVector`,
    `normalizedZeroDegreeRightVector_bound`,
    `normalizedZeroDegreeRightVector_funcs_zero`,
    `normalizedZeroDegreeRightVector_funcs_pos`,
    `conjTensorProduct_degreeZeroUnit_eq`,
    `osConjTensorProduct_degreeZeroUnit_eq`,
    `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`,
    `zeroDegree_right_single_wightman_extracts_factor`,
    `zeroDegree_right_single_os_extracts_factor`,
    `zero_degree_component_comparison_for_normalized_right_vector`,
    `cluster_left_factor_transport`,
    `cluster_right_factor_transport`;
  - **2-slot repaired base bridge** in
    `OSToWightmanBoundaryValuesBase.lean`:
    `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
    then `bvt_cluster_positiveTime_singleSplit_core`;
  - **5-slot public canonical-shell adapter** in
    `OSToWightmanBoundaryValues.lean`:
    `canonical_cluster_integrand_eq_singleSplit_integrand`
    -> `canonical_translate_factor_eq_singleSplit_translate_factor`
    -> `singleSplit_core_rewrites_to_canonical_shell`
    -> `canonical_shell_limit_of_rewrite`
    -> `bvt_cluster_canonical_from_positiveTime_core`.
  Only after those 19 upstream slots are present should later Lean work touch
  the checked private frontier as a final consumer.
  Source-check refinement on that first extraction pair: theorem 4 owns the
  planned slots `zeroDegree_right_single_wightman_extracts_factor` and
  `zeroDegree_right_single_os_extracts_factor` in
  `OSToWightmanPositivity.lean`, but the checked supplier theorems they must
  consume already live in `OSReconstruction/Wightman/Reconstruction/Core.lean:393
  :: WightmanInnerProduct_right_single` and
  `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean:466 ::
  OSInnerProduct_right_single`. So the job is packaging those checked
  right-single surfaces against the new degree-`0` witness package, not
  reproving right-single identities inside the positivity file. More sharply,
  the extraction lemmas themselves must now be read as literal Lean-order
  transcripts rather than mere dependency names:
  `zeroDegree_right_single_wightman_extracts_factor`
  = instantiate `WightmanInnerProduct_right_single`
  -> rewrite the normalized degree-`0` witness with
  `normalizedZeroDegreeRightVector_funcs_zero`
  -> kill every positive-degree tail with
  `normalizedZeroDegreeRightVector_funcs_pos`
  -> rewrite the surviving degree-`0` classical tensor term by
  `conjTensorProduct_degreeZeroUnit_eq`
  -> remove the remaining cast by
  `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`;
  `zeroDegree_right_single_os_extracts_factor`
  = instantiate `OSInnerProduct_right_single`
  -> rewrite the normalized degree-`0` witness with
  `normalizedZeroDegreeRightVector_funcs_zero`
  -> kill positive-degree tails with
  `normalizedZeroDegreeRightVector_funcs_pos`
  -> rewrite the surviving degree-`0` OS tensor term by
  `osConjTensorProduct_degreeZeroUnit_eq`
  -> remove the remaining cast by
  `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`.
  There is no extra theorem slot for scalar normalization in between. The right-factor
  lane is now frozen at the same granularity: later Lean work must
  (1) instantiate `normalizedZeroDegreeLeftVector d :=
  normalizedZeroDegreeRightVector d` by definitional equality only,
  (2) import no new structural/normalization lemmas beyond
  `normalizedZeroDegreeRightVector_bound` / `..._funcs_zero` /
  `..._funcs_pos`,
  (3) package only those checked supplier theorems into the right-side
  extraction slots `zeroDegree_right_single_wightman_extracts_factor` and
  `zeroDegree_right_single_os_extracts_factor`,
  (4) consume `zero_degree_component_comparison_for_normalized_right_vector`,
  and only then
  (5) close `cluster_right_factor_transport`.
  Current source-check against the checked repo-relative loci:
  - `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
    is the theorem-3 transport supplier theorem 4 must consume, and under the
    current doc contract it also owns the entire missing positivity-side
    bookkeeping/extraction chain:
    `normalizedZeroDegreeRightVector`,
    `normalizedZeroDegreeRightVector_bound`,
    `normalizedZeroDegreeRightVector_funcs_zero`,
    `normalizedZeroDegreeRightVector_funcs_pos`,
    `conjTensorProduct_degreeZeroUnit_eq`,
    `osConjTensorProduct_degreeZeroUnit_eq`,
    `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`,
    `zeroDegree_right_single_wightman_extracts_factor`,
    `zeroDegree_right_single_os_extracts_factor`,
    `zero_degree_component_comparison_for_normalized_right_vector`,
    `cluster_left_factor_transport`, and
    `cluster_right_factor_transport`; direct source check now records that all
    of those theorem-4 extraction names are still planned slots rather than
    checked-present lemmas in the current file;
  - `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean`
    already has the base reductions at exact anchors
    `:2214 :: bvt_F_clusterCanonicalEventually_translate_of_singleSplitLargeSpatial`,
    `:2352 :: bvt_F_clusterCanonicalEventually_translate_of_singleSplitSchwingerLargeSpatial`,
    and `:2514 :: bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`,
    and it is the designated home for the repaired positive-time bridge
    `...of_singleSplitTransportComparison` together with the thin wrapper
    `bvt_cluster_positiveTime_singleSplit_core`; those corrected transport-input
    names are still missing from the checked file today. The base-file bridge
    transcript is now frozen more explicitly too: (1) begin from exactly those
    checked base anchors `:2214`, `:2352`, and `:2514`; (2) instantiate the
    legacy `...singleSplitFactorComparison` shell without changing its quantifier
    order or eventual/positive-time statement shape; (3) replace only the two
    false same-shell hypotheses by `cluster_left_factor_transport` and
    `cluster_right_factor_transport`; (4) close the repaired theorem under the
    new name `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
    with no canonical-direction rewrites, no translated-factor rewrites, and no
    `BoundaryValueLimits.lean` imports; (5) package that repaired theorem once,
    and only once, into `bvt_cluster_positiveTime_singleSplit_core`; (6) treat
    that wrapper as the sole theorem allowed to leave the base file and enter
    the public adapter ladder, with first downstream consumer fixed as
    `canonical_cluster_integrand_eq_singleSplit_integrand` and the remaining
    wrapper-file queue fixed as
    `canonical_translate_factor_eq_singleSplit_translate_factor`
    -> `singleSplit_core_rewrites_to_canonical_shell`
    -> `canonical_shell_limit_of_rewrite`
    -> `bvt_cluster_canonical_from_positiveTime_core`.
    These three exact anchors are now the only admissible checked base inputs
    on the theorem-4 bridge lane, and
    `bvt_cluster_positiveTime_singleSplit_core` is the sole theorem allowed to
    leave the base file and enter the public adapter ladder;
  - `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
    has the final private wrapper
    `bvt_F_clusterCanonicalEventually_translate`, its translated wrapper,
    the public transfer theorem `bv_cluster_transfer_of_canonical_eventually`,
    and the exported consumer `bvt_W_cluster`; it is also the designated home
    for the still-missing public canonical-shell adapter package rather than a
    place to hide the repaired positive-time bridge itself. Direct source check
    now fixes the checked-present theorem shell there exactly as
    `:27 :: bv_cluster_transfer_of_canonical_eventually`,
    `:398 :: private bvt_F_clusterCanonicalEventually_translate`,
    `:414 :: private bvt_F_clusterCanonicalEventually`, and
    `:473 :: private bvt_W_cluster`, with the named adapter package still
    absent under separate theorem names. The final
    theorem-facing contract is now strict too: private
    `bvt_F_clusterCanonicalEventually_translate` should consume only
    `bvt_cluster_canonical_from_positiveTime_core`, so the literal frontier
    boundary is frozen as
    `canonical_shell_limit_of_rewrite`
    -> `bvt_cluster_canonical_from_positiveTime_core`
    -> `OSToWightmanBoundaryValues.lean:398 :: private bvt_F_clusterCanonicalEventually_translate`,
    while the adapter package itself must run in the explicit order
    `canonical_cluster_integrand_eq_singleSplit_integrand`
    -> `canonical_translate_factor_eq_singleSplit_translate_factor`
    -> `singleSplit_core_rewrites_to_canonical_shell`
    -> `canonical_shell_limit_of_rewrite`
    -> `bvt_cluster_canonical_from_positiveTime_core`;
    the last two rows are not interchangeable or compressible: first create
    `canonical_shell_limit_of_rewrite` as the only theorem allowed to touch the
    checked `BoundaryValueLimits.lean` package, and only after its exported
    eventual canonical-shell statement is fixed introduce
    `bvt_cluster_canonical_from_positiveTime_core` as a one-line public shell
    restatement. The final private frontier theorem may not absorb either of
    those jobs.
    the file-ownership boundary is now frozen even more literally:
    `canonical_cluster_integrand_eq_singleSplit_integrand` is the **first**
    theorem-4 slot allowed to live in this wrapper file, and it may consume
    only `canonicalForwardConeDirection` /
    `canonicalForwardConeDirection_mem` together with the exported base theorem
    `bvt_cluster_positiveTime_singleSplit_core`. It may not pull theorem-3
    scalar/limit transport directly, and it may not bypass the repaired base
    seam by importing `cluster_left_factor_transport`,
    `cluster_right_factor_transport`, or
    `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`.
    inside that limit slot, the suborder is also frozen:
    `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
    -> optional right-half-plane uniqueness via
    `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` and
    `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
    -> final Wightman-target limit transport by
    `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`.
    The Schwinger-target theorems
    `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`
    and
    `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
    are supplier-only lower legs here. Source-check the checked alternatives in
    `OSToWightmanBoundaryValueLimits.lean`: `:388`
    (`tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`)
    is historical/quarantined only with no direct theorem-4 consumer, whereas
    `:446` is the sole admissible terminal limit theorem and `:494 -> :536`
    remain uniqueness-only infrastructure;
  - `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`
    is *not* the theorem-4 home under the current checked-tree contract; it
    remains theorem-2/theorem-3 support infrastructure;
  - the intermediate adapter package is still missing under separate theorem
    names and should be introduced explicitly rather than hidden inside the
    final `sorry`.
  - implementation order rule for this lane: do not start theorem 4 by trying
    to prove `cluster_left_factor_transport` or `cluster_right_factor_transport`
    directly. First land the degree-0 normalization witness and its structural
    lemmas, then the two right-single extraction lemmas, then the `m = 0`
    comparison theorem; for the right-factor lane, reuse that same package by
    definitional alias rather than building a second left-normalization family.
    Only after that is the one-factor transport pair mature enough to feed the
    repaired base-file bridge. Dually, do not start the final wrapper by trying
    to prove private `bvt_F_clusterCanonicalEventually_translate` directly.
    First close the named canonical-shell adapter package in the order just
    listed, so the final private theorem is reduced to a one-line consumer of
    `bvt_cluster_canonical_from_positiveTime_core` rather than a mixed
    rewrite/limit proof block.

### 2. `SCV` load-bearing infrastructure (2)

`SCV/PaleyWiener.lean`:
- sorry-free
- no fake multidimensional Fourier-support interface remains
- only the 1D and slice-wise theorems are active

`SCV/LaplaceSchwartz.lean` (0):

Status:
- the interface split is now honest:
  - weak `HasFourierLaplaceRepr`
  - regular `HasFourierLaplaceReprRegular`
- the fake weak-to-regular upgrade theorem has been removed
- the generic boundary-distribution lemmas needed by `boundary_values_tempered`
  are now extracted:
  - `integrable_poly_weight_schwartz`
  - `integrable_poly_growth_schwartz`
  - `tendsto_boundary_integral`
  - `boundary_distribution_bound`
- the real missing theorem is now explicit: construct the growth inputs and/or
  regular package from actual Fourier-Laplace input with the right dual-cone support

`SCV/TubeDistributions.lean` (0):

Status:
- the weak bare-BV theorem fronts were removed instead of being carried as public placeholders
- only the rigorous regular variants remain, built from explicit regular input data

`SCV/BochnerTubeTheorem.lean` (2):
- `bochner_local_extension`
- `bochner_tube_extension`

Status:
- the old generic gluing theorem was too strong and has been replaced by the honest compatible-family theorem

### 3. `Reconstruction/ForwardTubeDistributions.lean` (0) — COMPLETE

**`distributional_uniqueness_forwardTube` — PROVED** (commit 5813d37).
Proof: flattening via `flattenCLEquiv` + `distributional_uniqueness_tube_of_zero_bv`.

All weak-BV sorrys eliminated. Only proved regular variants remain.

Infrastructure (sorry-free):
- `SCV/DistributionalUniqueness.lean`: `distributional_uniqueness_tube_of_zero_bv`,
  `exists_integral_clm_of_continuous` (truncation → CLM via Banach-Steinhaus),
  `eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`
- `SCV/SchwartzComplete.lean`: `CompleteSpace`, `BarrelledSpace`, Banach-Steinhaus chain

### 4. Wick rotation downstream

`WickRotation/SchwingerTemperedness.lean` (2):
- `wick_rotated_kernel_mul_zeroDiagonal_integrable`
- `constructedSchwinger_tempered_zeroDiagonal`

`WickRotation/SchwingerAxioms.lean` (2 actual holes + 1 quarantined wrapper):
- live direct `sorry`: `schwingerExtension_os_term_eq_wightman_term`
- live direct `sorry`: `W_analytic_cluster_integral`
- checked-present but quarantined wrapper:
  `wickRotatedBoundaryPairing_reflection_positive`

Current blocker sharpening (2026-04-08):
- `bhw_euclidean_reality_ae` and `bhw_pointwise_cluster_forwardTube` are no
  longer live holes in this file; they are now checked supplier theorems that
  later reverse packaging may consume.
- `schwingerExtension_os_term_eq_wightman_term` is the false OS=`Wightman`
  identification lane and should stay quarantined rather than reused as a
  stepping stone for future reverse positivity.

Reverse late-field execution ledger:

- `E2_reflection_positive`
  - `wickRotated_positiveTimeCore`
    - owner: `WickRotation/SchwingerAxioms.lean`
    - consumes: the reverse positive-time test-function setup
    - exports: the honest positive-time core
    - next consumer:
      `wickRotatedBoundaryPairing_eq_transport_inner_on_core`
  - `wickRotatedBoundaryPairing_eq_transport_inner_on_core`
    - owner: `WickRotation/SchwingerAxioms.lean`
    - consumes: `wickRotated_positiveTimeCore`
    - exports: core-level identification with the Section-4.3 transport inner
      product
    - next consumer: `wickRotatedBoundaryPairing_nonneg_on_core`
  - `wickRotatedBoundaryPairing_nonneg_on_core`
    - owner: `WickRotation/SchwingerAxioms.lean`
    - consumes:
      `wickRotatedBoundaryPairing_eq_transport_inner_on_core`
    - exports: nonnegativity on the core
    - next consumer: `wickRotated_positiveTimeCore_dense`
  - `wickRotated_positiveTimeCore_dense`
    - owner: `WickRotation/SchwingerAxioms.lean`
    - consumes: the same positive-time core setup
    - exports: density of the honest core
    - next consumer:
      `wickRotatedBoundaryPairing_nonneg_by_density`
  - `wickRotatedBoundaryPairing_nonneg_by_density`
    - owner: `WickRotation/SchwingerAxioms.lean`
    - consumes:
      `wickRotatedBoundaryPairing_nonneg_on_core` and
      `wickRotated_positiveTimeCore_dense`
    - exports: the full reverse positivity inequality on the boundary pairing
    - next consumer: `constructSchwinger_positive`
  - `constructSchwinger_positive`
    - owner: `Reconstruction/SchwingerOS.lean:774` (adjacent to the target
      field; repo-tree check confirms there is currently no separate reverse
      packaging support file for this last E2 slot)
    - consumes: `wickRotatedBoundaryPairing_nonneg_by_density`
    - exports: the actual field witness for
      `OsterwalderSchraderAxioms.E2_reflection_positive`
    - next consumer:
      `OsterwalderSchraderAxioms.E2_reflection_positive`
    - local packaging transcript: instantiate the exact positive-time family
      from the field statement, rewrite its pairing surface to
      `wickRotatedBoundaryPairing_nonneg_by_density`, use that theorem to close
      the nonnegativity inequality, then package the final field witness by
      definitional rewriting
  - quarantine note:
    `wickRotatedBoundaryPairing_reflection_positive` is only a checked-present
    wrapper. It still closes through
    `schwingerExtension_os_inner_product_eq_wightman` /
    `schwingerExtension_os_inner_product_eq_wightman_positivity`, so it is not
    an honest supplier on this route.

- `E4_cluster`
  - `W_analytic_cluster_integral`
    - owner: `WickRotation/SchwingerAxioms.lean`
    - consumes: the fixed supplier transcript
      `sector partition -> identity-sector ForwardTube application of
      bhw_pointwise_cluster_forwardTube -> permutation rewrite on bad sectors
      -> uniform HasForwardTubeGrowth majorant -> sectorwise dominated
      convergence -> finite sector sum / block factorization`
    - exports: the live common-BHW / full-`SchwartzNPoint` cluster supplier
    - next consumer: `wickRotatedBoundaryPairing_cluster`
  - `wickRotatedBoundaryPairing_cluster`
    - owner: `WickRotation/SchwingerAxioms.lean`
    - consumes: `W_analytic_cluster_integral`
    - exports: the checked full-`SchwartzNPoint` wrapper
    - next consumer:
      `constructSchwinger_cluster_translate_adapter`
  - `constructSchwinger_cluster_translate_adapter`
    - owner: reverse packaging layer targeting
      `Reconstruction/SchwingerOS.lean:802-804`
    - consumes: only `g : ZeroDiagonalSchwartz d m` plus the spatial
      translation vector `a`; it does **not** consume
      `wickRotatedBoundaryPairing_cluster`
    - exports: the translated witness
      `g_a : ZeroDiagonalSchwartz d m`
    - next consumer:
      `constructSchwinger_cluster_tensor_adapter`, `constructSchwinger_cluster`
    - local adapter transcript: define `g_a`, prove the literal pointwise
      translate formula demanded by the field quantifier, and package the same
      zero-diagonal side conditions before the cluster wrapper enters
  - `constructSchwinger_cluster_tensor_adapter`
    - owner: same reverse packaging layer above
      `Reconstruction/SchwingerOS.lean:804-807`
    - consumes: only `f : ZeroDiagonalSchwartz d n` and the translated witness
      `g_a`; it still does **not** consume `wickRotatedBoundaryPairing_cluster`
    - exports: the tensor witness
      `fg_a : ZeroDiagonalSchwartz d (n + m)` with
      `fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)`
    - next consumer: `constructSchwinger_cluster`
    - local adapter transcript: define `fg_a`, prove the exact tensor shell
      required by the field statement, and package its zero-diagonal side
      conditions before the final inequality theorem is invoked
  - `constructSchwinger_cluster`
    - owner: reverse packaging layer targeting
      `Reconstruction/SchwingerOS.lean:792`
    - consumes:
      `wickRotatedBoundaryPairing_cluster`, `g_a`, and `fg_a`
    - exports: the final field inequality witness for
      `OsterwalderSchraderAxioms.E4_cluster`
    - local packaging transcript: rewrite the quantified field goal into the
      exact wrapper estimate `wickRotatedBoundaryPairing_cluster`, substitute
      the explicit translated witness `g_a`, substitute the explicit tensor
      witness `fg_a`, and only then discharge the final norm inequality
    - next consumer: `OsterwalderSchraderAxioms.E4_cluster`

- Reverse-proof-doc contract sharpened (2026-04-08): if the repo later upgrades
  the current minimal bridge `wightman_to_os_full` to a full
  `OsterwalderSchraderAxioms` theorem, the file-level packaging order is now
  frozen as
  `E0_tempered -> E0_linear -> E0_reality -> E3_symmetric -> constructSchwinger_translation_covariant_BHW -> constructSchwinger_translation_invariant -> constructSchwinger_rotation_covariant_BHW -> constructSchwinger_rotation_invariant -> E2_reflection_positive -> E4_cluster`.
  The already-checked reverse packaging inputs must also stay explicit:
  `constructedSchwinger_tempered_zeroDiagonal`,
  `constructedZeroDiagonalSchwinger_linear`,
  `wickRotatedBoundaryPairing_reality`,
  `wickRotatedBoundaryPairing_symmetric`, and the split checked E1 consumers
  `F_ext_translation_invariant -> wickRotatedBoundaryPairing_translation_invariant`
  plus
  `F_ext_rotation_invariant -> wickRotatedBoundaryPairing_rotation_invariant`.
  The structure target is `OS.S = constructSchwingerFunctions Wfn`, not the
  derived accessor `OS.schwinger = ...`.
  In particular, the split `E1` package is no longer allowed to hide behind a
  bundled `EuclideanInvariance` theorem name; both field-shaped theorem slots
  belong to `SchwingerAxioms.lean` and must transport covariance through the
  common BHW analytic object before the later `E2` / `E4` transport packages,
  with only the planned `constructSchwinger_translation_covariant_BHW` /
  `constructSchwinger_rotation_covariant_BHW` slots allowed to touch the public
  group/bridge route and the later `*_invariant` slots restricted to pure
  Wick-restriction packaging.

`WickRotation/ForwardTubeLorentz.lean` (2):
- `polynomial_growth_on_slice`
- `wickRotation_not_in_PET_null`

`WickRotation/BHWTranslation.lean` (1):
- `isPreconnected_baseFiber` (base-variable fiber connectivity in PET)
  - STATUS ON MERGED PATH: no longer needed to prove `bhw_translation_invariant`
  - CURRENT ROLE: old-route residual theorem, kept as a separate geometric target
  - ROOT CAUSE: our ForwardTube k=0 condition `Im(z₀) ∈ V⁺` breaks translation invariance
  - MATHEMATICAL PROOF: PET is a domain of holomorphy (BEG 1967). baseFiber = PET ∩ (complex affine subspace). Intersection of DOH with complex affine subspace is connected (standard SCV).
  - Alternative proof: fiber bundle over contractible base (tailDiffPermSector is convex) with connected fiber (stabilizer in SO(d+1;ℂ) is connected). See Proofideas/baseFiber_inflation_proof.lean.
  - PROVED helpers (0 sorrys): inOpenForwardCone_add_time, forwardTube_add_broadcast_iTime, complexLorentzAction_add_broadcast, lorentz_action_inflation_dir (in test/proofideas_baseFiber_inflation.lean)
  - Production reduction: baseFiber_isPreconnected_of_index_and_active_geometry reduces to index set connectivity + sector overlap
  - FORMALIZATION GAP: needs SCV domain-of-holomorphy infrastructure OR Lie group fiber bundle theory, neither in Mathlib

`WickRotation/BHWReducedExtension.lean` (axiom 1):
- `reduced_bargmann_hall_wightman_of_input`
  - accepted as a strategically deferred reduced-coordinate BHW bridge
  - this is the Route 1 replacement for the old base-fiber route on the merged path
  - intended future discharge: descend the absolute BHW theorem through
    translation invariance / quotient geometry
  - see `docs/reduced_bhw_bridge_and_numerics.md`

`WickRotation/BHWExtension.lean` (0):
- Honest extendF-level adjacent-swap theorems are complete.
- If raw real-edge values are ever needed again, the remaining mathematical input is
  boundary continuity of the spectrum witness on the real ET edge, not more EOW/BHW infrastructure.

New proved theorems (2026-03-10):
- `W_analytic_swap_boundary_pairing_eq` — PROVED via distributional chain
- `analytic_extended_local_commutativity` — pointwise swap for `extendF` at real ET points
- `analytic_boundary_local_commutativity_of_boundary_continuous` — raw W_analytic with honest ContinuousWithinAt hypotheses

Current assessment:
- `R→E` has two independent hard roots:
  - coincidence-singularity / zero-diagonal integrability
  - Euclidean reality / reflection
- the `boundary_values_tempered` extraction work on the E→R side does not by itself close either of those; it mainly prepares the tempered Wightman boundary package after E→R continuation exists

## Secondary Blockers

Not on the shortest OS reconstruction lane:
- `Wightman/Reconstruction/Main.lean:74`: `wightman_uniqueness`, but no longer as a vague endgame label: after `GNSHilbertSpace.lean :1005 -> :1062 -> :1249 -> :1643 -> :2114`, the Main-file lane is fixed as `cyclicWordVector/cyclicWordSpan -> cyclicWordVector_inner_cyclicWordVector -> uniquenessPreMap -> uniquenessPreMap_inner_formula -> uniquenessPreMap_null_of_null -> uniquenessDenseMap -> uniquenessDenseMap_inner_preserving -> uniquenessDenseMap_norm_preserving -> uniquenessDenseMap_isometry -> cyclicWord_in_range_of_uniquenessDenseMap -> cyclicWordSpan_le_range_uniquenessDenseMap -> uniquenessDenseMap_denseRange -> uniquenessDenseMap_extends_to_unitary -> uniquenessUnitary_maps_vacuum -> uniquenessUnitary_intertwines_field_on_cyclic_core -> cyclicWordSpan_is_field_core -> uniquenessUnitary_intertwines_field -> wightman_uniqueness`, with no reopening of spectrum, nuclear, or cyclicity bridge work. Source-check the ownership split literally: the repo has `Main.lean` itself but no separate uniqueness-support Lean file, so the helper-lemma package currently lives only in `docs/wightman_uniqueness_blueprint.md`. The physical insertion contract is fixed here too: later Lean work must either place the whole helper queue directly into `Main.lean` above line 74, or first create one explicitly named helper file under `Wightman/Reconstruction/` and move a contiguous theorem block there with synchronized docs/imports; it may not act as if an unnamed helper file already owns part of the queue, and it may not scatter the uniqueness slots across unrelated existing reconstruction files. First-consumer boundaries are fixed here too: cyclic-word matrix-element transfer first enters only at `uniquenessPreMap_inner_formula`, quotient descent ends at `uniquenessPreMap_null_of_null`, descended inner/norm preservation starts only after `uniquenessDenseMap`, dense-range work starts only at `cyclicWord_in_range_of_uniquenessDenseMap`, field-core closure starts only at `cyclicWordSpan_is_field_core`, and `Main.lean:74` is assembly-only.
- `Wightman/Reconstruction/GNSHilbertSpace.lean`: one remaining spectral-theory blocker
- `Wightman/WightmanAxioms.lean`: 4 infrastructural sorrys
- Nuclear-space / Bochner-Minlos support: this clone does contain a live checked
  `Wightman/NuclearSpaces/*` subtree (`NuclearSpace.lean`,
  `SchwartzNuclear.lean`, `GaussianFieldBridge.lean`,
  `BochnerMinlos.lean`, `EuclideanMeasure.lean`, `ComplexSchwartz.lean`, plus
  helpers), but the downstream reconstruction consumers still see only the two
  exported axiom surfaces `schwartz_nuclear_extension` and
  `exists_continuousMultilinear_ofSeparatelyContinuous` in
  `Wightman/WightmanAxioms.lean`. Treat the honest open problem here as an
  ownership/integration split: later work must distinguish checked local
  NuclearSpaces support files, downstream reconstruction-facing axiom/theorem
  surfaces, and any remaining bridge/import wrappers needed to connect them.
- `ComplexLieGroups` residual blockers: see the CLG status files

## Execution Order

1. Finish the live E→R root blocker `schwinger_continuation_base_step` in `OSToWightman.lean`.
   - keep the hard gap explicit
   - use the existing honest semigroup/spectral/Laplace infrastructure
   - do not add abstract wrappers that hide the remaining step
   - first close the nontrivial 2-point Schwinger reduction on `ZeroDiagonalSchwartz d 2` / an admissible Euclidean subspace
   - do not spend active effort on one-point classification or ambient full-Schwartz surrogate theorems
2. Keep `boundary_values_tempered` fixed at its checked file locus `OSToWightmanBoundaryValuesBase.lean`, and use the extracted SCV boundary-distribution lemmas plus the theorem-2 blueprint to isolate the genuine remaining continuity work: the flattened-growth transport / flat-regular constructor package in `ForwardTubeDistributions.lean`.
3. Keep the new tensor insertion infrastructure in `Wightman/SchwartzTensorProduct.lean` in mind if the continuation blocker turns into a genuine Schwartz kernel-extension theorem, but do not confuse that groundwork with closure of the live blocker.
4. After the theorem-2 continuity constructor package is fixed and the locality frontier closes cleanly, finish the six transfer theorems and `bvt_cluster` in `OSToWightmanBoundaryValues.lean`.
5. In parallel or next, attack the live R→E front after the Route 1 merge:
   - `SchwingerTemperedness.lean`: coincidence-singularity / zero-diagonal continuity
   - `SchwingerAxioms.lean`: Euclidean reality / reflection, OS=W term, cluster
   - `BHWTranslation.isPreconnected_baseFiber` is now optional old-route cleanup, not required for the merged proof path
6. Defer `StoneTheorem` / GNS operator-theoretic work until the analyticity lane is materially settled.
7. When the queue finally reaches `Main.lean:74`, keep the owner split literal: `GNSHilbertSpace.lean` stops at exporting `gnsQFT`, `Main.lean` still contains only the final theorem surface, and the implementation-facing helper queue remains documentation-owned in `docs/wightman_uniqueness_blueprint.md` until a real support module is added. The uniqueness lane must then prove, in order, the cyclic-word core, inner-product formula on that core, the transferred pre-map inner-product theorem `uniquenessPreMap_inner_formula`, null-vector descent, descended-map packaging, descended inner preservation, descended norm preservation, isometry, `cyclicWord_in_range_of_uniquenessDenseMap`, `cyclicWordSpan_le_range_uniquenessDenseMap`, `uniquenessDenseMap_denseRange`, unitary extension, vacuum transport, cyclic-core field intertwining, the separate core-closure theorem `cyclicWordSpan_is_field_core`, domain-level field intertwining, and only then `wightman_uniqueness`. Physical layout is part of that contract: either keep this whole queue in `Main.lean` above `:74`, or create one explicitly named new helper file under `Wightman/Reconstruction/` and move one contiguous theorem block there in the same pass; do not distribute those slots piecemeal across unrelated existing files.

## Recently Completed (2026-03-14)

### Fiberwise antiderivative chain — COMPLETE (0 sorrys in test file)
- `contDiff_fiberwiseAntiderivRaw` — C^∞ smoothness
- `decay_fiberwiseAntiderivRaw` — Schwartz decay at all orders (induction on p)
- `fiberwiseAntideriv` — SchwartzMap packaging
- `lineDeriv_fiberwiseAntideriv` — head derivative recovers F
- Ready for production extraction to `SliceIntegral.lean` (~165 lines)

### Production extractions landed
- `PartialToTotal.lean` — partial → total HasFDerivAt (0 sorrys)
- `SchwartzCutoff.lean` — schwartz_tail_decay (0 sorrys)
- `BEGTrigonometric.lean` — sinusoidal_pos_of_endpoints_pos (0 sorrys)
- `SliceIntegral.lean` — iicZeroSlice chain + intervalPiece chain + fiberwiseAntiderivRaw (0 sorrys, 1990 lines total)
- `TwoPointDescent.lean` — integral identities + center-shear translation (0 sorrys)

## Commands

```bash
rg -n '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
lake build OSReconstruction.SCV
lake build OSReconstruction.Wightman
```
