# Systematic Development Plan (OS Reconstruction Critical Path)

Last updated: 2026-03-16

This is the active execution plan for closing `sorry`s on the OS reconstruction path.
It supersedes the earlier BHW-first ordering.

## 0. Canonical roles of the status / proof docs

To avoid multiple competing "current truth" documents, use the files as
follows.

1. `docs/development_plan_systematic.md`:
   the canonical blocker ordering and execution plan.
2. `docs/proof_docs_completion_plan.md`:
   the canonical meta-plan for hardening proof blueprints into implementation
   contracts.
3. `docs/theorem2_locality_blueprint.md`,
   `docs/theorem3_os_route_blueprint.md`, and
   `docs/theorem4_cluster_blueprint.md`:
   the authoritative route contracts for the live frontier theorems.
4. `README.md`:
   repo overview and high-level status only; not the place for the most
   detailed blocker ledger.
5. module-local `TODO.md` files:
   lane-local blocker censuses and engineering notes; they do not override the
   theorem blueprints or this execution order.
6. theorem-blueprint file inventories are part of the contract:
   - theorem 3 inventory authority lives in
     `docs/theorem3_os_route_blueprint.md`;
   - theorem 4 inventory authority lives in
     `docs/theorem4_cluster_blueprint.md`;
   - any doc pass that moves theorem-package loci across files must update
     those inventories in the same pass.

## 1. Proof-Quality Policy (Hard Constraints)

1. No wrappers, no useless lemmas, no code bloat.
2. Every new lemma must either:
   - close a blocker directly, or
   - carry nontrivial reusable mathematical content needed downstream.
3. Do not add forwarding/repackaging lemmas that only rename existing statements.
4. Close `sorry`s with substantial proofs (not assumption padding or existential hiding).
5. Numerical checks are optional diagnostics; they are not required workflow gates.

## 2. Live Sorry Census

Counts verified against the current repo tree with a direct scan of
`OSReconstruction/**/*.lean` for lines matching `^\s*sorry(\s|$)`.

| Scope | Sorrys |
|---|---:|
| `OSReconstruction/Wightman` | 23 |
| `OSReconstruction/SCV` | 2 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 36 |
| **Total** | **63** |

Tracked production axioms:
- `schwartz_nuclear_extension` in `Wightman/WightmanAxioms.lean`
- `exists_continuousMultilinear_ofSeparatelyContinuous` in `Wightman/WightmanAxioms.lean`
- `vladimirov_tillmann` in `SCV/VladimirovTillmann.lean`
- `distributional_cluster_lifts_to_tube` in `SCV/VladimirovTillmann.lean`
- `tube_boundaryValueData_of_polyGrowth` in `SCV/TubeBoundaryValues.lean`
- `reduced_bargmann_hall_wightman_of_input` in
  `WickRotation/BHWReducedExtension.lean`

## 3. Primary Priority Stack

### A) E -> R direction (`OSToWightman*`, 8 sorrys)

The E -> R lane now has two distinct documentation layers and they must not be
blurred.

1. **Actual theorem-package loci inside the production files**
   - `OSToWightman.lean`: upstream root continuation theorem
     `schwinger_continuation_base_step`
   - `OSToWightmanBoundaryValuesBase.lean`:
     checked boundary-value existence package
     `boundary_values_tempered`, together with the already-present theorem-2
     continuity suppliers `bvt_F_holomorphic` and `bvt_boundary_values`
   - `OSToWightmanBoundaryValues.lean`:
     theorem-2 locality frontier `bvt_F_swapCanonical_pairing`, the
     downstream transfer chain, and the final cluster theorem wrapper
     `bvt_cluster`
   - `OSToWightmanPositivity.lean`: the theorem-3 checked support locus.
     A live source check now shows landed support surfaces
     `identity_theorem_right_halfplane`,
     `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`,
     `positiveTimeBorchersVector_dense`, and
     `euclideanPositiveTimeSingleVector`; the fully split Section-4.3
     transport/closure theorem names in the blueprint remain planned
     theorem-slot targets rather than already-landed production lemmas
2. **Theorem-blueprint contracts controlling those files**
   - `docs/theorem2_locality_blueprint.md`
   - `docs/theorem3_os_route_blueprint.md`
   - `docs/theorem4_cluster_blueprint.md`

Clusters:
1. Upstream continuation blocker:
   - `OSToWightman.lean`: `schwinger_continuation_base_step`
2. Theorem-2 locality frontier:
   - implementation locus:
     `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean ::
     bvt_F_swapCanonical_pairing`
   - route contract: `docs/theorem2_locality_blueprint.md`
   - primary geometry route: explicit real open edge / ET-support Route B,
     with forward-Jost Route A documented only as blocked fallback
3. Positivity / theorem-3 transport package:
   - implementation locus: `OSToWightmanPositivity.lean`
   - exported downstream wrapper: `OSToWightmanBoundaryValues.lean :: bvt_W_positive`
   - source-check contract: do not infer landed theorem-3 closure names from
     older planning prose. The checked file currently exposes the A/B bridge
     and Hilbert-density support surfaces named above, plus a quarantined note
     that the Section-4.3 transport block is still missing under separate
     theorem names
   - checked companion support file: `OSReconstruction/SCV/PartialFourierSpatial.lean`
     is present in the live tree and already exposes the concrete supplier
     chain
     `partialFourierSpatial_fun`
     -> `partialFourierSpatial_timeSliceSchwartz`
     -> `partialFourierSpatial_timeSlice_hasPaleyWienerExtension`
     -> `partialFourierSpatial_timeSliceCanonicalExtension`,
     sitting above the coordinate reshuffle `nPointTimeSpatialCLE`, together
     with checked continuity / derivative transport theorems for
     `partialFourierSpatial_fun`; the open theorem-3 work is therefore the
     Section-4.3 packaging above that checked chain, not the discovery of
     whether a partial-spatial-Fourier support file exists at all
4. Boundary-value existence and transfer:
   - `OSToWightmanBoundaryValuesBase.lean`:
     public theorem surfaces `boundary_values_tempered`,
     `bvt_F_holomorphic`, and `bvt_boundary_values`, together with the
     checked-private in-file packaging theorems
     `forwardTube_boundaryValueData_of_polyGrowth` and
     `full_analytic_continuation_boundaryValueData`
   - `ForwardTubeDistributions.lean`: the still-missing flattened-growth /
     flat-regular constructor package consumed by theorem 2
   - `OSToWightmanBoundaryValues.lean`: downstream transfer chain and the
     theorem-2/theorem-4 frontier consumers only; it should not be described
     as the file that owns `boundary_values_tempered`
4. Cluster property:
   - base reductions already in `OSToWightmanBoundaryValuesBase.lean`
   - one-factor transport inputs owned by `OSToWightmanPositivity.lean`
   - repaired positive-time bridge owned by
     `OSToWightmanBoundaryValuesBase.lean`
   - public canonical-shell adapter plus final wrapper owned by
     `OSToWightmanBoundaryValues.lean`
   - missing public adapter / corrected bridge package controlled by
     `docs/theorem4_cluster_blueprint.md`

Live status:
- the OS quotient/Hilbert semigroup infrastructure is already built in
  `OSToWightmanSemigroup.lean`
- `OSLinearGrowthCondition` is already used upstream in proved production
  lemmas to get polynomial growth of Euclidean time-shift matrix elements and
  hence contraction
- rational-time identification with positive functional-calculus powers is in
  place
- positive-time continuity of `t ↦ CFC.nnrpow A t` is now in
  `vNA/Bochner/SemigroupRoots.lean`
- `Wightman/SchwartzTensorProduct.lean` now contains explicit product-test
  insertion operators (`productTensorUpdateCLM`, `prependFieldCLMLeft/Right`)
  for the kernel-extension lane
- theorem 3 should no longer be described only as a file-level blocker inside
  `OSToWightmanBoundaryValues.lean`: the live theorem-package seam is the
  Section-4.3 transformed-image route in `OSToWightmanPositivity.lean`, while
  `bvt_W_positive` in `OSToWightmanBoundaryValues.lean` is the exported
  consumer wrapper
- theorem 3 should also no longer be described as if the Section-4.3 transport
  still lacks a checked support-file foothold: `SCV/PartialFourierSpatial.lean`
  is now a landed supplier layer, so the implementation ambiguity is not
  "where does the partial Fourier analysis live?" but rather the sharper
  Package-I transcript:
  `partialFourierSpatial_fun`
  -> `partialFourierSpatial_timeSliceSchwartz`
  -> `partialFourierSpatial_timeSlice_hasPaleyWienerExtension`
  -> `partialFourierSpatial_timeSliceCanonicalExtension`
  -> one-variable theorem slot `os1TransportOneVar`
  -> kernel-zero slot `os1TransportOneVar_eq_zero_iff`
  -> degreewise slot `os1TransportComponent`
  -> degreewise kernel-zero slot `os1TransportComponent_eq_zero_iff`
  -> transformed-image bundle `BvtTransportImageSequence`
  -> on-image transport map `bvt_transport_to_osHilbert_onImage`
  -> concrete Lemma-4.2 adapter `lemma42_matrix_element_time_interchange`
  -> on-image quadratic identity
     `bvt_wightmanInner_eq_transport_norm_sq_onImage`,
  with the well-definedness step required to consume explicit kernel-zero
  surfaces `os1TransportOneVar_eq_zero_iff` and
  `os1TransportComponent_eq_zero_iff` rather than an unnamed injectivity
  slogan, and with quotient-side dense-range results kept in the separate
  paper-faithfulness lane rather than treated as the live positivity-closing
  step
- theorem 4 should no longer be described only as the final private wrapper
  `bvt_cluster`: the checked repo already has the base reductions in
  `OSToWightmanBoundaryValuesBase.lean`, but the corrected bridge theorem
  `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
  and the public canonical-shell adapter package are still doc-level targets
  that must be introduced explicitly before the final wrapper proof is treated
  as implementation-ready. Source-check against the live tree now fixes the
  checked/planned split more sharply: `OSToWightmanBoundaryValuesBase.lean`
  really contains `...singleSplitLargeSpatial`,
  `...singleSplitSchwingerLargeSpatial`, and legacy
  `...singleSplitFactorComparison`; `OSToWightmanBoundaryValues.lean` really
  contains only the final consumer shell
  (`bv_cluster_transfer_of_canonical_eventually`, private
  `bvt_F_clusterCanonicalEventually_translate`, private
  `bvt_F_clusterCanonicalEventually`, private `bvt_W_cluster`); and the
  theorem-4 one-factor transport package in `OSToWightmanPositivity.lean`
  remains planned support work rather than checked-present named lemmas.
- theorem-4 file ownership is now fixed more sharply too:
  theorem-3-derived one-factor transport inputs
  (`cluster_left_factor_transport`, `cluster_right_factor_transport`) belong in
  `OSToWightmanPositivity.lean`; the repaired positive-time cluster bridge
  `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
  together with the thin wrapper
  `bvt_cluster_positiveTime_singleSplit_core` belong in
  `OSToWightmanBoundaryValuesBase.lean`; and the public canonical-shell adapter
  package
  `canonical_cluster_integrand_eq_singleSplit_integrand`
  -> `canonical_translate_factor_eq_singleSplit_translate_factor`
  -> `singleSplit_core_rewrites_to_canonical_shell`
  -> `canonical_shell_limit_of_rewrite`
  -> `bvt_cluster_canonical_from_positiveTime_core`
  belongs in `OSToWightmanBoundaryValues.lean` immediately above the final
  private wrapper. `OSToWightmanBoundaryValueLimits.lean` is not the theorem-4
  home under the current checked-tree contract.
- the immediate active target inside `schwinger_continuation_base_step` is the
  original 2-point Schwinger case:
  - one difference variable after translation reduction,
  - stated on `ZeroDiagonalSchwartz d 2` or an explicitly admissible Euclidean
    subspace,
  - not on ambient full Schwartz space
- theorem 2 must no longer be described as that continuation root blocker:
  the live theorem-2 theorem surface is the canonical-shift boundary pairing
  theorem `bvt_F_swapCanonical_pairing` in
  `OSToWightmanBoundaryValues.lean`, and its doc-level hard gap is now the
  explicit Route-B open-edge / ET-support geometry package plus the flattened
  regular continuity constructor described in
  `docs/theorem2_locality_blueprint.md`
- theorem 2 should also no longer be described as a vague BHW / ET problem at
  the file level: the checked production-locus split is now
  `OSToWightmanBoundaryValues.lean` for the frontier theorem,
  `OSToWightmanBoundaryValuesComparison.lean` for the downstream consumer,
  `OSToWightmanBoundaryValueLimits.lean` for the canonical-shift closure
  layer, `ForwardTubeDistributions.lean` for the flattened-regular continuity
  supplier and checked boundary-recovery theorems
  (`boundary_value_recovery_forwardTube_of_flatRegular`,
  `boundary_value_recovery_forwardTube_of_flatRegular_from_bv`),
  `BHWExtension.lean` plus the checked BHW-permutation umbrella /
  adjacent-swap support stack
  `ComplexLieGroups/Connectedness/BHWPermutation.lean` /
  `ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean` /
  `ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean`
  for the swap/locality suppliers, and `AnalyticContinuation.lean` plus
  `ComplexLieGroups/JostPoints.lean` for the analytic/geometry suppliers;
  moreover the checked adjacent-swap support stack is two-layered: the
  pointwise/open-edge adjacent route lives in `Adjacency.lean`, while the
  checked raw-boundary pairing theorem surface consumed by theorem 2 lives in
  `AdjacencyDistributional.lean`; the checked raw-boundary theorem surface is
  adjacent-only (`i`, `i+1`), while the frontier theorem still uses general
  `swap i j`, so the theorem-2 proof transcript must run through the
  flat-regular input, the adjacent-only substitute consumer theorem
  `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` (statement
  home in `BHWExtension.lean`, lower helper home in
  `AdjacencyDistributional.lean`), the packaging theorem
  `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`, the theorem-2-
  specific canonical pairing recovery specialization
  `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` at
  `canonicalForwardConeDirection`, the separate gluing theorem
  `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`, and then a
  separate adjacent-chain reduction theorem
  `bvt_F_swapCanonical_pairing_of_adjacent_chain` before the final frontier
  theorem. `OSToWightmanBoundaryValueLimits.lean` is the checked file locus for
  the canonical-shift / adjacent-chain part of that planned theorem-2 closure
  package, but the current tree still uses that file only for theorem-3 /
  `singleSplit_xiShift` limit machinery, so the theorem-2 subsection there is
  still missing support work rather than an already-present package to reuse.
  More sharply, that sibling subsection starts only after
  `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` is already available;
  it does not own the raw-boundary closure theorem itself. Those layers must
  not be hidden in one closing `sorry`. Conversely, schematic pseudocode names
  for the internal
  adjacent-step data of that reducer (for example
  `adjacentSwapFactorization` / `AdjacentCanonicalSwapPairingStepHolds`) are
  not themselves part of the theorem-slot contract unless a later doc pass
  explicitly promotes them; the contract is the existence of the separate
  reducer theorem, not those exact helper names.
- the original 1-point Schwinger case is mathematically trivial from
  translation invariance and is no longer an active development lane
- only after the 2-point Schwinger reduction is exposed cleanly should we
  choose between:
  - a concrete Schwinger-side interleaved/operator kernel theorem, or
  - a genuine Schwartz kernel-extension theorem built on the tensor
    infrastructure

### B) R -> E wick-rotation submodules (9 sorrys + 1 deferred axiom on the active path)

1. `SchwingerTemperedness.lean`:
   - zero-diagonal integrability / temperedness
2. `SchwingerAxioms.lean`:
   - source-checked reverse status split:
     - live direct `sorry`: `schwingerExtension_os_term_eq_wightman_term`
       (false OS=`Wightman` identification lane; quarantined, not a target to
       revive)
     - live direct `sorry`: `W_analytic_cluster_integral`
       (full-Schwartz reverse cluster supplier theorem, still blocked on
       `wickRotation_not_in_PET_null` + Fubini, but not itself the final
       `E4_cluster` field packaging on `ZeroDiagonalSchwartz`)
     - checked-present but quarantined wrapper:
       `wickRotatedBoundaryPairing_reflection_positive`, which currently still
       closes only by passing through the false
       `schwingerExtension_os_inner_product_eq_wightman` chain and therefore
       must not be treated as honest infrastructure for `E2_reflection_positive`
   - future stronger reverse-theorem packaging owner for the source-checked
     field-level reverse slots:
     `E0_reality`, `E3_symmetric`, split `E1_translation_invariant`, split
     `E1_rotation_invariant`, and the later reverse Section-4 transport
     wrappers for `E2_reflection_positive` / `E4_cluster`
   - doc-level contract: do not describe this future package as one bundled
     `EuclideanInvariance` theorem; the reverse blueprint now fixes the order
     `E0_tempered -> E0_linear -> E0_reality -> E3_symmetric -> E1_translation_invariant -> E1_rotation_invariant -> E2_reflection_positive -> E4_cluster`
   - closure-shape contract: future `E2_reflection_positive` must be a reverse
     Section-4.3 transport/density package targeting
     `SchwingerOS.lean :: OsterwalderSchraderAxioms.E2_reflection_positive`,
     and the docs must now freeze its exact theorem-slot order too:
     `wickRotated_positiveTimeCore -> wickRotatedBoundaryPairing_eq_transport_inner_on_core -> wickRotatedBoundaryPairing_nonneg_on_core -> wickRotated_positiveTimeCore_dense -> wickRotatedBoundaryPairing_nonneg_by_density -> constructSchwinger_positive -> OsterwalderSchraderAxioms.E2_reflection_positive`.
     This lane may not be described as a direct reuse of the quarantined
     positivity wrapper `wickRotatedBoundaryPairing_reflection_positive`, nor
     as a vague promise to reuse the forward `E -> R` positivity theorem.
     Future `E4_cluster` must be a parallel reverse Section-4.4
     transport/density package targeting
     `SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster`; neither slot
     may be documented as a vague promise to reuse
     `W_analytic_cluster_integral` unchanged. For `E4_cluster` the docs must
     freeze the explicit consumer ladder
     `W_analytic_cluster_integral -> wickRotatedBoundaryPairing_cluster -> constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster -> OsterwalderSchraderAxioms.E4_cluster`,
     with the first two surfaces already checked in
     `WickRotation/SchwingerAxioms.lean` and the last three slots marked as the
     planned zero-diagonal adapter / packaging work. The packaging stage must itself now be read
     as a three-step local transcript rather than one opaque theorem: first
     `constructSchwinger_cluster_translate_adapter` manufactures the translated
     witness `g_a : ZeroDiagonalSchwartz d m`, then
     `constructSchwinger_cluster_tensor_adapter` manufactures the tensor
     witness `fg_a : ZeroDiagonalSchwartz d (n + m)` with the literal product
     formula required by the field statement, and only then may
     `constructSchwinger_cluster` consume
     `wickRotatedBoundaryPairing_cluster` plus those witnesses to close
     `E4_cluster`
3. `BHWTranslation.lean`:
   - old-route base-fiber connectivity on PET
   - no longer needed to obtain `bhw_translation_invariant` on the merged Route 1 path
4. `BHWReducedExtension.lean`:
   - deferred reduced BHW bridge theorem
   - intended future discharge: descend the absolute BHW extension through
     translation fibers / quotient geometry
5. `ForwardTubeLorentz.lean`:
   - slice polynomial growth
   - null exceptional set for PET entry

### C) Shared SCV infrastructure (2 sorrys total, but still load-bearing)

1. `LaplaceSchwartz.lean` is now sorry-free and contains the generic tempered
   boundary-value lemmas needed for `boundary_values_tempered`.
2. `PaleyWiener.lean` is sorry-free; no live multivariable Paley-Wiener theorem is
   on the immediate critical path.
3. `BochnerTubeTheorem.lean` (2) remains open, but it is no longer the first
   blocker to attack.

The honest remaining SCV-facing gap in the E -> R lane is not generic DCT or
integrability anymore; it is deriving the growth hypotheses (`hpoly`, `hunif`)
from the OS data.

## 4. Secondary / Standalone Blockers

1. `Wightman/Reconstruction/Main.lean`: `wightman_uniqueness` (1)
2. `Wightman/Reconstruction/GNSHilbertSpace.lean`: vacuum-uniqueness chain (1)
3. `Wightman/WightmanAxioms.lean`: 4 infrastructural sorrys
4. Nuclear-space / Bochner-Minlos lane: **checked local support lane, but not
   yet integrated into downstream reconstruction consumers**
   - the checked tree here does contain a live
     `Wightman/NuclearSpaces/` subtree (`NuclearSpace.lean`,
     `SchwartzNuclear.lean`, `GaussianFieldBridge.lean`,
     `BochnerMinlos.lean`, `EuclideanMeasure.lean`, `ComplexSchwartz.lean`);
   - implementation-facing work on this lane is therefore split between the
     checked local support files above and the still-exported downstream axioms
     `schwartz_nuclear_extension` and
     `exists_continuousMultilinear_ofSeparatelyContinuous` in
     `Wightman/WightmanAxioms.lean`;
   - any future pass that changes whether a theorem package is owned by the
     local support files, by gaussian-field import/re-export, or by the
     downstream axiom surface must update this plan in the same pass.
5. `ComplexLieGroups/*`: 2 remaining BHW-permutation blockers (maintained, not current top lane)
   - exact scope caution: these are only the downstream full-permutation endgame
     blockers in
     `ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlocker.lean`
     (`blocker_isConnected_permSeedSet_nontrivial`,
     `blocker_iterated_eow_hExtPerm_d1_nontrivial`)
   - theorem 2 is **not** blocked on that file; its implementation route stops
     earlier on the adjacent-swap seam
     `Adjacency.lean -> AdjacencyDistributional.lean -> BHWExtension.lean -> OStoWightmanBoundaryValueLimits.lean`
   - any future pass that reprioritizes this lane must preserve that ownership
     boundary instead of reopening theorem-2 raw-boundary packaging under the
     permutation-flow banner

## 5. Execution Order

1. Close `schwinger_continuation_base_step` in `OSToWightman.lean`.
   - first attack the original 2-point Schwinger reduction on the honest Schwinger domain
   - avoid one-point classification detours and avoid ambient full-Schwartz theorem surfaces
2. Use the extracted SCV boundary-distribution lemmas to reduce
   `OSToWightmanBoundaryValuesBase.lean :: boundary_values_tempered` to the
   genuine OS-side growth inputs carried by
   `OSToWightman.lean :: full_analytic_continuation_with_symmetry_growth`.
3. If the continuation blocker truly requires the Schwartz-kernel assembly, use the
   fixed functional-analysis axioms in `Wightman/WightmanAxioms.lean`
   (`exists_continuousMultilinear_ofSeparatelyContinuous` and
   `schwartz_nuclear_extension`) and continue the blocker-facing density/kernel
   assembly in the reconstruction files.
4. Close the boundary-value consumer layer in this order:
   - theorem 2: keep locality work on
     `OSToWightmanBoundaryValues.lean :: bvt_F_swapCanonical_pairing`, using
     the Route-B open-edge / ET-support geometry package and the flattened
     regular continuity constructor documented in
     `docs/theorem2_locality_blueprint.md`;
   - theorem 3: keep implementation work on the Section-4.3 package in
     `OSToWightmanPositivity.lean`, with `bvt_W_positive` in
     `OSToWightmanBoundaryValues.lean` treated as the exported wrapper;
   - theorem 4: keep work split into the corrected single-split transport
     bridge plus the public canonical-shell adapter package before touching the
     final private wrapper `bvt_F_clusterCanonicalEventually_translate`;
   - only then close the remaining transfer chain and `bvt_cluster` in
     `OSToWightmanBoundaryValues.lean`.
5. In parallel or next, attack the live R -> E theorem-level front:
   - `SchwingerTemperedness.lean`: coincidence-singularity / zero-diagonal continuity
   - `SchwingerAxioms.lean`: Euclidean reality, OS=W term, and cluster
   - keep `isPreconnected_baseFiber` in `BHWTranslation.lean` as an old-route residual,
     not as the merged-path blocker
6. Finish final wiring (`wightman_uniqueness`, remaining `GNSHilbertSpace`, residual `WightmanAxioms` blockers).

## 6. Deprioritized Work (Unless It Unblocks the Above)

1. Most of `vNA/*`
2. Historical/planned nuclear-space side development beyond the currently
   checked `Wightman/WightmanAxioms.lean` axiom surfaces
3. Additional CLG refactors not required by active OS reconstruction blockers

## 7. Verification Commands

```bash
# module builds
lake build OSReconstruction.SCV
lake build OSReconstruction.Wightman

# blocker census
rg -n '^\s*sorry\b' OSReconstruction --glob '*.lean'
rg -n '^axiom\\s+' OSReconstruction --glob '*.lean'
```
