# Production Sorry Triage

Purpose: this note is the repo-wide triage sheet for every direct production
`sorry` currently present in `OSReconstruction/**/*.lean`.

Count convention:
- direct tactic holes only: `^[[:space:]]*sorry([[:space:]]|$)`
- rechecked on `2026-04-08`
- current live count: `60`

This note should be read together with:
- `docs/theorem2_locality_blueprint.md`
- `docs/theorem3_os_route_blueprint.md`
- `docs/theorem4_cluster_blueprint.md`
- `docs/r_to_e_blueprint.md`
- `docs/general_k_continuation_blueprint.md`
- `docs/gns_pipeline_blueprint.md`
- `docs/vna_triage.md`
- `docs/peripheral_sorry_triage.md`

## 1. Current census

| Subsystem | Direct `sorry`s |
|---|---:|
| `OSReconstruction/Wightman` | 20 |
| `OSReconstruction/SCV` | 2 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 36 |
| **Total** | **60** |

## 2. Highest-priority OS-route frontiers

These are the blockers closest to the current public reconstruction lane.

| ID | File:line | Theorem | Why it matters | Primary doc |
|---|---|---|---|---|
| W1 | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:351` | `bvt_F_swapCanonical_pairing` | theorem 2 locality frontier; final consumer of the adjacent-only raw-boundary package plus the later canonical-shift / adjacent-chain closure layer | `docs/theorem2_locality_blueprint.md` |
| W2 | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:381` | `bvt_W_positive` | theorem 3 exported positivity wrapper; implementation seam lives below it in `OSToWightmanPositivity.lean` | `docs/theorem3_os_route_blueprint.md` |
| W3 | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:398` | `bvt_F_clusterCanonicalEventually_translate` | theorem 4 final cluster frontier; base reductions already exist below it in `OSToWightmanBoundaryValuesBase.lean` | `docs/theorem4_cluster_blueprint.md` |

Everything else in this document should be interpreted relative to those three
live public blockers.

## 3. Wightman-side direct `sorry`s (20)

### 3.1. `E -> R` continuation and boundary-value lane

The theorem-2 ledger in this section now uses a stricter ownership split.
`W1 = bvt_F_swapCanonical_pairing` is only the frontier consumer in
`OSToWightmanBoundaryValues.lean`; it is **not** the place where later Lean
work should rediscover the whole locality proof. The checked/doc-planned route
below it is now:

1. Route-B open-edge / ET-support geometry on the checked adjacent-swap stack
   `ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean` /
   `.../AdjacencyDistributional.lean`, starting from the checked-present lower
   supplier `exists_real_open_nhds_adjSwap`;
2. the flattened regular continuity package for `bvt_F` on
   `Wightman/Reconstruction/ForwardTubeDistributions.lean`;
3. the adjacent-only raw-boundary substitute consumer theorem
   `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` on the
   `WickRotation/BHWExtension.lean` / `AdjacencyDistributional.lean` seam,
   closing via the checked pointwise theorem
   `analytic_boundary_local_commutativity_of_boundary_continuous` rather than
   by circularly calling a wrapper that assumes
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)`;
4. the packaged adjacent raw-boundary equality
   `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` on the same BHW
   extension side;
5. the canonical-shift recovery / gluing / adjacent-chain subsection in
   `WickRotation/OSToWightmanBoundaryValueLimits.lean`, in the exact order
   `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
   -> `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
   -> `bvt_F_swapCanonical_pairing_of_adjacent_chain`;
6. only then the final frontier theorem `bvt_F_swapCanonical_pairing`.

This distinction is implementation-critical: `OSToWightmanBoundaryValueLimits.lean`
owns only the canonical-shift package above the already-closed adjacent
raw-boundary theorem, while `BHWExtension.lean` / `AdjacencyDistributional.lean`
own the adjacent raw-boundary closure itself.

To stop later implementation from having to reconstruct the handoff order from
multiple docs, the theorem-2 lane is now frozen here as a slot ledger too:

| Slot | File ownership | Must consume exactly | Must prove / export exactly | Next allowed consumer |
| --- | --- | --- | --- | --- |
| `choose_real_open_edge_for_adjacent_swap` | `ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean` (or a theorem-2-facing wrapper beside that checked helper layer) | checked `exists_real_open_nhds_adjSwap` plus theorem-2 support inclusion for `tsupport f` | one theorem-2-facing open real edge `V` with adjacent-swap compatibility on `V`, `tsupport f ⊆ V`, and the swapped-edge data needed downstream | `swapped_support_lies_in_swapped_open_edge`, `swapped_open_edge_embeds_in_extendedTube` |
| `swapped_support_lies_in_swapped_open_edge` | same Route-B geometry layer | output of `choose_real_open_edge_for_adjacent_swap` plus the checked swap identity on real points | support transport only: the swapped test-function support lies in the swapped real open edge | `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` |
| `swapped_open_edge_embeds_in_extendedTube` | same Route-B geometry layer | output of `choose_real_open_edge_for_adjacent_swap` | ET transport only: both the chosen edge and its swapped image lie in the required extended-tube domain | `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`, `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` |
| `bvt_F_hasFlatRegularRepr` | `Wightman/Reconstruction/ForwardTubeDistributions.lean` | checked unflattened suppliers `bvt_F_holomorphic`, `bvt_boundary_values`, and the explicit growth field extracted from `full_analytic_continuation_with_symmetry_growth` | a theorem-2-specific flat-regular witness package for `bvt_F` | `bvt_F_boundary_continuous_at_real_support`, `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` |
| `bvt_F_boundary_continuous_at_real_support` | `Wightman/Reconstruction/ForwardTubeDistributions.lean` | `bvt_F_hasFlatRegularRepr` plus checked `boundary_function_continuous_forwardTube_of_flatRegular` | boundary continuity of `bvt_F` on the real support/edge data used by theorem 2 | `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` |
| `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` | statement home `Wightman/Reconstruction/WickRotation/BHWExtension.lean`; lower helper lemmas in `ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean` | Route-B open-edge package (`choose_real_open_edge_for_adjacent_swap`, `swapped_support_lies_in_swapped_open_edge`, `swapped_open_edge_embeds_in_extendedTube`) plus `bvt_F_boundary_continuous_at_real_support` and checked `analytic_boundary_local_commutativity_of_boundary_continuous` | the actual adjacent-only non-circular raw-boundary pairing equality for theorem 2 | `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` |
| `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` | `Wightman/Reconstruction/WickRotation/BHWExtension.lean` / theorem-2 boundary-pairing layer | `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` plus the checked ET-support wrapper format expected by the Wick-rotation boundary side | theorem-2-facing adjacent raw-boundary equality in the exported boundary-pairing format | `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` |
| `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean` | `bvt_F_hasFlatRegularRepr` plus checked `boundary_value_recovery_forwardTube_of_flatRegular_from_bv`, instantiated with checked `bvt_W`, `bvt_W_continuous`, `bvt_boundary_values`, and `canonicalForwardConeDirection` | the theorem-2-specific canonical-direction pairing recovery equality | `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` |
| `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean` | `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` plus two uses of `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` | adjacent canonical pairing equality for one adjacent transposition | `bvt_F_swapCanonical_pairing_of_adjacent_chain` |
| `bvt_F_swapCanonical_pairing_of_adjacent_chain` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean` | explicit adjacent-transposition factorization data for `swap i j` plus repeated `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` | general `swap i j` canonical pairing equality, still below the frontier file | `bvt_F_swapCanonical_pairing` |
| `bvt_F_swapCanonical_pairing` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean` | checked `bv_local_commutativity_transfer_of_swap_pairing` plus `bvt_F_swapCanonical_pairing_of_adjacent_chain` | the final theorem-2 frontier statement consumed by the transfer layer | downstream transfer / public locality consumers only |

Two negative route rules are now fixed here too:
1. no slot above `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`
   may consume global `IsLocallyCommutativeWeak d (bvt_W OS lgc)`;
2. nothing in `OSToWightmanBoundaryValueLimits.lean` may reopen the
   raw-boundary closure theorem after the `BHWExtension.lean` seam has closed
   it.

| ID | File:line | Theorem | Lane | Status |
|---|---|---|---|---|
| W4 | `Wightman/Reconstruction/WickRotation/OSToWightman.lean:66` | `exists_acrOne_productTensor_witness` | base-step support package | active |
| W5 | `Wightman/Reconstruction/WickRotation/OSToWightman.lean:209` | `acrOne_productTensor_witness_euclidKernelPackage` | base-step support package | active |
| W6 | `Wightman/Reconstruction/WickRotation/OSToWightman.lean:376` | `compactlySupported_zeroDiagonal_subset_closure_admissibleProductTensorSet` | base-step closure/density package | active |
| W1 | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:351` | `bvt_F_swapCanonical_pairing` | theorem 2 locality | active |
| W2 | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:381` | `bvt_W_positive` | theorem 3 positivity | active |
| W3 | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:398` | `bvt_F_clusterCanonicalEventually_translate` | theorem 4 cluster | active |
| W7 | `Wightman/Reconstruction/WickRotation/K2VI1/Frontier.lean:133` | `hasCompactSupport_twoPointCenterShearDescent_reflected_local` | theorem-1 / K2 residual support theorem | medium |

### 3.2. `R -> E` / reverse-direction and historical side lanes

| ID | File:line | Theorem | Lane | Status |
|---|---|---|---|---|
| W8 | `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean:2358` | `schwingerExtension_os_term_eq_wightman_term` | false positivity route | quarantine/delete |
| W9 | `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean:2412` | `wickRotatedBoundaryPairing_reflection_positive` | quarantined reverse-direction positivity wrapper | checked-present but untrusted |
| W10 | `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean:3545` | `W_analytic_cluster_integral` | reverse-direction cluster supplier | live but not on shortest path |
| W11 | `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean:3589` | `wickRotatedBoundaryPairing_cluster` | reverse-direction cluster wrapper above the live supplier | checked-present but not final field witness |
| W12 | `Wightman/Reconstruction/WickRotation/BHWTranslation.lean:1115` | `isPreconnected_baseFiber` | old-route PET connectivity | peripheral |
| W13 | `Wightman/Reconstruction/WickRotation/ForwardTubeLorentz.lean:1129` | `wickRotation_not_in_PET_null` | reverse-direction measure-zero geometry | peripheral |

Source-checked reverse-lane contract (2026-04-08): keep three statuses distinct.
1. `schwingerExtension_os_term_eq_wightman_term` is the false OS=`Wightman`
   identification lane and should not be revived as a stepping stone.
2. `SchwingerAxioms.lean:2412 :: wickRotatedBoundaryPairing_reflection_positive`
   is **checked-present but quarantined**, because it still closes only through
   `schwingerExtension_os_inner_product_eq_wightman_positivity`; therefore the
   future field `SchwingerOS.lean:774 :: OsterwalderSchraderAxioms.E2_reflection_positive`
   still has no honest checked supplier theorem.
3. `SchwingerAxioms.lean:3545 :: W_analytic_cluster_integral` is a real live theorem-shaped supplier, but it
   is only the full-Schwartz/common-BHW integral stage, and
   `SchwingerAxioms.lean:3589 :: wickRotatedBoundaryPairing_cluster` is only
   the checked wrapper above it. The future field
   `SchwingerOS.lean:792 :: OsterwalderSchraderAxioms.E4_cluster` still needs the
   fully frozen consumer ladder
   `W_analytic_cluster_integral -> wickRotatedBoundaryPairing_cluster -> constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster -> OsterwalderSchraderAxioms.E4_cluster`,
   where the first adapter must manufacture the translated witness
   `g_a : ZeroDiagonalSchwartz d m`, the second must manufacture the tensor
   witness `fg_a : ZeroDiagonalSchwartz d (n + m)`, and only then may
   `constructSchwinger_cluster` discharge the final norm inequality on
   `constructSchwingerFunctions Wfn`.
   The supplier theorem itself is now frozen to the sector-decomposition proof
   transcript: finite time-ordering sector partition of the `(n+m)`-point
   Wick-rotated integral -> identity-sector application of
   `bhw_pointwise_cluster_forwardTube` -> BHW permutation rewrites on bad
   sectors -> uniform `HasForwardTubeGrowth` majorant with Schwartz decay ->
   sectorwise dominated convergence -> finite sector sum. Later Lean work
   should not treat the current theorem as if that packaging were already done,
   and should not reopen PET-strengthening or direct-distributional routes as
   coequal implementation plans.

   The reverse `E4` lane is now frozen here as a slot ledger too, so later Lean
   implementation does not have to reconstruct the adapter handoff from the
   blueprint stack:

   | Slot | File ownership | Must consume exactly | Must prove / export exactly | Next allowed consumer |
   | --- | --- | --- | --- | --- |
   | `W_analytic_cluster_integral` | `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` | the checked common-BHW / full-`SchwartzNPoint` cluster setup, with the proof transcript fixed as sector partition -> identity-sector ForwardTube step -> bad-sector permutation rewrites -> uniform majorant -> sectorwise DCT -> finite sector sum | the reverse Section-4.4 supplier estimate on the common-BHW/full-`SchwartzNPoint` side | `wickRotatedBoundaryPairing_cluster` only |
   | `wickRotatedBoundaryPairing_cluster` | `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` | `W_analytic_cluster_integral` only | the checked Wick-rotated full-`SchwartzNPoint` cluster wrapper, still not a zero-diagonal axiom-field witness | `constructSchwinger_cluster_translate_adapter`, `constructSchwinger_cluster_tensor_adapter`, `constructSchwinger_cluster` |
   | `constructSchwinger_cluster_translate_adapter` | reverse packaging layer targeting `Wightman/Reconstruction/SchwingerOS.lean` | `g : ZeroDiagonalSchwartz d m` plus a spatial translation vector `a` | the exact quantified witness `g_a : ZeroDiagonalSchwartz d m` with pointwise equation `g_a.1 x = g.1 (fun i => x i - a)` required by `E4_cluster` | `constructSchwinger_cluster_tensor_adapter`, `constructSchwinger_cluster` |
   | `constructSchwinger_cluster_tensor_adapter` | same reverse packaging layer above `SchwingerAxioms.lean` | `f : ZeroDiagonalSchwartz d n` plus the translated witness `g_a` | the exact `(n+m)`-point witness `fg_a : ZeroDiagonalSchwartz d (n + m)` with pointwise equation `fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)` | `constructSchwinger_cluster` |
   | `constructSchwinger_cluster` | same reverse packaging layer, with final consumer target `SchwingerOS.lean:792` | `wickRotatedBoundaryPairing_cluster` plus the manufactured witnesses `g_a` and `fg_a`; no vague tensor-restriction shortcut is allowed here | the literal norm inequality demanded by `OsterwalderSchraderAxioms.E4_cluster` | final reverse field packaging only |

### 3.3. GNS / uniqueness / functional-analysis side lane

| ID | File:line | Theorem | Lane | Status |
|---|---|---|---|---|
| W12 | `Wightman/Reconstruction/GNSHilbertSpace.lean:1258` | `gns_matrix_coefficient_holomorphic_axiom` | GNS spectrum condition bridge | high, but not on current `E -> R` path |
| W13 | `Wightman/Reconstruction/Main.lean:82` | `wightman_uniqueness` | standalone uniqueness theorem | medium |

Checked-tree clarification (2026-04-08): the current repo tree under
`OSReconstruction/Wightman/` **does** contain a live
`Wightman/NuclearSpaces/` subtree. A direct checked-tree scan shows at least
`NuclearSpace.lean`, `SchwartzNuclear.lean`, `GaussianFieldBridge.lean`,
`BochnerMinlos.lean`, `EuclideanMeasure.lean`, and `ComplexSchwartz.lean`, and
an exact direct-hole scan of that subtree gives **7** local `sorry`s:
- `NuclearSpace.lean`: 2
- `BochnerMinlos.lean`: 5

The reason those files do not appear in the live `63`-sorry census is narrower:
this triage note is presently tracking only the active OS-reconstruction / SCV /
CLG / vNA headline buckets used by the current critical-path plan. The
NuclearSpaces lane is therefore a **checked secondary lane** with real file
ownership, but it is intentionally excluded from the headline count so the
public theorem-2/3/4 execution ledger does not silently change shape.
Whenever this policy is mentioned elsewhere, the docs should state both facts
explicitly:
1. the repo really has a checked `Wightman/NuclearSpaces/*` subtree with 7 live
   local `sorry`s,
2. the headline `60` count deliberately excludes that secondary lane, and
3. downstream docs must still distinguish checked local support files,
   downstream exported axioms in `Wightman/WightmanAxioms.lean`, and the
   still-open integration route between those layers.

## 4. SCV direct `sorry`s (2)

| ID | File:line | Theorem | Role | Primary doc |
|---|---|---|---|---|
| S1 | `SCV/BochnerTubeTheorem.lean:126` | `bochner_local_extension` | local convex patch extension | `docs/scv_infrastructure_blueprint.md` |
| S2 | `SCV/BochnerTubeTheorem.lean:220` | `bochner_tube_extension` | global Bochner tube theorem | `docs/scv_infrastructure_blueprint.md` |

These are not the first blockers on the current theorem-2/3/4 route, but they
remain core SCV infrastructure for later general-`k` continuation.

## 5. Complex-Lie-group direct `sorry`s (2)

| ID | File:line | Theorem | Role | Primary doc |
|---|---|---|---|---|
| C1 | `ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlocker.lean:55` | `blocker_isConnected_permSeedSet_nontrivial` | higher-dimensional permutation-flow connectedness | `docs/bhw_permutation_blueprint.md` |
| C2 | `ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlocker.lean:119` | `blocker_iterated_eow_hExtPerm_d1_nontrivial` | one-dimensional nontrivial branch | `docs/bhw_permutation_blueprint.md` |

These are honest mathematical blockers, but they are currently peripheral to
the theorem-2/3/4 OS-route work.

## 6. vNA direct `sorry`s (36)

The operator-algebra backlog is large enough that it now has its own dedicated
triage note: `docs/vna_triage.md`. The complete line-by-line census is still
listed here for global completeness.

### 6.1. Measure-theory base

| ID | File:line | Theorem | Status |
|---|---|---|---|
| V1 | `vNA/MeasureTheory/CaratheodoryExtension.lean:150` | `toOuterMeasure_Icc` | foundational |
| V2 | `vNA/MeasureTheory/CaratheodoryExtension.lean:162` | `borel_le_caratheodory` | foundational |
| V3 | `vNA/MeasureTheory/CaratheodoryExtension.lean:308` | `toIntervalPremeasure` | foundational |
| V4 | `vNA/MeasureTheory/CaratheodoryExtension.lean:312` | `toIntervalPremeasure` | foundational |
| V5 | `vNA/MeasureTheory/CaratheodoryExtension.lean:319` | `toIntervalPremeasure` | foundational |
| V6 | `vNA/MeasureTheory/CaratheodoryExtension.lean:373` | `toSpectralMeasure_Icc` | foundational |
| V7 | `vNA/MeasureTheory/CaratheodoryExtension.lean:380` | `toSpectralMeasure_sigma_additive` | foundational |
| V8 | `vNA/MeasureTheory/CaratheodoryExtension.lean:385` | `toSpectralMeasure_univ` | foundational |
| V9 | `vNA/MeasureTheory/CaratheodoryExtension.lean:407` | `spectralPremeasureFromLimit` | foundational |
| V10 | `vNA/MeasureTheory/CaratheodoryExtension.lean:410` | `spectralPremeasureFromLimit` | foundational |
| V11 | `vNA/MeasureTheory/CaratheodoryExtension.lean:415` | `spectralPremeasureFromLimit` | foundational |

### 6.2. Core modular theory

| ID | File:line | Theorem | Status |
|---|---|---|---|
| V12 | `vNA/ModularTheory.lean:232` | `conjugates_modular_operator` | downstream of Tomita package |
| V13 | `vNA/ModularTheory.lean:247` | `reverses_modular_flow` | downstream of Tomita package |
| V14 | `vNA/ModularTheory.lean:282` | `tomita_fundamental` | core theorem |
| V15 | `vNA/ModularTheory.lean:303` | `modular_automorphism_preserves` | downstream |
| V16 | `vNA/ModularTheory.lean:341` | `StandardForm.positiveCone_self_dual` | late-stage standard form |
| V17 | `vNA/ModularTheory.lean:361` | `standard_form_unique` | late-stage standard form |

### 6.3. Modular automorphism group

| ID | File:line | Theorem | Status |
|---|---|---|---|
| V18 | `vNA/ModularAutomorphism.lean:93` | `preserves_algebra` | downstream |
| V19 | `vNA/ModularAutomorphism.lean:369` | `cocycle_in_algebra` | downstream |
| V20 | `vNA/ModularAutomorphism.lean:380` | `cocycle_identity` | downstream |
| V21 | `vNA/ModularAutomorphism.lean:436` | `modular_relation` | downstream |
| V22 | `vNA/ModularAutomorphism.lean:464` | `modular_inner_iff` | downstream |
| V23 | `vNA/ModularAutomorphism.lean:476` | `approximately_inner` | downstream |

### 6.4. KMS package

| ID | File:line | Theorem | Status |
|---|---|---|---|
| V24 | `vNA/KMS.lean:99` | `modular_state_is_kms` | downstream |
| V25 | `vNA/KMS.lean:102` | `modular_state_is_kms` | downstream |
| V26 | `vNA/KMS.lean:109` | `modular_state_is_kms` | downstream |
| V27 | `vNA/KMS.lean:127` | `kms_characterizes_modular` | downstream |
| V28 | `vNA/KMS.lean:137` | `kms_is_equilibrium` | downstream |
| V29 | `vNA/KMS.lean:149` | `kms_unique_for_factors` | downstream |
| V30 | `vNA/KMS.lean:165` | `high_temperature_limit` | downstream |
| V31 | `vNA/KMS.lean:175` | `zero_temperature_limit` | downstream |
| V32 | `vNA/KMS.lean:211` | `kms_implies_passive` | downstream |
| V33 | `vNA/KMS.lean:254` | `passive_stable_implies_kms` | downstream |

### 6.5. Predual and Stone-theorem surface

| ID | File:line | Theorem | Status |
|---|---|---|---|
| V34 | `vNA/Predual.lean:231` | `sigmaWeak_convergence_iff` | operator-topology package |
| V35 | `vNA/Predual.lean:246` | `kaplansky_density` | operator-topology package |
| V36 | `vNA/Unbounded/StoneTheorem.lean:1781` | `timeEvolution_generator` | unbounded spectral/Stone package |

## 7. Tracked axioms not counted in the `60`

The repo also contains important production axioms that do not show up in the
direct `sorry` census.

| Axiom | File | Role | Primary doc |
|---|---|---|---|
| `schwartz_nuclear_extension` | `Wightman/WightmanAxioms.lean` | kernel theorem | `docs/nuclear_spaces_blueprint.md` |
| `exists_continuousMultilinear_ofSeparatelyContinuous` | `Wightman/WightmanAxioms.lean` | separate-to-joint continuity | `docs/nuclear_spaces_blueprint.md` |
| `reduced_bargmann_hall_wightman_of_input` | `Wightman/Reconstruction/WickRotation/BHWReducedExtension.lean` | reduced Route 1 BHW bridge | `docs/general_k_continuation_blueprint.md` |
| `tube_boundaryValueData_of_polyGrowth` | `SCV/TubeBoundaryValues.lean` | tube BV from growth | `docs/scv_infrastructure_blueprint.md` |
| `vladimirov_tillmann` | `SCV/VladimirovTillmann.lean` | tube growth / Fourier-Laplace package | `docs/scv_infrastructure_blueprint.md` |
| `distributional_cluster_lifts_to_tube` | `SCV/VladimirovTillmann.lean` | reverse-direction cluster lift | `docs/scv_infrastructure_blueprint.md` |

## 8. Immediate execution order implied by this triage

If the user wants the shortest mathematically faithful route on current `main`,
the next documentation-guided Lean execution order should be:

1. theorem 3 public reduction in `docs/theorem3_os_route_blueprint.md`,
2. theorem 4 one-factor extraction / cluster closure in
   `docs/theorem4_cluster_blueprint.md`,
3. theorem 2 locality continuity / adapter package in
   `docs/theorem2_locality_blueprint.md`,
4. only then the broader general-`k`, reverse-direction, GNS, nuclear, and
   vNA backlogs.

This file should be updated whenever the direct `sorry` count changes.

## 9. High-priority Wightman blockers with concrete next packages

The repo-wide table above is useful for census purposes. The five frontiers
below are the ones that currently deserve the most detailed implementation
attention.

### 9.1. `bvt_W_positive`

File:
- `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:381`

Source-checked theorem-3 ownership split against the live tree:

1. `OSToWightmanPositivity.lean` is the implementation locus, but only part of
   that route is checked-present today;
2. `OSToWightmanBoundaryValueLimits.lean` is theorem-3 support only: it owns
   the checked `singleSplit_xiShift` holomorphic / positive-real / `t -> 0+`
   limit package, not the Section-4.3 transport image itself;
3. `OSToWightmanBoundaryValues.lean` owns only the frontier consumer
   `bvt_W_positive` plus downstream wrappers.

The theorem-3 execution ledger should now be read literally:

| Slot | Ownership | Consumes | Exports | Next consumer |
|------|-----------|----------|---------|---------------|
| `identity_theorem_right_halfplane` | `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | none | right-half-plane identity theorem for scalar holomorphic functions | `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` |
| `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` | `OSToWightmanPositivity.lean` | checked holomorphicity of `bvt_singleSplit_xiShiftHolomorphicValue` and `OSInnerProductTimeShiftHolomorphicValue`, plus `identity_theorem_right_halfplane` | equality of the theorem-3 scalar holomorphic traces on `{Re z > 0}` for compact positive-time single/single data | the `singleSplit_xiShift` positive-real / `t -> 0+` support package in `OSToWightmanBoundaryValueLimits.lean` |
| theorem-3 `singleSplit_xiShift` support layer | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean` | chosen scalar holomorphic trace, positive-real identification theorems, and `t -> 0+` limit-transfer theorems for compact positive-time single/single data | the one-variable boundary/limit facts the Section-4.3 transport package is allowed to consume | `os1TransportComponent` and the later transformed-image package only |
| checked partial-spatial-Fourier foothold | `SCV/PartialFourierSpatial.lean` | none beyond the checked SCV/Schwartz infrastructure already imported there | concrete Section-4.3 support surfaces `nPointTimeSpatialCLE`, `partialFourierSpatial_fun`, `partialFourierSpatial_timeSliceSchwartz`, `partialFourierSpatial_timeSlice_hasPaleyWienerExtension`, and `partialFourierSpatial_timeSliceCanonicalExtension` on the half-space test-function side; later theorem-3 work must consume these in that order rather than inventing a new transport companion file | `os1TransportOneVar` only |
| `positiveTimeBorchersVector_dense` | `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | positive-time Hilbert-space completion infrastructure already in that file | dense positive-time single vectors in `OSHilbertSpace OS` | the final density closure theorem |
| `euclideanPositiveTimeSingleVector` | `OSToWightmanPositivity.lean` | the same positive-time Hilbert-space support layer | canonical OS Hilbert-space vector attached to one positive-time component, together with its checked norm identity | `bvt_transport_to_osHilbert_onImage`, `bvt_wightmanInner_eq_transport_norm_sq_onImage` |
| `os1TransportOneVar` | `OSToWightmanPositivity.lean` | theorem-3 `singleSplit_xiShift` support layer plus the checked `SCV/PartialFourierSpatial.lean` supplier chain `partialFourierSpatial_fun -> partialFourierSpatial_timeSliceSchwartz -> partialFourierSpatial_timeSlice_hasPaleyWienerExtension -> partialFourierSpatial_timeSliceCanonicalExtension` | one-variable Section-4.3 transport map on the positive-time half-space test-function codomain | `os1TransportOneVar_eq_zero_iff`, `os1TransportComponent` |
| `os1TransportOneVar_eq_zero_iff` | `OSToWightmanPositivity.lean` | `os1TransportOneVar` | explicit one-variable kernel-zero theorem for the branch-`3b` transport stage | `os1TransportComponent`, `bvt_transport_to_osHilbert_onImage_wellDefined` |
| `os1TransportComponent` | `OSToWightmanPositivity.lean` | `os1TransportOneVar`, `os1TransportOneVar_eq_zero_iff`, and the explicit Section-4.3 Fourier-Laplace transport formula | degreewise transformed-image transport map on the genuine half-space codomain | `os1TransportComponent_eq_zero_iff`, `BvtTransportImageSequence` |
| `os1TransportComponent_eq_zero_iff` | `OSToWightmanPositivity.lean` | `os1TransportComponent` | explicit degreewise kernel-zero theorem for the transformed-image stage | `bvt_transport_to_osHilbert_onImage_wellDefined`, `BvtTransportImageSequence` |
| `BvtTransportImageSequence` | `OSToWightmanPositivity.lean` | `os1TransportComponent` | bundled transformed-image core on which the quadratic identity is actually proved | `bvt_transport_to_osHilbert_onImage`, `bvt_wightmanInner_eq_transport_norm_sq_onImage` |
| `bvt_transport_to_osHilbert_onImage` | `OSToWightmanPositivity.lean` | `BvtTransportImageSequence`, preimage choice, `os1TransportComponent_eq_zero_iff`, and the Section-4.3 OS-Hilbert transport definitions | OS Hilbert-space vector attached to transformed-image data | `bvt_wightmanInner_eq_transport_norm_sq_onImage` |
| `bvt_wightmanInner_eq_transport_norm_sq_onImage` | `OSToWightmanPositivity.lean` | `BvtTransportImageSequence`, `bvt_transport_to_osHilbert_onImage`, and the repaired OS II `bvt_F` / `bvt_W` kernel route | the transformed-image quadratic identity `(W(F,F)).re = ‖u(F)‖^2` on the image core only | `bvt_W_positive_of_transportImage_density` |
| `bvt_W_positive_of_transportImage_density` | `OSToWightmanPositivity.lean` | `bvt_wightmanInner_eq_transport_norm_sq_onImage`, `positiveTimeBorchersVector_dense`, and the continuity/density closure step in the Hilbert codomain | theorem-3 positivity for arbitrary `BorchersSequence d` as an implementation-side theorem | `bvt_W_positive` |
| `bvt_W_positive` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean` | the implementation-side positivity theorem from `OSToWightmanPositivity.lean` | the private frontier theorem consumed by downstream wrappers | downstream transfer / public reconstruction consumers only |

Exact checked-present vs planned split after the live source check:

1. checked-present in `OSToWightmanPositivity.lean` today:
   `identity_theorem_right_halfplane`,
   `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`,
   `positiveTimeBorchersVector_dense`,
   `euclideanPositiveTimeSingleVector`, and related norm identities;
2. checked-present in `OSToWightmanBoundaryValueLimits.lean` today: the theorem-3
   `singleSplit_xiShift` scalar holomorphic / positive-real / limit package;
3. still planned theorem-slot names, not landed file surfaces yet:
   `os1TransportComponent`, `BvtTransportImageSequence`,
   `bvt_transport_to_osHilbert_onImage`,
   `bvt_wightmanInner_eq_transport_norm_sq_onImage`,
   `bvt_W_positive_of_transportImage_density`.

Important theorem-3 route rules:

1. do **not** rehabilitate `hschw` or any same-test-function contour slogan;
2. do **not** revive the false raw Schwartz-density slogan
   "ordered-positive-time support is dense in full `SchwartzNPoint d n`";
3. prove the quadratic identity first on the transformed-image core, then close
   by Hilbert-space density/continuity;
4. do **not** grow the Section-4.3 transport package inside
   `OSToWightmanBoundaryValues.lean` or `OSToWightmanBoundaryValueLimits.lean`.

Estimated remaining Lean size:
- `260-620` lines, now concentrated in the still-missing Section-4.3
  transformed-image / quadratic-identity / density-closure package in
  `OSToWightmanPositivity.lean`.

### 9.2. `bvt_F_clusterCanonicalEventually_translate`

File:
- `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:398`

Checked-present theorem-4 file/consumer split rechecked against the current
repo tree:

1. `OSToWightmanPositivity.lean` is the theorem-3 supplier file theorem 4 must
   consume; the still-missing one-factor transport inputs belong there.
2. `OSToWightmanBoundaryValuesBase.lean` already contains the cluster-side base
   reductions
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitLargeSpatial`,
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitSchwingerLargeSpatial`,
   and the legacy theorem
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`.
   The repaired positive-time bridge belongs in this base file too.
3. `OSToWightmanBoundaryValues.lean` owns only the public canonical-shell
   adapter package and the final frontier theorem
   `bvt_F_clusterCanonicalEventually_translate`.
4. `OSToWightmanBoundaryValueLimits.lean` is **not** a theorem-4 ownership
   file on the current route; it remains theorem-2/theorem-3 support only.

Concrete next packages, now frozen in exact theorem-slot order:

1. `normalizedZeroDegreeRightVector`
2. `normalizedZeroDegreeRightVector_bound`
3. `normalizedZeroDegreeRightVector_funcs_zero`
4. `normalizedZeroDegreeRightVector_funcs_pos`
5. `zeroDegree_right_single_wightman_extracts_factor`
6. `zeroDegree_right_single_os_extracts_factor`
7. `zero_degree_component_comparison_for_normalized_right_vector`
8. `cluster_left_factor_transport`
9. `cluster_right_factor_transport`
10. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
11. `bvt_cluster_positiveTime_singleSplit_core`
12. `canonical_cluster_integrand_eq_singleSplit_integrand`
13. `canonical_translate_factor_eq_singleSplit_translate_factor`
14. `singleSplit_core_rewrites_to_canonical_shell`
15. `canonical_shell_limit_of_rewrite`
16. `bvt_cluster_canonical_from_positiveTime_core`
17. `bvt_F_clusterCanonicalEventually_translate`

To stop later Lean work from reconstructing the theorem-4 handoff from the
blueprint by memory, the live theorem-4 lane is now frozen here as a slot
ledger too:

| Slot | File ownership | Must consume exactly | Must prove / export exactly | Next allowed consumer |
| --- | --- | --- | --- | --- |
| `normalizedZeroDegreeRightVector` | `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | the degree-`0` unit shell only | the literal positive-time Borchers vector concentrated in degree `0` with value `1` | its three structural lemmas, the two right-single extraction lemmas |
| `normalizedZeroDegreeRightVector_bound` / `..._funcs_zero` / `..._funcs_pos` | same theorem-3/theorem-4 bookkeeping layer in `OSToWightmanPositivity.lean` | `normalizedZeroDegreeRightVector` | the exact structural facts `bound = 0`, degree-`0` shell is the unit, and all positive-degree shells vanish | `zeroDegree_right_single_wightman_extracts_factor`, `zeroDegree_right_single_os_extracts_factor`, `zero_degree_component_comparison_for_normalized_right_vector` |
| `zeroDegree_right_single_wightman_extracts_factor` | `OSToWightmanPositivity.lean` | checked `WightmanInnerProduct_right_single` plus the normalized degree-`0` structural lemmas | extraction of the left Wightman factor against the normalized zero-degree right vector | `cluster_left_factor_transport` |
| `zeroDegree_right_single_os_extracts_factor` | `OSToWightmanPositivity.lean` | checked `OSInnerProduct_right_single` plus the same structural lemmas | extraction of the left OS factor against the normalized zero-degree right vector | `cluster_left_factor_transport` |
| `zero_degree_component_comparison_for_normalized_right_vector` | `OSToWightmanPositivity.lean` | corrected theorem-3 Section-4.3 transport package plus the normalized degree-`0` vanishing facts | the unique surviving `m = 0` transport comparison needed for theorem-4 factor extraction | `cluster_left_factor_transport`, `cluster_right_factor_transport` |
| `cluster_left_factor_transport` | `OSToWightmanPositivity.lean` | `zeroDegree_right_single_wightman_extracts_factor`, `zeroDegree_right_single_os_extracts_factor`, `zero_degree_component_comparison_for_normalized_right_vector` | corrected theorem-3-to-theorem-4 left one-factor transport equality | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` |
| `cluster_right_factor_transport` | `OSToWightmanPositivity.lean` | the left-factor package with the nontrivial shell moved to the right | corrected theorem-3-to-theorem-4 right one-factor transport equality | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` |
| `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean` | checked base reductions through `...singleSplitSchwingerLargeSpatial` plus `cluster_left_factor_transport` and `cluster_right_factor_transport` | the repaired positive-time single-split bridge with the same conclusion shape as the legacy `...singleSplitFactorComparison` theorem but without false same-shell hypotheses | `bvt_cluster_positiveTime_singleSplit_core` |
| `bvt_cluster_positiveTime_singleSplit_core` | `OSToWightmanBoundaryValuesBase.lean` | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` | the theorem-4 cluster statement on the ordered-positive-time / compact-support single-split shell | `singleSplit_core_rewrites_to_canonical_shell` |
| `canonical_cluster_integrand_eq_singleSplit_integrand` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean` | checked canonical-direction / `xiShift` comparison surfaces already present around the boundary-value shell | the integrand-level rewrite from the public canonical shell to the positive-time single-split shell | `singleSplit_core_rewrites_to_canonical_shell` |
| `canonical_translate_factor_eq_singleSplit_translate_factor` | `OSToWightmanBoundaryValues.lean` | checked translation-factor identities on the theorem-4 shell | the right-factor rewrite matching the positive-time single-split core input | `singleSplit_core_rewrites_to_canonical_shell` |
| `singleSplit_core_rewrites_to_canonical_shell` | `OSToWightmanBoundaryValues.lean` | `bvt_cluster_positiveTime_singleSplit_core`, `canonical_cluster_integrand_eq_singleSplit_integrand`, `canonical_translate_factor_eq_singleSplit_translate_factor` | rewrite/transport of the positive-time core theorem into the public canonical shell statement | `canonical_shell_limit_of_rewrite` |
| `canonical_shell_limit_of_rewrite` | `OSToWightmanBoundaryValues.lean` | `singleSplit_core_rewrites_to_canonical_shell` | transport from the rewritten canonical shell statement to the public eventual/limit form | `bvt_cluster_canonical_from_positiveTime_core` |
| `bvt_cluster_canonical_from_positiveTime_core` | `OSToWightmanBoundaryValues.lean` | `canonical_shell_limit_of_rewrite` | the explicit public canonical-shell adapter theorem above the positive-time core | `bvt_F_clusterCanonicalEventually_translate` |
| `bvt_F_clusterCanonicalEventually_translate` | `OSToWightmanBoundaryValues.lean` | `bvt_cluster_canonical_from_positiveTime_core` only | the final theorem-4 frontier statement consumed downstream by `bvt_F_clusterCanonicalEventually`, `bv_cluster_transfer_of_canonical_eventually`, and `bvt_W_cluster` | downstream transfer / public cluster consumers only |

What this resolves at route level:

1. theorem 4 is now fixed as a strict consumer lane above theorem 3 rather than
   a place to reopen continuation or positivity;
2. the repaired positive-time bridge belongs in
   `OSToWightmanBoundaryValuesBase.lean`, while the public canonical-shell
   adapter belongs in `OSToWightmanBoundaryValues.lean`;
3. `OSToWightmanBoundaryValueLimits.lean` is explicitly excluded from theorem-4
   ownership on the current checked tree;
4. the legacy theorem
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`
   is now documented only as checked legacy infrastructure, not as the
   endorsed theorem-4 bridge surface.

What should not happen:

1. do not reopen theorem 3 analytically inside theorem 4,
2. do not invent a new same-shell comparison theorem,
3. do not hide the canonical-shell adapter inside the final frontier `sorry`,
4. do not drift any part of the theorem-4 bridge into
   `OSToWightmanBoundaryValueLimits.lean` without first rewriting the blueprint
   and the global plan docs.

Estimated remaining Lean size:
- `210-445` lines for the theorem-4 package itself, plus `35-85` lines for the
  explicit degree-zero normalization subpackage.

### 9.3. `bvt_F_swapCanonical_pairing`

File:
- `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:351`

Checked-present supplier surfaces that the docs now freeze as the theorem-2
source objects:

1. `ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean ::
   exists_real_open_nhds_adjSwap`
2. `Wightman/Reconstruction/WickRotation/BHWExtension.lean ::
   analytic_boundary_local_commutativity_of_boundary_continuous`
3. `Wightman/Reconstruction/ForwardTubeDistributions.lean ::
   boundary_function_continuous_forwardTube_of_flatRegular`
4. `Wightman/Reconstruction/ForwardTubeDistributions.lean ::
   boundary_value_recovery_forwardTube_of_flatRegular_from_bv`

Concrete next packages, in the exact theorem-slot order later Lean work should
consume them:

1. `choose_real_open_edge_for_adjacent_swap`
2. `swapped_support_lies_in_swapped_open_edge`
3. `swapped_open_edge_embeds_in_extendedTube`
4. `bvt_F_hasFlatRegularRepr`
5. `bvt_F_boundary_continuous_at_real_support`
6. `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`
7. `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`
8. `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
9. `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
10. `bvt_F_swapCanonical_pairing_of_adjacent_chain`
11. `bvt_F_swapCanonical_pairing`

Route/ownership clarification now enforced by this triage note:

1. the adjacent raw-boundary closure belongs on the
   `BHWExtension.lean` / `AdjacencyDistributional.lean` seam;
2. `OSToWightmanBoundaryValueLimits.lean` begins only after that closure and
   owns canonical-shift recovery, gluing, and adjacent-chain reduction;
3. the frontier theorem in `OSToWightmanBoundaryValues.lean` should remain a
   thin final consumer of those named packages.

What should not happen:

1. do not reopen edge-of-the-wedge,
2. do not overclaim forward-Jost support from a too-weak hypothesis,
3. do not close theorem 2 by directly calling
   `W_analytic_swap_boundary_pairing_eq` or
   `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity` on
   `W := bvt_W OS lgc`, because both checked theorem surfaces still ask for the
   circular global input `IsLocallyCommutativeWeak d W`,
4. do not hide the general `swap i j` -> adjacent-chain reduction inside the
   final frontier `sorry`.

Estimated remaining Lean size:
- `160-355` lines, but now with the theorem-slot order and file ownership made
  explicit enough that the remaining work should be executable as a staged
  package rather than rediscovered ad hoc.

### 9.4. `gns_matrix_coefficient_holomorphic_axiom`

File:
- `Wightman/Reconstruction/GNSHilbertSpace.lean:1258`

Concrete next packages:

1. matrix coefficient as smeared Wightman distribution,
2. one-variable forward support theorem,
3. partial boundary-value theorem,
4. holomorphic extension and uniqueness.

Primary doc:
- `docs/gns_pipeline_blueprint.md`

Estimated remaining Lean size:
- `140-260` lines once the SCV one-variable bridge is in place.

### 9.5. `wightman_uniqueness`

File:
- `Wightman/Reconstruction/Main.lean:82`

Concrete next packages:

1. cyclic-word dense map,
2. inner-product preservation,
3. unitary extension,
4. field intertwining.

Primary doc:
- `docs/wightman_uniqueness_blueprint.md`

Estimated remaining Lean size:
- `120-240` lines, but only after cyclicity is honest.

## 10. Blockers that are mathematically real but not current execution targets

The following direct `sorry`s should remain documented but not distract the
current theorem-2/3/4 execution order:

1. `schwingerExtension_os_term_eq_wightman_term` (false OS=`Wightman` lane;
   keep quarantined)
2. `W_analytic_cluster_integral` (live reverse cluster supplier, but still not
   the final `E4_cluster` field packaging)
3. `isPreconnected_baseFiber`
4. `wickRotation_not_in_PET_null` (currently consumed by the reverse cluster
   supplier, not by an honest reverse positivity theorem)
5. the checked nuclear / Bochner-Minlos secondary lane recorded in
   `docs/nuclear_spaces_blueprint.md`, `docs/gns-pipeline-sorries.md`, and
   `docs/peripheral_sorry_triage.md`, owned by the local
   `Wightman/NuclearSpaces/*` support files and currently carrying 7 direct
   `sorry`s outside the headline `60`-count policy
6. all of the `vNA` backlog

This note exists partly to keep that discipline explicit.

## 11. What counts as a triage doc being implementation-ready

This triage note should be considered adequate only when:

1. the live direct-sorry census is current,
2. the active theorem-2/3/4 frontiers are identified first,
3. every direct `sorry` is at least classified by lane and status,
4. the most urgent Wightman blockers have concrete next packages and rough
   line-count estimates,
5. the side backlogs are visible but not conflated with the active OS route.

The note now satisfies all five conditions.

## 12. Global dependency graph for the active proof lanes

The repo now has enough local blueprint coverage that the active dependency
graph should be stated explicitly in one place.

### 12.1. Public `E -> R` frontiers

1. `W1 = theorem 2 locality`
   in `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
   depends on:
   - `docs/theorem2_locality_blueprint.md`
   - `docs/scv_infrastructure_blueprint.md`
   - current BHW / ET geometry files
2. `W2 = theorem 3 positivity`
   depends on:
   - `docs/theorem3_os_route_blueprint.md`
   - `docs/os1_detailed_proof_audit.md`
   - current K2 / compact-approximation production chain
3. `W3 = theorem 4 cluster`
   depends on:
   - theorem 3 one-factor package first,
   - `docs/theorem4_cluster_blueprint.md`,
   - OS I Section 4.4 transport ideas from
     `docs/os1_detailed_proof_audit.md`

So the public execution order remains:

1. theorem 3,
2. theorem 4,
3. theorem 2 separately,

with theorem 4 downstream of theorem 3 and theorem 2 largely independent of
that positivity/cluster lane.

### 12.2. Generalization and side lanes

1. `general k > 2`
   depends on:
   - `docs/general_k_continuation_blueprint.md`
   - `docs/os2_detailed_proof_audit.md`
   - `docs/scv_infrastructure_blueprint.md`
2. `R -> E`
   depends on:
   - `docs/r_to_e_blueprint.md`
   - `docs/os1_detailed_proof_audit.md`
   - reverse-direction Schwinger/BHW production files, with the split `E1`
     seam frozen explicitly as
     `SchwingerAxioms.lean :: F_ext_translation_invariant -> wickRotatedBoundaryPairing_translation_invariant`
     and
     `SchwingerAxioms.lean :: F_ext_rotation_invariant -> wickRotatedBoundaryPairing_rotation_invariant`,
     before any later full `OsterwalderSchraderAxioms` wrapper
3. `GNS spectrum/cyclicity`
   depends on:
   - `docs/gns_pipeline_blueprint.md`
   - `docs/nuclear_spaces_blueprint.md`
   - `docs/scv_infrastructure_blueprint.md`
4. `vNA / unbounded spectral`
   depends on:
   - `docs/vna_infrastructure_blueprint.md`
   - `docs/vna_triage.md`

### 12.3. Route rule implied by the graph

The graph above should guide later implementation order:

1. do not pause the public `E -> R` theorem-3/theorem-4 lane for GNS or vNA;
2. do not start the full general-`k` OS II port before the SCV infrastructure
   it names has an honest implementation route;
3. do not let reverse-direction cleanup drag the active theorem-2/3/4 route off
   paper.

### 12.4. Complete-project phased execution plan

If later Lean work resumes against the whole remaining project rather than just
the public OS-route frontier, the docs should enforce the following phases.

#### Phase 1. Public `E -> R` completion

1. `W2` theorem 3 positivity,
2. `W3` theorem 4 cluster,
3. `W1` theorem 2 locality.

#### Phase 2. Immediate `E -> R` support cleanup

1. `W4-W6` in `OSToWightman.lean`,
2. `W7` in `K2VI1/Frontier.lean`.

#### Phase 3. Generalization / SCV support

1. `S1-S2` Bochner tube extension,
2. general `k > 2` OS II package from
   `docs/general_k_continuation_blueprint.md`.

#### Phase 4. Reverse-direction strengthening

1. honest `R -> E` transport packages from
   `docs/r_to_e_blueprint.md`, including the checked split-`E1` seam
   `F_ext_translation_invariant -> wickRotatedBoundaryPairing_translation_invariant`
   and `F_ext_rotation_invariant -> wickRotatedBoundaryPairing_rotation_invariant`
   in `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` before any
   later full `OsterwalderSchraderAxioms` wrapper,
2. quarantine/remove the false reverse-direction positivity chain.

#### Phase 5. GNS / kernel / uniqueness side lane

1. nuclear-space and kernel-theorem packages,
2. GNS matrix-coefficient bridge,
3. cyclicity,
4. `wightman_uniqueness`.

#### Phase 6. Peripheral geometric backlogs

1. BHW permutation blockers,
2. historical PET / reverse-direction residuals.

#### Phase 7. vNA / operator-algebra backlog

1. measure extension,
2. Stone/generator,
3. Tomita/modular,
4. KMS,
5. predual.

This seven-phase plan is the strongest global execution order currently
documented in the repo. Later implementation should justify any deviation from
it in the local proof docs first.
