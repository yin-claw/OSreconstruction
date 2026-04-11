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
| `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean` | exact local transcript only: first `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`, then `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` on the swapped (`g`) side, then the same recovery theorem on the unswapped (`f`) side, then transitivity/symmetry closure | adjacent canonical pairing equality for one adjacent transposition | `bvt_F_swapCanonical_pairing_of_adjacent_chain` |
| `bvt_F_swapCanonical_pairing_of_adjacent_chain` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean` | explicit adjacent-transposition factorization data for `swap i j` plus repeated `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`; it may not reopen `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`, `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`, or `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` directly | general `swap i j` canonical pairing equality, still below the downstream comparison and frontier files | `OSToWightmanBoundaryValuesComparison.lean :: bv_local_commutativity_transfer_of_swap_pairing`, then `bvt_F_swapCanonical_pairing` |
| `bv_local_commutativity_transfer_of_swap_pairing` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean` | checked comparison/transfer shell plus `bvt_F_swapCanonical_pairing_of_adjacent_chain`; it is the first downstream theorem-2 consumer after the canonical-swap package leaves `OSToWightmanBoundaryValueLimits.lean` | theorem-2 locality transfer result in the comparison layer | downstream locality assembly, `bvt_F_swapCanonical_pairing` |
| `bvt_F_swapCanonical_pairing` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean` | the finished comparison/transfer seam together with the already-closed canonical-swap package; it is not allowed to replace or absorb `OSToWightmanBoundaryValuesComparison.lean` | the thin final theorem-2 frontier wrapper consumed by later public locality assembly | downstream transfer / public locality consumers only |

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
| W13 | `Wightman/Reconstruction/Main.lean:74` | `wightman_uniqueness` | pure downstream uniqueness consumer only: may use finished `gnsQFT` + cyclicity, then must run the fixed Main-side slot order `cyclicWordVector/cyclicWordSpan -> cyclicWordVector_inner_cyclicWordVector -> uniquenessPreMap -> uniquenessPreMap_inner_formula -> uniquenessPreMap_null_of_null -> uniquenessDenseMap -> uniquenessDenseMap_inner_preserving -> uniquenessDenseMap_norm_preserving -> uniquenessDenseMap_isometry -> cyclicWord_in_range_of_uniquenessDenseMap -> cyclicWordSpan_le_range_uniquenessDenseMap -> uniquenessDenseMap_denseRange -> uniquenessDenseMap_extends_to_unitary -> uniquenessUnitary_maps_vacuum -> uniquenessUnitary_intertwines_field_on_cyclic_core -> cyclicWordSpan_is_field_core -> uniquenessUnitary_intertwines_field -> wightman_uniqueness` without reopening upstream GNS bridge work; source-checked ownership note: there is still no separate checked Main-side uniqueness support file in the repo tree, so this helper queue remains documentation-owned until a real support module is added. Physical insertion contract is now frozen too: either implement the queue directly in `Main.lean` above `:74`, or first create one explicitly named new helper module under `Wightman/Reconstruction/` and move one contiguous theorem block there with synchronized imports/docs; scattering the queue across unrelated existing reconstruction files is forbidden. First-consumer boundaries are frozen here too: `cyclicWordVector_inner_cyclicWordVector` is the only matrix-element slot, quotient descent ends at `uniquenessPreMap_null_of_null`, descended inner/norm preservation starts only after `uniquenessDenseMap`, dense-range work starts only at `cyclicWord_in_range_of_uniquenessDenseMap -> cyclicWordSpan_le_range_uniquenessDenseMap`, `uniquenessDenseMap_extends_to_unitary` is the only completion/surjectivity row and must export the unitary plus its dense-subspace extension identity, `uniquenessUnitary_intertwines_field_on_cyclic_core` is core-only, field-core closure starts only at `cyclicWordSpan_is_field_core` with the local order `cyclicWordVector_mem_domain -> span-level domain inclusion -> checked WightmanQFT field-core/graph-closure facts`, and `Main.lean:74` is assembly-only | medium |

Checked-tree clarification (2026-04-08): the current repo tree under
`OSReconstruction/Wightman/` **does** contain a live
`Wightman/NuclearSpaces/` subtree. A direct checked-tree scan shows at least
`NuclearSpace.lean`, `SchwartzNuclear.lean`, `GaussianFieldBridge.lean`,
`BochnerMinlos.lean`, `EuclideanMeasure.lean`, and `ComplexSchwartz.lean`, and
an exact direct-hole scan of that subtree gives **7** local `sorry`s:
- `NuclearSpace.lean`: 2
- `BochnerMinlos.lean`: 5

Earlier overview notes used a narrower headline count that excluded this
secondary lane, but that is no longer the active repo-wide policy. The live
whole-project census used by `README.md`,
`docs/development_plan_systematic.md`,
`docs/proof_docs_completion_plan.md`, and
`OSReconstruction/Wightman/TODO.md` is now the checked-tree **`60`-sorry**
count, and that whole-project headline already includes the `Wightman`
bucket containing the `Wightman/NuclearSpaces/*` subtree. So the point here is
not “these files are outside the headline count”; it is the sharper ownership
split:
1. the repo really has a checked `Wightman/NuclearSpaces/*` subtree with 7 live
   local `sorry`s,
2. the live repo-wide headline count is still `60`, but later docs must say
   explicitly if they switch to a narrower auxiliary census for a local lane,
   and
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
| `identity_theorem_right_halfplane` | `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:48` | none | right-half-plane identity theorem for scalar holomorphic functions | `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` only |
| `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` | `.../OSToWightmanPositivity.lean:110` | checked holomorphicity of `bvt_singleSplit_xiShiftHolomorphicValue` and `OSInnerProductTimeShiftHolomorphicValue`, plus `identity_theorem_right_halfplane` | equality of the theorem-3 scalar holomorphic traces on `{Re z > 0}` for compact positive-time single/single data | the theorem-3 `singleSplit_xiShift` support package in `OSToWightmanBoundaryValueLimits.lean` only |
| theorem-3 `singleSplit_xiShift` support layer | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean` | chosen scalar holomorphic trace, positive-real identification theorems, and `t -> 0+` limit-transfer theorems for compact positive-time single/single data | the one-variable boundary/limit facts the Section-4.3 transport package is allowed to consume | `os1TransportOneVar` first, then `os1TransportOneVar_eq_zero_iff`; `os1TransportComponent` may consume this scalar package only through those exported Stage-A surfaces, and no later theorem-3 slot may bypass this support layer |
| checked partial-spatial-Fourier foothold | `SCV/PartialFourierSpatial.lean` | none beyond the checked SCV/Schwartz infrastructure already imported there | concrete Section-4.3 support surfaces `nPointTimeSpatialCLE`, `partialFourierSpatial_fun`, `partialFourierSpatial_timeSliceSchwartz`, `partialFourierSpatial_timeSlice_hasPaleyWienerExtension`, and `partialFourierSpatial_timeSliceCanonicalExtension` on the half-space test-function side; later theorem-3 work must consume these in that order rather than inventing a new transport companion file | `os1TransportOneVar` only |
| `positiveTimeBorchersVector` + `positiveTimeBorchersVector_inner_eq` + `positiveTimeBorchersVector_norm_sq_eq` | `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:1461` / `:1467` / `:1480` | checked positive-time Hilbert-space support infrastructure already in that file | the general OS-Hilbert target for arbitrary positive-time Borchers data, together with its first checked inner/norm equalities | `bvt_transport_to_osHilbert_onImage` first; no earlier theorem-3 slot may consume this package |
| `positiveTimeBorchersVector_dense` | `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:1506` | positive-time Hilbert-space completion infrastructure already in that file | density of positive-time vectors in `OSHilbertSpace OS` | `bvt_W_positive_of_transportImage_density` only |
| `euclideanPositiveTimeSingleVector` | `.../OSToWightmanPositivity.lean:1523`, with checked norm supplier `euclideanPositiveTimeSingleVector_norm_sq_eq` at `:1530` | the same positive-time Hilbert-space support layer, but only as a downstream specialization of the general Hilbert target/equality package | canonical OS Hilbert-space vector attached to one positive-time component, together with its checked norm identity | later Stage-C single-component specializations only; `bvt_transport_to_osHilbert_onImage` must not be documented as landing here primitively |
| `os1TransportOneVar` | `OSToWightmanPositivity.lean` | theorem-3 `singleSplit_xiShift` support layer plus the checked `SCV/PartialFourierSpatial.lean` supplier chain `partialFourierSpatial_fun -> partialFourierSpatial_timeSliceSchwartz -> partialFourierSpatial_timeSlice_hasPaleyWienerExtension -> partialFourierSpatial_timeSliceCanonicalExtension` | one-variable Section-4.3 transport map on the positive-time half-space test-function codomain | `os1TransportOneVar_eq_zero_iff`, `os1TransportComponent` |
| `os1TransportOneVar_eq_zero_iff` | `OSToWightmanPositivity.lean` | `os1TransportOneVar` | explicit one-variable kernel-zero theorem for the branch-`3b` transport stage | `os1TransportComponent`, `bvt_transport_to_osHilbert_onImage_wellDefined` |
| `os1TransportComponent` | `OSToWightmanPositivity.lean` | `os1TransportOneVar`, `os1TransportOneVar_eq_zero_iff`, and the explicit Section-4.3 Fourier-Laplace transport formula | degreewise transformed-image transport map on the genuine half-space codomain | `os1TransportComponent_eq_zero_iff`, `BvtTransportImageSequence` |
| `os1TransportComponent_eq_zero_iff` | `OSToWightmanPositivity.lean` | `os1TransportComponent` | explicit degreewise kernel-zero theorem for the transformed-image stage | `bvt_transport_to_osHilbert_onImage_wellDefined`, `BvtTransportImageSequence` |
| `BvtTransportImageSequence` | `OSToWightmanPositivity.lean` | `os1TransportComponent` | bundled transformed-image core on which the quadratic identity is actually proved | `bvt_transport_to_osHilbert_onImage_wellDefined` only; later slots may reuse this transformed-image object only downstream of `bvt_transport_to_osHilbert_onImage` and the separate Lemma-4.2 seam `lemma42_matrix_element_time_interchange`, never directly from this row |
| `bvt_transport_to_osHilbert_onImage_wellDefined` | `OSToWightmanPositivity.lean` | `BvtTransportImageSequence`, degreewise representative choice, difference of two chosen preimage families, then kernel-zero consumption in the strict order `os1TransportOneVar_eq_zero_iff -> os1TransportComponent_eq_zero_iff` | proof that the OS-Hilbert transport value is independent of the chosen transformed-image preimage | `bvt_transport_to_osHilbert_onImage` |
| `bvt_transport_to_osHilbert_onImage` | `OSToWightmanPositivity.lean` | `BvtTransportImageSequence`, `bvt_transport_to_osHilbert_onImage_wellDefined`, and the checked general Hilbert target/equality package `positiveTimeBorchersVector` / `positiveTimeBorchersVector_inner_eq` / `positiveTimeBorchersVector_norm_sq_eq` first entering exactly here | OS Hilbert-space transport map landing first in the general positive-time Borchers target attached to transformed-image data | `lemma42_matrix_element_time_interchange` first, then `bvt_wightmanInner_eq_transport_norm_sq_onImage`; later rows may not bypass this map and consume representative data directly, and the single-component wrapper may re-enter only downstream as a specialization |
| `bvt_wightmanInner_eq_transport_norm_sq_onImage` | `OSToWightmanPositivity.lean` | `bvt_transport_to_osHilbert_onImage_wellDefined` to freeze one representative family first, then `bvt_transport_to_osHilbert_onImage`, then `lemma42_matrix_element_time_interchange`, and only then the repaired OS II `bvt_F` / `bvt_W` kernel route together with norm-square recognition via the checked general equality `positiveTimeBorchersVector_norm_sq_eq` on the actual transport target | the transformed-image quadratic identity `(W(F,F)).re = ‖u(F)‖^2` on the image core only | `bvt_W_positive_of_transportImage_density` |
| `bvt_W_positive_of_transportImage_density` | `OSToWightmanPositivity.lean` | `bvt_wightmanInner_eq_transport_norm_sq_onImage`, `positiveTimeBorchersVector_dense`, and the continuity/density closure step in the Hilbert codomain | theorem-3 positivity for arbitrary `BorchersSequence d` as an implementation-side theorem | `bvt_W_positive` |
| `bvt_W_positive` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean` | the implementation-side positivity theorem from `OSToWightmanPositivity.lean` | the private frontier theorem consumed by downstream wrappers | downstream transfer / public reconstruction consumers only |

Exact checked-present vs planned split after the live source check:

1. checked-present in `OSToWightmanPositivity.lean` today:
   the scalar Stage-A entry pair `identity_theorem_right_halfplane` (`:48`)
   and `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` (`:110`); the
   general Hilbert target/equality package `positiveTimeBorchersVector`
   (`:1461`), `positiveTimeBorchersVector_inner_eq` (`:1467`), and
   `positiveTimeBorchersVector_norm_sq_eq` (`:1480`), first consumed only by
   `bvt_transport_to_osHilbert_onImage`; the density supplier
   `positiveTimeBorchersVector_dense` (`:1506`), first consumed only by
   `bvt_W_positive_of_transportImage_density`; and the downstream
   single-component specialization `euclideanPositiveTimeSingleVector`
   (`:1523`) with norm supplier `euclideanPositiveTimeSingleVector_norm_sq_eq`
   (`:1530`), which is not part of the primitive theorem-3 closure lane but a
   later specialization of the general Hilbert target.
2. checked-present in `OSToWightmanBoundaryValueLimits.lean` today: the theorem-3
   `singleSplit_xiShift` scalar holomorphic / positive-real / limit package,
   with the internal supplier/consumer split now frozen literally as
   `:260 :: bvt_singleSplit_xiShiftHolomorphicValue`
   -> `:273 :: differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue`
   -> `:290 :: bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
   -> supplier-only Schwinger leg `:314 :: bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`
   -> supplier-only Schwinger limit `:350 :: tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
   -> deprecated bridge `:388 :: tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift` (historical/quarantined only; no live theorem-3/theorem-4 consumer)
   -> helper-only uniqueness lemma `:494 :: eqOn_rightHalfPlane_of_ofReal_eq`
   -> uniqueness packaging `:536 :: bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
   -> sole live terminal theorem `:446 :: tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`.
   First-consumer discipline is part of the contract: Stage A may consume only
   the scalar object/positive-real shell (`:260`, `:290`); the optional
   uniqueness detour may consume only `:494 -> :536`; and the first theorem-3
   terminal consumer is exactly `:446`, never `:314`, `:350`, or `:388`.
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
   consume, but a direct source check still finds **none** of the theorem-4
   extraction slots there yet. In particular,
   `normalizedZeroDegreeRightVector`,
   `zeroDegree_right_single_wightman_extracts_factor`,
   `zeroDegree_right_single_os_extracts_factor`,
   `zero_degree_component_comparison_for_normalized_right_vector`,
   `cluster_left_factor_transport`, and `cluster_right_factor_transport` are
   still planned theorem-slot names, not checked helper theorems already in the
   file.
2. `OSToWightmanBoundaryValuesBase.lean` already contains the cluster-side base
   reductions
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitLargeSpatial`,
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitSchwingerLargeSpatial`,
   and the legacy theorem
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`.
   It does **not yet** contain the corrected bridge
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
   or the thin wrapper `bvt_cluster_positiveTime_singleSplit_core`; those are
   still planned theorem-slot work owned by this base file.
3. `OSToWightmanBoundaryValues.lean` currently exposes only the checked
   frontier shell at `:27 :: bv_cluster_transfer_of_canonical_eventually`,
   `:398 :: private bvt_F_clusterCanonicalEventually_translate`,
   `:414 :: private bvt_F_clusterCanonicalEventually`, and
   `:473 :: private bvt_W_cluster`. The public canonical-shell adapter family
   `canonical_cluster_integrand_eq_singleSplit_integrand`
   -> `canonical_translate_factor_eq_singleSplit_translate_factor`
   -> `singleSplit_core_rewrites_to_canonical_shell`
   -> `canonical_shell_limit_of_rewrite`
   -> `bvt_cluster_canonical_from_positiveTime_core`
   remains planned support work above that checked frontier shell rather than
   checked code already present in the file, and the consumer boundary is now
   fixed literally as `canonical_shell_limit_of_rewrite`
   -> `bvt_cluster_canonical_from_positiveTime_core`
   -> `:398 :: private bvt_F_clusterCanonicalEventually_translate`.
4. `OSToWightmanBoundaryValueLimits.lean` is **not** a theorem-4 ownership
   file on the current route; it remains theorem-2/theorem-3 support only.
   The only theorem-4 slot allowed to touch its checked scalar package is
   `canonical_shell_limit_of_rewrite`, and even there the proof transcript is
   fixed literally as
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
   -> optional right-half-plane uniqueness only via
   `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` +
   `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
   -> final Wightman-target `t → 0+` transport only via
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`.
   This is now frozen as a literal theorem-construction contract too:
   `canonical_shell_limit_of_rewrite` must start from the already-exported
   shell statement from `singleSplit_core_rewrites_to_canonical_shell`, keep
   that shell fixed, and then perform only those three moves. It may not reopen
   the kernel rewrite, the translated-factor rewrite, or the base-core
   application. Correspondingly,
   `bvt_cluster_canonical_from_positiveTime_core` is only the public shell
   restatement of that exported eventual statement; it may not import any
   `BoundaryValueLimits.lean` theorem directly or perform leftover shell
   normalization, uniqueness, or limit transport. So the public adapter lane
   must arrive at `canonical_shell_limit_of_rewrite` with the canonical-shell
   integrand rewrite and translated-factor rewrite already discharged; this
   theorem is a pure limit-transport slot, not a second hidden place to repair
   shell shape.

Theorem-4 proof transcript, frozen in exact Lean execution order:

1. build the literal degree-`0` unit Borchers vector
   `normalizedZeroDegreeRightVector`;
2. prove its structural bookkeeping lemmas
   `normalizedZeroDegreeRightVector_bound`,
   `normalizedZeroDegreeRightVector_funcs_zero`, and
   `normalizedZeroDegreeRightVector_funcs_pos`;
3. use the checked right-single inner-product surfaces to extract the two
   one-factor identities
   `zeroDegree_right_single_wightman_extracts_factor` and
   `zeroDegree_right_single_os_extracts_factor`;
4. close the unique surviving `m = 0` comparison slot
   `zero_degree_component_comparison_for_normalized_right_vector` from the
   repaired theorem-3 transport package;
5. package those ingredients into the one-factor transport theorems
   `cluster_left_factor_transport` and `cluster_right_factor_transport`;
6. consume the checked base reductions together with those two transport inputs
   to prove the repaired bridge
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`;
7. wrap that repaired bridge as the positive-time shell theorem
   `bvt_cluster_positiveTime_singleSplit_core`;
8. only then begin the public-shell adapter package in
   `OSToWightmanBoundaryValues.lean`, in the strict order
   `canonical_cluster_integrand_eq_singleSplit_integrand`
   -> `canonical_translate_factor_eq_singleSplit_translate_factor`
   -> `singleSplit_core_rewrites_to_canonical_shell`
   -> `canonical_shell_limit_of_rewrite`
   -> `bvt_cluster_canonical_from_positiveTime_core`;
9. let the final frontier theorem
   `bvt_F_clusterCanonicalEventually_translate` consume only
   `bvt_cluster_canonical_from_positiveTime_core`, after which the already
   checked wrappers `bvt_F_clusterCanonicalEventually`,
   `bv_cluster_transfer_of_canonical_eventually`, and `bvt_W_cluster` resume.

To stop later Lean work from reconstructing the theorem-4 handoff from the
blueprint by memory, the live theorem-4 lane is now frozen here as a slot
ledger too:

| Slot | File ownership | Must consume exactly | Must prove / export exactly | Next allowed consumer |
| --- | --- | --- | --- | --- |
| `normalizedZeroDegreeRightVector` | `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | the degree-`0` unit shell only | the literal positive-time Borchers vector concentrated in degree `0` with value `1` | its three structural lemmas, then `conjTensorProduct_degreeZeroUnit_eq`, `osConjTensorProduct_degreeZeroUnit_eq`, `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`, then the two right-single extraction lemmas | planned slot; not source-checked as present yet |
| `normalizedZeroDegreeRightVector_bound` / `..._funcs_zero` / `..._funcs_pos` | same theorem-3/theorem-4 bookkeeping layer in `OSToWightmanPositivity.lean` | `normalizedZeroDegreeRightVector` | the exact structural facts `bound = 0`, degree-`0` shell is the unit, and all positive-degree shells vanish | `conjTensorProduct_degreeZeroUnit_eq`, `osConjTensorProduct_degreeZeroUnit_eq`, `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`, `zeroDegree_right_single_wightman_extracts_factor`, `zeroDegree_right_single_os_extracts_factor`, `zero_degree_component_comparison_for_normalized_right_vector` | planned slots; not source-checked as present yet |
| `conjTensorProduct_degreeZeroUnit_eq` | `OSToWightmanPositivity.lean` | `normalizedZeroDegreeRightVector_funcs_zero` | the exact classical/Wightman degree-`0` normalization rewrite used before right-single extraction may fire | `zeroDegree_right_single_wightman_extracts_factor` | planned slot; not source-checked as present yet |
| `osConjTensorProduct_degreeZeroUnit_eq` | `OSToWightmanPositivity.lean` | `normalizedZeroDegreeRightVector_funcs_zero` | the exact classical/OS degree-`0` normalization rewrite used before right-single extraction may fire | `zeroDegree_right_single_os_extracts_factor` | planned slot; not source-checked as present yet |
| `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq` | `OSToWightmanPositivity.lean` | `normalizedZeroDegreeRightVector_funcs_zero` | the exact cast/zero-diagonal normalization rewrite needed to keep the degree-`0` unit shell explicit before theorem-4 transport packaging | `zeroDegree_right_single_wightman_extracts_factor`, `zeroDegree_right_single_os_extracts_factor`, `zero_degree_component_comparison_for_normalized_right_vector` | planned slot; not source-checked as present yet |
| `zeroDegree_right_single_wightman_extracts_factor` | `OSToWightmanPositivity.lean` | checked `OSReconstruction/Wightman/Reconstruction/Core.lean:393 :: WightmanInnerProduct_right_single`, then in strict Lean order `normalizedZeroDegreeRightVector_funcs_zero` -> `normalizedZeroDegreeRightVector_funcs_pos` -> `conjTensorProduct_degreeZeroUnit_eq` -> `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`; no separate scalar-normalization slot is allowed between these rewrites | extraction of the left Wightman factor against the normalized zero-degree right vector, with the cast-removal step made explicit before definitional closure | `cluster_left_factor_transport` | planned slot; not source-checked as present yet |
| `zeroDegree_right_single_os_extracts_factor` | `OSToWightmanPositivity.lean` | checked `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean:466 :: OSInnerProduct_right_single`, then in strict Lean order `normalizedZeroDegreeRightVector_funcs_zero` -> `normalizedZeroDegreeRightVector_funcs_pos` -> `osConjTensorProduct_degreeZeroUnit_eq` -> `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`; again no extra scalar-normalization slot is allowed | extraction of the left OS factor against the normalized zero-degree right vector, with the cast-removal step made explicit before definitional closure | `cluster_left_factor_transport` | planned slot; not source-checked as present yet |
| `zero_degree_component_comparison_for_normalized_right_vector` | `OSToWightmanPositivity.lean` | corrected theorem-3 Section-4.3 transport package plus the normalized degree-`0` vanishing facts | the unique surviving `m = 0` transport comparison needed for theorem-4 factor extraction | `cluster_left_factor_transport`, `cluster_right_factor_transport` | planned slot; not source-checked as present yet |
| `cluster_left_factor_transport` | `OSToWightmanPositivity.lean` | `zeroDegree_right_single_wightman_extracts_factor`, `zeroDegree_right_single_os_extracts_factor`, `zero_degree_component_comparison_for_normalized_right_vector` | corrected theorem-3-to-theorem-4 left one-factor transport equality | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` | planned slot; not source-checked as present yet |
| `cluster_right_factor_transport` | `OSToWightmanPositivity.lean` | the right-side analogue of `cluster_left_factor_transport`: reuse the same normalized degree-`0` witness package via the definitional alias `normalizedZeroDegreeLeftVector d := normalizedZeroDegreeRightVector d`, then consume the corresponding right-single Wightman/OS extraction rewrites together with `zero_degree_component_comparison_for_normalized_right_vector` to move the nontrivial shell to the second input without inventing a second normalization package | corrected theorem-3-to-theorem-4 right one-factor transport equality | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` | planned slot; not source-checked as present yet |
| `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean` | checked base reductions through `:2214 :: ...singleSplitLargeSpatial`, `:2352 :: ...singleSplitSchwingerLargeSpatial`, and `:2514 :: ...singleSplitFactorComparison` plus `cluster_left_factor_transport` and `cluster_right_factor_transport` | the repaired positive-time single-split bridge with the same conclusion shape as the legacy `...singleSplitFactorComparison` theorem but without false same-shell hypotheses | `bvt_cluster_positiveTime_singleSplit_core` | planned slot; base file currently has only the legacy bridge |
| `bvt_cluster_positiveTime_singleSplit_core` | `OSToWightmanBoundaryValuesBase.lean` | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` only, with the proof transcript frozen as `state the exact ordered-positive-time / compact-support single-split eventual shell -> apply bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison -> close` | the theorem-4 cluster statement on the ordered-positive-time / compact-support single-split shell, exported from the base file as the sole theorem allowed to enter the public adapter ladder | `canonical_cluster_integrand_eq_singleSplit_integrand` first; the remaining public queue is `canonical_translate_factor_eq_singleSplit_translate_factor -> singleSplit_core_rewrites_to_canonical_shell -> canonical_shell_limit_of_rewrite -> bvt_cluster_canonical_from_positiveTime_core` | planned slot; not source-checked as present yet |
| `canonical_cluster_integrand_eq_singleSplit_integrand` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean` | only the checked canonical-direction surfaces imported through `OSToWightmanBoundaryValuesComparison.lean` (`canonicalForwardConeDirection`, `canonicalForwardConeDirection_mem`) plus the repaired base-core shell statement exported by `bvt_cluster_positiveTime_singleSplit_core`; it may **not** import theorem-3 scalar/limit transport from `OSToWightmanBoundaryValueLimits.lean` | the theorem-4-specific kernel rewrite inside the exact shell already visible at `:398 :: private bvt_F_clusterCanonicalEventually_translate`, i.e. it rewrites only the analytic factor `bvt_F OS lgc (n + m) (fun k μ => ↑(x k μ) + t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)` into the positive-time / single-split kernel expected by the repaired base theorem; this is the first public-wrapper consumer of `bvt_cluster_positiveTime_singleSplit_core`, not a sibling that can be skipped | `singleSplit_core_rewrites_to_canonical_shell` | planned slot; source-check confirms the final wrapper file still has no landed cluster-specific rewrite theorem under this seam |
| `canonical_translate_factor_eq_singleSplit_translate_factor` | `OSToWightmanBoundaryValues.lean` | only the checked translated-shell data already in scope (`translateSchwartzNPoint` together with the same canonical-direction surface) plus the translated-shell statement shape appearing in private `bvt_F_clusterCanonicalEventually_translate`; it may **not** hide the eventual/limit step and it may not consume the base theorem directly without the integrand rewrite slot already fixed | the theorem-4-specific test-function rewrite in that same shell, i.e. it rewrites only `((f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x)` into the single-split right-factor form expected after `canonical_cluster_integrand_eq_singleSplit_integrand` has already frozen the analytic-kernel side of the shell | `singleSplit_core_rewrites_to_canonical_shell` | planned slot; source-check confirms the final wrapper file still has no landed cluster-specific rewrite theorem under this seam |
| `singleSplit_core_rewrites_to_canonical_shell` | `OSToWightmanBoundaryValues.lean` | `bvt_cluster_positiveTime_singleSplit_core`, `canonical_cluster_integrand_eq_singleSplit_integrand`, `canonical_translate_factor_eq_singleSplit_translate_factor` | shell-only reduction of the `:398` frontier statement: fix the full quantifier block `(n, m, f, g, ε, a, t)`; rewrite the analytic kernel first via `canonical_cluster_integrand_eq_singleSplit_integrand`; rewrite the translated test-function factor second via `canonical_translate_factor_eq_singleSplit_translate_factor`; verify the eventual/limit quantifier block is still unchanged and the shell now matches the ordered-positive-time single-split statement verbatim; only then invoke `bvt_cluster_positiveTime_singleSplit_core`, with both rewrites discharged before the limit step begins | `canonical_shell_limit_of_rewrite` | planned slot; final wrapper file currently exposes only the consumer shell |
| `canonical_shell_limit_of_rewrite` | `OSToWightmanBoundaryValues.lean` | `singleSplit_core_rewrites_to_canonical_shell` plus only the checked scalar-holomorphic / limit-transport package imported from `OSToWightmanBoundaryValueLimits.lean`; its internal proof transcript is fixed as `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq` -> optional right-half-plane uniqueness only via `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` + `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq` -> final Wightman-target `t → 0+` transport only via `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`. The Schwinger-target theorems `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift` and `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger` are lower supplier legs only, and the deprecated bridge `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift` is forbidden here | transport from the rewritten canonical shell statement to the eventual/limit form consumed immediately by `bvt_cluster_canonical_from_positiveTime_core` and then private `bvt_F_clusterCanonicalEventually_translate` | `bvt_cluster_canonical_from_positiveTime_core` | planned slot; final wrapper file currently exposes only the consumer shell |
| `bvt_cluster_canonical_from_positiveTime_core` | `OSToWightmanBoundaryValues.lean` | `canonical_shell_limit_of_rewrite` only | the explicit public canonical-shell adapter theorem above the positive-time core, stated as the immediate and only allowed input to the checked frontier shell `:398 :: private bvt_F_clusterCanonicalEventually_translate` | `:398 :: private bvt_F_clusterCanonicalEventually_translate` only | planned slot; final wrapper file currently exposes only the consumer shell |
| `bvt_F_clusterCanonicalEventually_translate` | `OSToWightmanBoundaryValues.lean` | `bvt_cluster_canonical_from_positiveTime_core` only | the checked private theorem-4 frontier statement at `:398`, consumed downstream only by `:414 :: private bvt_F_clusterCanonicalEventually`, `:27 :: bv_cluster_transfer_of_canonical_eventually`, and `:473 :: private bvt_W_cluster` | downstream checked transfer / public cluster consumers only | checked-present private frontier theorem |

What this resolves at route level:

1. theorem 4 is now fixed as a strict consumer lane above theorem 3 rather than
   a place to reopen continuation or positivity;
2. the repaired positive-time bridge belongs in
   `OSToWightmanBoundaryValuesBase.lean`, while the public canonical-shell
   adapter belongs in `OSToWightmanBoundaryValues.lean`;
3. the first two adapter slots have frozen consumes boundaries: the integrand
   rewrite may use only canonical-direction plus repaired-base-core data, while
   the translated-factor rewrite may use only translated-shell data already in
   scope plus the private frontier theorem shape;
4. `OSToWightmanBoundaryValueLimits.lean` is explicitly excluded from theorem-4
   ownership on the current checked tree except as the checked supplier package
   for `canonical_shell_limit_of_rewrite`; inside that single allowed limit slot
   the subproof order is now frozen too:
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
   -> optional right-half-plane uniqueness via
    `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue`
    + `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
    -> final Wightman-target `t → 0+` transport via
    `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`;
5. the implementation queue is now frozen as a literal cross-file theorem
   creation order rather than a slogan-level “cluster package”:
   - first, in `OSToWightmanPositivity.lean`, create only
     `normalizedZeroDegreeRightVector`
     -> `normalizedZeroDegreeRightVector_bound`
     -> `normalizedZeroDegreeRightVector_funcs_zero`
     -> `normalizedZeroDegreeRightVector_funcs_pos`
     -> `conjTensorProduct_degreeZeroUnit_eq`
     -> `osConjTensorProduct_degreeZeroUnit_eq`
     -> `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`
     -> `zeroDegree_right_single_wightman_extracts_factor`
     -> `zeroDegree_right_single_os_extracts_factor`
     -> `zero_degree_component_comparison_for_normalized_right_vector`
     -> `cluster_left_factor_transport`
     -> `cluster_right_factor_transport`;
   - second, in `OSToWightmanBoundaryValuesBase.lean`, create only
     `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
     -> `bvt_cluster_positiveTime_singleSplit_core`;
   - third, in `OSToWightmanBoundaryValues.lean`, create only
     `canonical_cluster_integrand_eq_singleSplit_integrand`
     -> `canonical_translate_factor_eq_singleSplit_translate_factor`
     -> `singleSplit_core_rewrites_to_canonical_shell`
     -> `canonical_shell_limit_of_rewrite`
     -> `bvt_cluster_canonical_from_positiveTime_core`;
   - fourth, let the already-checked frontier consumer remain just that:
     `OSToWightmanBoundaryValues.lean:398 :: private bvt_F_clusterCanonicalEventually_translate`.
6. the base/adaptor seam is now frozen explicitly: later Lean work may not feed
   `cluster_left_factor_transport`, `cluster_right_factor_transport`, or
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
   straight into `canonical_shell_limit_of_rewrite` or the private frontier
   theorem. The only theorem allowed to leave the base file is
   `bvt_cluster_positiveTime_singleSplit_core`, and the public adapter lane
   must begin there specifically through
   `canonical_cluster_integrand_eq_singleSplit_integrand`, not by jumping
   directly to `singleSplit_core_rewrites_to_canonical_shell`.
7. the public-wrapper seam is now frozen just as literally:
   `OSToWightmanBoundaryValues.lean :: canonical_cluster_integrand_eq_singleSplit_integrand`
   is the **first** theorem-4 slot allowed to live in the public wrapper file,
   and `OSToWightmanBoundaryValues.lean:398 :: private
   bvt_F_clusterCanonicalEventually_translate` is the **first checked
   downstream consumer shell**. Therefore later Lean work may not bypass the
   adapter queue by proving a mixed rewrite/limit theorem that jumps directly
   from `bvt_cluster_positiveTime_singleSplit_core` to the private frontier, or
   by hiding the canonical integrand rewrite / translated-factor rewrite inside
   `canonical_shell_limit_of_rewrite`.
   `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` and
   `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
   -> final Wightman-target transport by
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`,
   with the Schwinger-target limit theorems retained only as lower supplier
   legs; `OSToWightmanBoundaryValues.lean` currently exposes only the final
   consumer shell rather than any already-landed cluster-specific rewrite
   lemmas for the canonical integrand / translate-factor seam;
5. the legacy theorem
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

Exact theorem-2 endgame execution contract now enforced by this triage note:

1. `OSToWightmanBoundaryValueLimits.lean` starts only after
   `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` is already available;
   it does not own the adjacent raw-boundary closure theorem itself.
2. `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` is the first theorem
   in that sibling subsection and must specialize
   `boundary_value_recovery_forwardTube_of_flatRegular_from_bv` at the checked
   boundary-functional package `bvt_W`, `bvt_W_continuous`,
   `bvt_boundary_values`, and `canonicalForwardConeDirection`.
3. `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` is the
   second theorem in that sibling subsection and must run in the literal order
   raw-boundary theorem first -> swapped-side canonical recovery second ->
   unswapped-side canonical recovery third -> transitivity/symmetry closure.
4. `bvt_F_swapCanonical_pairing_of_adjacent_chain` is the third theorem in that
   sibling subsection and is only the adjacent-factorization reducer above the
   adjacent canonical theorem; it may not reopen raw-boundary or recovery
   theorems directly.

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
- `Wightman/Reconstruction/GNSHilbertSpace.lean:1249`

Checked owner/consumer boundary:

1. the earlier GNS translation-continuity lane is already closed in the live
   tree at `:1005` and `:1062`;
2. `:1249 :: gns_matrix_coefficient_holomorphic_axiom` is therefore the first
   still-open spectrum-condition owner slot;
3. the theorem should be implemented as a one-variable forward-tube consumer
   only, not as a second home for many-variable SCV package design;
4. `gns_cyclicity`, `gnsQFT`, and `wightman_uniqueness` are downstream
   consumers and may not absorb any part of this boundary-value bridge.

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
- `Wightman/Reconstruction/Main.lean:74`

Checked owner/consumer boundary:

1. uniqueness is downstream of `GNSHilbertSpace.lean:2114 :: gnsQFT`;
2. it may consume cyclicity facts, but it may not reopen the spectrum bridge,
   the nuclear bridge, or the quotient-density work owned by
   `GNSHilbertSpace.lean:1643 :: gns_cyclicity`;
3. the live tree contains no checked `Wightman/Reconstruction/Main/*` helper
   module or other separate Main-side uniqueness support `.lean` file, whereas
   the nuclear-side lane really does have checked support files under
   `Wightman/NuclearSpaces/*` (including `Helpers/PositiveDefiniteKernels.lean`
   and `NuclearOperator.lean`); therefore the uniqueness helper queue is still
   blueprint/documentation-owned rather than file-owned below `Main.lean`;
4. physical insertion is restricted to two layouts only: either the queue is
   created directly in `Main.lean` above `:74`, or one explicitly named new
   helper module under `Wightman/Reconstruction/` is created first and then one
   contiguous theorem block is moved there with imports/docs updated in the
   same pass;
5. the first implementation slot here is the cyclic-word / dense-core map, not
   a new abstract reconstruction theorem, and later Lean work may not scatter
   those uniqueness slots across unrelated existing reconstruction files.

Concrete next packages:

1. cyclic-word dense-core package (`cyclicWordVector` / `cyclicWordSpan`) plus the exact matrix-element slot `cyclicWordVector_inner_cyclicWordVector`,
2. pre-quotient transfer package `uniquenessPreMap` / `uniquenessPreMap_inner_formula` / `uniquenessPreMap_null_of_null`,
3. descended-map metric package `uniquenessDenseMap` / `uniquenessDenseMap_inner_preserving` / `uniquenessDenseMap_norm_preserving` / `uniquenessDenseMap_isometry`,
4. direct dense-range closure `cyclicWord_in_range_of_uniquenessDenseMap` -> `cyclicWordSpan_le_range_uniquenessDenseMap` -> `uniquenessDenseMap_denseRange`,
5. unitary extension,
6. vacuum transport,
7. cyclic-core then full-domain field intertwining via the separate core theorem `cyclicWordSpan_is_field_core`.

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
   `sorry`s already included inside the live whole-project headline `60`-count;
   when a narrower auxiliary census is used for that lane, the doc must say so
   explicitly instead of implying the local support files sit outside the repo-
   wide count
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
