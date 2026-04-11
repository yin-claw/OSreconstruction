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
| `OSReconstruction/Wightman` | 20 |
| `OSReconstruction/SCV` | 2 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 36 |
| **Total** | **60** |

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
     A live source check now shows three checked supplier families by first
     consumer, not one flat support bag: scalar Stage-A entry surfaces
     `identity_theorem_right_halfplane` (`:48`) and
     `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` (`:110`); then the
     checked general Hilbert-target/equality package
     `positiveTimeBorchersVector` (`:1461`),
     `positiveTimeBorchersVector_inner_eq` (`:1467`), and
     `positiveTimeBorchersVector_norm_sq_eq` (`:1480`); then the checked
     density theorem `positiveTimeBorchersVector_dense` (`:1506`) as the
     final-closure-only supplier; and only outside that primitive closure lane
     the later single-component specialization
     `euclideanPositiveTimeSingleVector` (`:1523`, norm supplier
     `euclideanPositiveTimeSingleVector_norm_sq_eq` at `:1530`) kept
     explicitly downstream of the general Stage-C target and downstream of the
     density theorem's first consumer. The fully split
     Section-4.3 transport/closure theorem names in the blueprint remain
     planned theorem-slot targets rather than already-landed production lemmas.
     First-consumer rule: the scalar `:48` / `:110` pair enters first at
     `os1TransportOneVar` / `os1TransportOneVar_eq_zero_iff`, the general
     Hilbert-target/equality package first enters at
     `bvt_transport_to_osHilbert_onImage`, the single-component wrapper is
     downstream specialization only, and the density theorem first enters at
     `bvt_W_positive_of_transportImage_density`
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
     older planning prose. The checked file currently exposes only the three
     frozen support families named above, in first-consumer order rather than
     source-file order: scalar Stage-A entry pair (`:48`, `:110`) ->
     general Hilbert target/equality package (`:1461`, `:1467`, `:1480`) ->
     density theorem (`:1506`), with the single-component wrapper
     (`:1523`, `:1530`) kept explicitly downstream as specialization only.
     The Section-4.3 transport block is still missing under separate theorem
     names, and no summary is allowed to compress those families back into a
     generic “A/B + Hilbert-density support” bag
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
  still lacks a checked support-file foothold: `OSReconstruction/SCV/PartialFourierSpatial.lean`
  is already in the repo and already owns the checked supplier chain
  `partialFourierSpatial_fun`
  -> `partialFourierSpatial_timeSliceSchwartz`
  -> `partialFourierSpatial_timeSlice_hasPaleyWienerExtension`
  -> `partialFourierSpatial_timeSliceCanonicalExtension`.
  The remaining documentation burden is therefore not “find the support file”
  but “freeze the exact Lean execution ledger above it”. Read theorem 3 in the
  following owner / consumes / exports / next-consumer order:

  | Slot | Ownership | Consumes | Exports | Next consumer |
  | --- | --- | --- | --- | --- |
  | checked branch-`3b` SCV foothold | `OSReconstruction/SCV/PartialFourierSpatial.lean` | existing SCV/Schwartz infrastructure in that file | `partialFourierSpatial_fun`, `partialFourierSpatial_timeSliceSchwartz`, `partialFourierSpatial_timeSlice_hasPaleyWienerExtension`, `partialFourierSpatial_timeSliceCanonicalExtension` | `os1TransportOneVar` |
  | `os1TransportOneVar` | `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | theorem-3 `singleSplit_xiShift` support route plus the checked SCV supplier chain above, with source-checked scalar entry seam `identity_theorem_right_halfplane` (`OSToWightmanPositivity.lean:48`) -> `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` (`:110`) | one-variable Section-4.3 transport map on the corrected half-space codomain | `os1TransportOneVar_eq_zero_iff`, `os1TransportComponent` |
  | `os1TransportOneVar_eq_zero_iff` | same file | `os1TransportOneVar` together with the positive-half-line boundary-value uniqueness input; the checked `:48` / `:110` scalar suppliers are first consumed on this Stage-A lane, not by later closure slots | one-variable kernel-zero theorem | `os1TransportComponent`, `bvt_transport_to_osHilbert_onImage_wellDefined` |
  | `os1TransportComponent` | same file | `os1TransportOneVar`, `os1TransportOneVar_eq_zero_iff`, and the explicit Section-4.3 Fourier-Laplace transport formula `(4.19)`-`(4.20)` | degreewise transformed-image transport map | `os1TransportComponent_eq_zero_iff`, `BvtTransportImageSequence` |
  | `os1TransportComponent_eq_zero_iff` | same file | `os1TransportComponent` | degreewise kernel-zero theorem | `BvtTransportImageSequence`, `bvt_transport_to_osHilbert_onImage_wellDefined` |
  | `BvtTransportImageSequence` | same file | `os1TransportComponent` | transformed-image core object on which positivity is closed | `bvt_transport_to_osHilbert_onImage_wellDefined` only; the quadratic-identity lane may see this object again only downstream of the transport-map theorem and the separate Lemma-4.2 seam |
  | `bvt_transport_to_osHilbert_onImage_wellDefined` | same file | `BvtTransportImageSequence`, degreewise representative choice, difference of two chosen preimage families, then kernel-zero consumption in the strict order `os1TransportOneVar_eq_zero_iff` -> `os1TransportComponent_eq_zero_iff` | proof that the OS-Hilbert transport value is independent of the chosen transformed-image preimage | `bvt_transport_to_osHilbert_onImage` |
  | `bvt_transport_to_osHilbert_onImage` | same file | `BvtTransportImageSequence`, `bvt_transport_to_osHilbert_onImage_wellDefined`, and the checked general Hilbert embedding package in `OSToWightmanPositivity.lean`: `positiveTimeBorchersVector` together with the first checked equalities `positiveTimeBorchersVector_inner_eq` / `positiveTimeBorchersVector_norm_sq_eq`; the single-component wrapper `euclideanPositiveTimeSingleVector` (`:1523`) with norm supplier `euclideanPositiveTimeSingleVector_norm_sq_eq` (`:1530`) is a later specialization of that package rather than the primitive transport target | OS Hilbert-space transport map on transformed-image data | `lemma42_matrix_element_time_interchange` first, then `bvt_wightmanInner_eq_transport_norm_sq_onImage`; later rows may not bypass this map and consume representative choices directly |
  | `lemma42_matrix_element_time_interchange` | same file | `bvt_transport_to_osHilbert_onImage`, transformed-image data, and the repaired OS-II-backed `bvt_F` / `bvt_W` continuation kernel | explicit Lemma-4.2 matrix-element interchange seam | `bvt_wightmanInner_eq_transport_norm_sq_onImage` |
  | `bvt_wightmanInner_eq_transport_norm_sq_onImage` | same file | `bvt_transport_to_osHilbert_onImage_wellDefined` to freeze one representative family first, then `bvt_transport_to_osHilbert_onImage`, then `lemma42_matrix_element_time_interchange`, and only then norm-square recognition against the repaired OS-II-backed `bvt_F` / `bvt_W` kernel route via the checked general norm theorem `positiveTimeBorchersVector_norm_sq_eq` on the actual transport target | on-image quadratic identity | `bvt_W_positive_of_transportImage_density` |
  | `bvt_W_positive_of_transportImage_density` | same file | on-image quadratic identity plus the checked Hilbert-density support `positiveTimeBorchersVector_dense` (`OSToWightmanPositivity.lean:1506`), first consumed here rather than in an earlier transport theorem | implementation-side positivity closure theorem | `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean :: bvt_W_positive` |

  Anti-drift rules for this planning note:
  1. `bvt_transport_to_osHilbert_onImage_wellDefined` is a mandatory theorem
     slot, not a fact hidden inside `bvt_transport_to_osHilbert_onImage`;
  2. the kernel-zero theorems are consumed at that well-definedness stage, not
     later by slogan-level “injectivity”;
  3. the quadratic-identity proof transcript is fixed as representative choice
     already discharged by `bvt_transport_to_osHilbert_onImage_wellDefined`
     -> transport-map definition into the checked general target
     `positiveTimeBorchersVector` -> `lemma42_matrix_element_time_interchange`
     -> norm-square recognition via `positiveTimeBorchersVector_norm_sq_eq`, so
     later Lean work may not collapse those substeps back into one route-level
     slogan or silently replace the general transport target with the later
     single-component specialization; and
  4. quotient-side dense-range theorems remain in the separate
     paper-faithfulness lane and must not be reintroduced as the live
     positivity-closing route.
- theorem 4 should no longer be described only as the final private wrapper
  `bvt_cluster`: the checked repo already has the base reductions in
  `OSToWightmanBoundaryValuesBase.lean`, but the corrected bridge theorem and
  the public canonical-shell adapter package are still missing named theorem
  slots that must be introduced explicitly before the final wrapper proof is
  treated as implementation-ready. Source-check against the live tree now fixes
  the checked/planned split more sharply: `OSToWightmanBoundaryValuesBase.lean`
  really contains `...singleSplitLargeSpatial`,
  `...singleSplitSchwingerLargeSpatial`, and legacy
  `...singleSplitFactorComparison`; `OSToWightmanBoundaryValues.lean` really
  contains only the final consumer shell
  (`bv_cluster_transfer_of_canonical_eventually`, private
  `bvt_F_clusterCanonicalEventually_translate`, private
  `bvt_F_clusterCanonicalEventually`, private `bvt_W_cluster`). In
  particular, there are not yet any checked theorem-4-specific cluster rewrite
  lemmas in that file for the canonical integrand or translate factor: those
  rows remain planned adapter slots, even if they later consume generic
  imported comparison/limit machinery from
  `OSToWightmanBoundaryValuesComparison.lean` and
  `OSToWightmanBoundaryValueLimits.lean`. The theorem-4 one-factor transport
  package in `OSToWightmanPositivity.lean` likewise remains planned support
  work rather than checked-present named lemmas.
- theorem 4 should now be read through the following owner / consumes /
  exports / next-consumer ledger rather than from prose alone:

  | Slot | Ownership | Consumes | Exports | Next consumer |
  | --- | --- | --- | --- | --- |
  | `normalizedZeroDegreeRightVector` | `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | degree-`0` unit shell only | the literal positive-time Borchers vector concentrated in degree `0` with value `1` | `normalizedZeroDegreeRightVector_bound`, `..._funcs_zero`, `..._funcs_pos`, `conjTensorProduct_degreeZeroUnit_eq`, `osConjTensorProduct_degreeZeroUnit_eq`, `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`, then the right-single extraction lemmas |
  | `normalizedZeroDegreeRightVector_bound` / `..._funcs_zero` / `..._funcs_pos` | same file | `normalizedZeroDegreeRightVector` | the exact structural facts `bound = 0`, degree-`0` shell is the unit, and all positive-degree shells vanish | `conjTensorProduct_degreeZeroUnit_eq`, `osConjTensorProduct_degreeZeroUnit_eq`, `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`, `zeroDegree_right_single_wightman_extracts_factor`, `zeroDegree_right_single_os_extracts_factor`, `zero_degree_component_comparison_for_normalized_right_vector` |
  | `conjTensorProduct_degreeZeroUnit_eq` | same file | `normalizedZeroDegreeRightVector_funcs_zero` | the exact classical/Wightman degree-`0` normalization rewrite used before right-single extraction may fire | `zeroDegree_right_single_wightman_extracts_factor` |
  | `osConjTensorProduct_degreeZeroUnit_eq` | same file | `normalizedZeroDegreeRightVector_funcs_zero` | the exact classical/OS degree-`0` normalization rewrite used before right-single extraction may fire | `zeroDegree_right_single_os_extracts_factor` |
  | `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq` | same file | `normalizedZeroDegreeRightVector_funcs_zero` | the exact cast/zero-diagonal normalization rewrite needed to keep the degree-`0` unit shell explicit before theorem-4 transport packaging | `zeroDegree_right_single_wightman_extracts_factor`, `zeroDegree_right_single_os_extracts_factor`, `zero_degree_component_comparison_for_normalized_right_vector` |
  | `zeroDegree_right_single_wightman_extracts_factor` | same file | checked `OSReconstruction/Wightman/Reconstruction/Core.lean :: WightmanInnerProduct_right_single` plus `conjTensorProduct_degreeZeroUnit_eq`, `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`, and the normalized degree-`0` structural lemmas | extraction of the left Wightman factor against the normalized zero-degree right vector | `cluster_left_factor_transport` |
  | `zeroDegree_right_single_os_extracts_factor` | same file | checked `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean :: OSInnerProduct_right_single` plus `osConjTensorProduct_degreeZeroUnit_eq`, `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`, and the same structural lemmas | extraction of the left OS factor against the normalized zero-degree right vector | `cluster_left_factor_transport` |
  | `zero_degree_component_comparison_for_normalized_right_vector` | same file | corrected theorem-3 Section-4.3 transport package plus the normalized degree-`0` vanishing facts | the unique surviving `m = 0` transport comparison needed for theorem-4 factor extraction | `cluster_left_factor_transport`, `cluster_right_factor_transport` |
  | `cluster_left_factor_transport` | same file | literal Lean-order transcript only: first consume the already-packaged extraction pair `zeroDegree_right_single_wightman_extracts_factor` and `zeroDegree_right_single_os_extracts_factor` (so the checked suppliers `Core.lean:393 :: WightmanInnerProduct_right_single` and `SchwingerOS.lean:466 :: OSInnerProduct_right_single`, plus the normalization/cast-cleanup queue, are no longer visible here); second rewrite the theorem-3 Section-4.3 transport statement only through `zero_degree_component_comparison_for_normalized_right_vector`; third substitute the extracted left-factor identities into that surviving `m = 0` shell; fourth close with no new witness manufacture, scalar-normalization, or right-single algebra reopened at this row | corrected theorem-3-to-theorem-4 left one-factor transport equality | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` |
  | `cluster_right_factor_transport` | same file | the right-side analogue of `cluster_left_factor_transport`: reuse the same normalized degree-`0` witness package via the definitional alias `normalizedZeroDegreeLeftVector d := normalizedZeroDegreeRightVector d`, then consume the corresponding right-single Wightman/OS extraction rewrites together with `zero_degree_component_comparison_for_normalized_right_vector` to move the nontrivial shell to the second input without inventing a second normalization package | corrected theorem-3-to-theorem-4 right one-factor transport equality | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` |
  | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` | `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean` | literal base-file replacement transcript only: start from the checked anchors `:2214 :: ...singleSplitLargeSpatial`, `:2352 :: ...singleSplitSchwingerLargeSpatial`, and `:2514 :: ...singleSplitFactorComparison`; replace only the false same-shell factor-comparison input by `cluster_left_factor_transport` and `cluster_right_factor_transport`; keep the quantified eventual / ordered-positive-time shell otherwise unchanged; export exactly that repaired bridge under the new theorem name, with no canonical-direction rewrite or `BoundaryValueLimits.lean` transport allowed in this file | repaired positive-time single-split bridge with the same conclusion shape as the legacy `...singleSplitFactorComparison` theorem but without false same-shell hypotheses | `bvt_cluster_positiveTime_singleSplit_core` only |
  | `bvt_cluster_positiveTime_singleSplit_core` | same file | a one-step packaging wrapper consuming only `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`; it may restate the same ordered-positive-time / compact-support shell in the public form needed by the wrapper file, but it may not add canonical-direction rewrites, scalar-holomorphic transport, or any new cluster-factor algebra | the theorem-4 cluster statement on the ordered-positive-time / compact-support single-split shell, exported from the base file as the sole theorem allowed to enter the public adapter ladder | `canonical_cluster_integrand_eq_singleSplit_integrand` first; the later wrapper-file queue is then `canonical_translate_factor_eq_singleSplit_translate_factor -> singleSplit_core_rewrites_to_canonical_shell -> canonical_shell_limit_of_rewrite -> bvt_cluster_canonical_from_positiveTime_core` |
  | `canonical_cluster_integrand_eq_singleSplit_integrand` | `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean` | only the checked canonical-direction surfaces imported through `OSToWightmanBoundaryValuesComparison.lean` (`canonicalForwardConeDirection`, `canonicalForwardConeDirection_mem`) plus the repaired base-core shell statement exported by `bvt_cluster_positiveTime_singleSplit_core`; anti-drift owner rule: even though the checked sibling files `OSToWightmanBoundaryValuesEuclidean.lean` and `OSToWightmanBoundaryValuesCompactApprox.lean` exist in the live tree, they are not alternate homes for this slot under the current theorem-4 contract | the theorem-4-specific integrand rewrite from the public canonical shell to the repaired positive-time single-split shell; this row is kernel-only and may not hide any `a : SpacetimeDim d` to `a_sp : Fin d → ℝ` conversion | `singleSplit_core_rewrites_to_canonical_shell` |
  | `canonical_translate_factor_eq_singleSplit_translate_factor` | same file | only the checked translated-shell data already in scope (`translateSchwartzNPoint` together with the same canonical-direction surface) plus the translated-shell statement shape appearing in private `bvt_F_clusterCanonicalEventually_translate`; anti-drift owner rule: this slot, too, stays pinned to `OSToWightmanBoundaryValues.lean` rather than diffusing into the checked sibling files `OSToWightmanBoundaryValuesEuclidean.lean` / `OSToWightmanBoundaryValuesCompactApprox.lean` | the translated-right-factor rewrite needed to match the positive-time core surface exactly, before any limit transport is invoked; this is the unique row allowed to convert the frontier parameter `a : SpacetimeDim d` with side condition `a 0 = 0` into the base-shell spatial tail `a_sp := fun i => a (Fin.succ i)` used through `Fin.cons 0 a_sp` | `singleSplit_core_rewrites_to_canonical_shell` |
  | `singleSplit_core_rewrites_to_canonical_shell` | same file | `bvt_cluster_positiveTime_singleSplit_core`, `canonical_cluster_integrand_eq_singleSplit_integrand`, `canonical_translate_factor_eq_singleSplit_translate_factor` | rewrite/transport of the positive-time core theorem into the exact canonical-shell statement shape expected by private `bvt_F_clusterCanonicalEventually_translate`; this row must finish all shell-shape work before any limit theorem is touched, but it is binder/shell-neutral bookkeeping only and may not perform any residual `SpacetimeDim`/spatial-tail conversion, `Fin.cons` cleanup, or migrate part of the queue into the Euclidean/CompactApprox sibling files | `canonical_shell_limit_of_rewrite` |
  | `canonical_shell_limit_of_rewrite` | same file | `singleSplit_core_rewrites_to_canonical_shell` plus only the checked scalar-holomorphic / limit-transport package imported from `OSToWightmanBoundaryValueLimits.lean`, source-checked at `:260 :: bvt_singleSplit_xiShiftHolomorphicValue`, `:273 :: differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue`, `:290 :: bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`, `:314 :: bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`, `:350 :: tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`, `:446 :: tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`, `:494 :: eqOn_rightHalfPlane_of_ofReal_eq`, and `:536 :: bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`; its internal proof transcript is fixed as `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq` -> optional right-half-plane uniqueness only via `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` + `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq` -> final Wightman-target `t → 0+` transport only via `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`. The Schwinger-target theorems `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift` and `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger` are lower supplier legs only, `eqOn_rightHalfPlane_of_ofReal_eq` is uniqueness infrastructure only, and the deprecated bridge `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift` is forbidden on this lane. In particular this slot is a pure limit-transport theorem: it may not reopen the canonical integrand rewrite, the translated-factor rewrite, or the repaired base-bridge seam | transport from the rewritten shell statement to the eventual/limit form consumed immediately by `bvt_cluster_canonical_from_positiveTime_core` and then private `bvt_F_clusterCanonicalEventually_translate` | `bvt_cluster_canonical_from_positiveTime_core` |
  | `bvt_cluster_canonical_from_positiveTime_core` | same file | `canonical_shell_limit_of_rewrite` only | the full public theorem-4 canonical-shell adapter result, stated as the immediate input to the only checked downstream frontier shell in `OSToWightmanBoundaryValues.lean` (`:398 :: private bvt_F_clusterCanonicalEventually_translate`; downstream `:414 :: private bvt_F_clusterCanonicalEventually`, `:27 :: bv_cluster_transfer_of_canonical_eventually`, `:473 :: private bvt_W_cluster`) | `:398 :: private bvt_F_clusterCanonicalEventually_translate` only |

  Source-check note on the first extraction pair: the still-missing theorem-4
  slots `conjTensorProduct_degreeZeroUnit_eq`,
  `osConjTensorProduct_degreeZeroUnit_eq`,
  `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`,
  `zeroDegree_right_single_wightman_extracts_factor`, and
  `zeroDegree_right_single_os_extracts_factor` are all owned by
  `OSToWightmanPositivity.lean`, but the checked right-single supplier theorems
  they must consume already live elsewhere in the repo tree:
  `OSReconstruction/Wightman/Reconstruction/Core.lean ::
  WightmanInnerProduct_right_single` and
  `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean ::
  OSInnerProduct_right_single`. So the missing work is not just “apply the
  right-single theorem” but first normalize the degree-`0` shell into the exact
  classical / zero-diagonal shape those checked suppliers expect, then package
  the extracted factors. The current base-file cluster bridge already invokes
  the checked right-single surfaces, so theorem-4 implementation should be read
  as packaging above existing supplier theorems rather than rediscovering
  right-single identities inside the positivity file.

  Exact theorem-creation queue for the theorem-4 lane (freeze this literally
  unless compile reality forces a rename, in which case the docs must be
  updated at the same time):

  1. `OSToWightmanPositivity.lean`
     - `normalizedZeroDegreeRightVector`
     - `normalizedZeroDegreeRightVector_bound`
     - `normalizedZeroDegreeRightVector_funcs_zero`
     - `normalizedZeroDegreeRightVector_funcs_pos`
     - `conjTensorProduct_degreeZeroUnit_eq`
     - `osConjTensorProduct_degreeZeroUnit_eq`
     - `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`
     - `zeroDegree_right_single_wightman_extracts_factor`
     - `zeroDegree_right_single_os_extracts_factor`
     - `zero_degree_component_comparison_for_normalized_right_vector`
     - `cluster_left_factor_transport`
     - `cluster_right_factor_transport`
  2. `OSToWightmanBoundaryValuesBase.lean`
     - `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
     - `bvt_cluster_positiveTime_singleSplit_core`
  3. `OSToWightmanBoundaryValues.lean`
     - `canonical_cluster_integrand_eq_singleSplit_integrand`
     - `canonical_translate_factor_eq_singleSplit_translate_factor`
     - `singleSplit_core_rewrites_to_canonical_shell`
     - `canonical_shell_limit_of_rewrite`
     - `bvt_cluster_canonical_from_positiveTime_core`
  4. already-checked downstream consumer, with no new theorem-4 work hidden
     below it:
     - `OSToWightmanBoundaryValues.lean:398 :: private bvt_F_clusterCanonicalEventually_translate`

  Exact file-handoff contract for the base/adaptor seam:

  - The last theorem-4 slot allowed to mention the repaired one-factor transport
    pair is
    `OSToWightmanBoundaryValuesBase.lean ::
    bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`.
  - The only theorem-4 slot allowed to leave the base file is
    `OSToWightmanBoundaryValuesBase.lean ::
    bvt_cluster_positiveTime_singleSplit_core`.
  - The first theorem-4 slot allowed to live in the public wrapper file is
    `OSToWightmanBoundaryValues.lean ::
    canonical_cluster_integrand_eq_singleSplit_integrand`, and it is also the
    first direct consumer of `bvt_cluster_positiveTime_singleSplit_core`.
    `canonical_translate_factor_eq_singleSplit_translate_factor` is a sibling
    wrapper-file rewrite theorem used only after that handoff has already
    entered the public file; it is not a competing alternate first consumer of
    the base-file wrapper.
  - Therefore the public wrapper file has an explicit local transcript too:
    first `canonical_cluster_integrand_eq_singleSplit_integrand`, second
    `canonical_translate_factor_eq_singleSplit_translate_factor`, third
    `singleSplit_core_rewrites_to_canonical_shell`, fourth
    `canonical_shell_limit_of_rewrite`, fifth
    `bvt_cluster_canonical_from_positiveTime_core`, and only then the checked
    private frontier shell `:398 :: private
    bvt_F_clusterCanonicalEventually_translate`.
  - Therefore later Lean work may not bypass the handoff by feeding
    `cluster_left_factor_transport`, `cluster_right_factor_transport`, or the
    repaired bridge directly into `canonical_shell_limit_of_rewrite` or the
    private frontier theorem. The adapter lane must begin from
    `bvt_cluster_positiveTime_singleSplit_core` and rebuild the canonical shell
    statement in the exact order recorded above.
  - The shell conversion itself is now fixed against the checked theorem
    statements, not just against theorem names. The base-file export still ends
    on the positive-time single-split shell with analytic kernel
    `bvt_F OS lgc (n + m) (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I))`
    and test-function factor
    `f.osConjTensorProduct (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)`.
    The checked frontier theorem at
    `OSToWightmanBoundaryValues.lean:398 :: private
    bvt_F_clusterCanonicalEventually_translate` instead asks for the canonical
    shell with analytic kernel
    `bvt_F OS lgc (n + m) (fun k μ => ↑(x k μ) + t *
    ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)`
    and test-function factor
    `f.tensorProduct (translateSchwartzNPoint (d := d) a g)`.
    So the wrapper-file contract is literal: only
    `canonical_cluster_integrand_eq_singleSplit_integrand` may rewrite the
    analytic kernel; only
    `canonical_translate_factor_eq_singleSplit_translate_factor` may rewrite the
    translated factor; `singleSplit_core_rewrites_to_canonical_shell` must then
    keep the entire quantifier / eventual / norm shell fixed while composing
    exactly those two rewrites and applying
    `bvt_cluster_positiveTime_singleSplit_core`; and no residual shell
    conversion may remain for `canonical_shell_limit_of_rewrite` or the private
    frontier theorem.

  Implementation-size sanity check, so the task is not mentally compressed back
  into “one final cluster theorem”:

  - positivity-file normalization / extraction package:
    roughly `165-345` lines total,
  - base-file repaired bridge plus thin wrapper:
    roughly `40-85` lines total,
  - public canonical-shell adapter package:
    roughly `25-60` lines,
  - total theorem-4 documentation target: about `230-490` Lean lines, mostly
    bookkeeping / packaging rather than new continuation.
- anti-drift rule: `OSToWightmanBoundaryValueLimits.lean` is not the theorem-4
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
  `bvt_F_swapCanonical_pairing_of_adjacent_chain` before the first downstream
  consumer `OSToWightmanBoundaryValuesComparison.lean:1465 ::
  bv_local_commutativity_transfer_of_swap_pairing` and only then the final
  frontier theorem `OSToWightmanBoundaryValues.lean:351 ::
  bvt_F_swapCanonical_pairing`. The checked frontier file now fixes the final
  theorem-2 handoff transcript even more sharply: line `:725` closes the public
  locality theorem by exact application of
  `bv_local_commutativity_transfer_of_swap_pairing (d := d) n`, and line `:729`
  only packages that result through the private wrapper
  `bvt_F_swapCanonical_pairing (d := d) OS lgc n`. So the comparison theorem is
  the literal last substantive consumer after the canonical-swap package leaves
  `BoundaryValueLimits.lean`, not merely a planning-level bridge. Inside that
  canonical-shift sibling subsection the local execution order is now fixed
  too: the gluing theorem must call the adjacent raw-boundary theorem first,
  then apply canonical recovery on the swapped (`g`) side, then on the
  unswapped (`f`) side, and only then close by transitivity/symmetry; the
  adjacent-chain reducer may consume only that adjacent canonical theorem plus
  explicit factorization data for `swap i j`, not the raw-boundary or
  boundary-recovery theorems directly. More sharply, the reducer itself must be
  documented and later implemented in one fixed local order:
  factorization slot for the adjacent-transposition chain realizing `swap i j`
  -> test-function transport slot carrying the endpoint swap witness along that
  chain -> step-application slot using only
  `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
  step-by-step -> composition slot concatenating those equalities in chain
  order and rewriting the composed permutation back to `swap i j` -> export of
  the finished general-swap canonical pairing theorem. This removes the last
  implementation ambiguity about where the combinatorial permutation work ends
  and where theorem-2 locality theorems are allowed to re-enter.
  `OSToWightmanBoundaryValueLimits.lean` is the checked file locus for
  the canonical-shift / adjacent-chain part of that planned theorem-2 closure
  package, but the current tree still uses that file only for theorem-3 /
  `singleSplit_xiShift` limit machinery, so the theorem-2 subsection there is
  still missing support work rather than an already-present package to reuse.
  More sharply, that sibling subsection starts only after
  `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` is already available;
  it does not own the raw-boundary closure theorem itself. Those layers must
  not be hidden in one closing `sorry`, and the adjacent-chain reducer is not
  allowed to reopen `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`,
  `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`, or
  `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` inside its
  factorization or transport subproofs. Conversely, schematic pseudocode names
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
     `E0_tempered -> E0_linear -> E0_reality -> E3_symmetric -> constructSchwinger_translation_covariant_BHW -> constructSchwinger_translation_invariant -> constructSchwinger_rotation_covariant_BHW -> constructSchwinger_rotation_invariant -> E2_reflection_positive -> E4_cluster`
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
     `E4_cluster`.
   - executable late-field ledger for later Lean work (source-checked against
     `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean:2412,3545,3589`
     and `Wightman/Reconstruction/SchwingerOS.lean:792-804`):

     | Slot | Owner | Consumes | Exports | Next consumer |
     | --- | --- | --- | --- | --- |
     | `wickRotated_positiveTimeCore` | `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` | forward Section-4.3 transport/Hilbert positive-time data | Wick-rotated positive-time dense core | `wickRotatedBoundaryPairing_eq_transport_inner_on_core` |
     | `wickRotatedBoundaryPairing_eq_transport_inner_on_core` | same file | `wickRotated_positiveTimeCore` plus the forward Section-4.3 transport inner-product identity | reverse Euclidean pairing = forward transport inner product on the core | `wickRotatedBoundaryPairing_nonneg_on_core` |
     | `wickRotatedBoundaryPairing_nonneg_on_core` | same file | the core pairing identity plus forward positivity on the transport side | nonnegativity on the positive-time core | `wickRotated_positiveTimeCore_dense`, `wickRotatedBoundaryPairing_nonneg_by_density` |
     | `wickRotated_positiveTimeCore_dense` | same file | the chosen reverse positive-time core | density of that core in the ambient positive-time Euclidean test-function space | `wickRotatedBoundaryPairing_nonneg_by_density` |
     | `wickRotatedBoundaryPairing_nonneg_by_density` | same file | core nonnegativity plus core density | ambient positive-time reverse nonnegativity theorem | `constructSchwinger_positive` |
     | `constructSchwinger_positive` | reverse packaging layer targeting `Wightman/Reconstruction/SchwingerOS.lean:774` | ambient positive-time reverse nonnegativity theorem; no false OS=`Wightman` shortcut | exact field witness `OsterwalderSchraderAxioms.E2_reflection_positive` | final field packaging only |
     | `W_analytic_cluster_integral` | `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` | common-BHW/full-`SchwartzNPoint` cluster setup, with fixed proof transcript sector partition -> identity-sector ForwardTube step -> bad-sector permutation rewrites -> uniform `HasForwardTubeGrowth` majorant -> sectorwise dominated convergence -> finite sector sum | reverse Section-4.4 supplier estimate on the common-BHW/full-`SchwartzNPoint` side | `wickRotatedBoundaryPairing_cluster` |
     | `wickRotatedBoundaryPairing_cluster` | same file | `W_analytic_cluster_integral` | checked Wick-rotated full-`SchwartzNPoint` wrapper, still below any zero-diagonal field witness | `constructSchwinger_cluster_translate_adapter`, `constructSchwinger_cluster_tensor_adapter`, `constructSchwinger_cluster` |
     | `constructSchwinger_cluster_translate_adapter` | reverse packaging layer targeting `Wightman/Reconstruction/SchwingerOS.lean` | `g : ZeroDiagonalSchwartz d m` plus a spatial translation vector `a` | exact quantified witness `g_a : ZeroDiagonalSchwartz d m` required by `SchwingerOS.lean:802-804` | `constructSchwinger_cluster_tensor_adapter`, `constructSchwinger_cluster` |
     | `constructSchwinger_cluster_tensor_adapter` | same reverse packaging layer | `f : ZeroDiagonalSchwartz d n` plus the translated witness `g_a` | exact `(n+m)`-point witness `fg_a : ZeroDiagonalSchwartz d (n + m)` with the literal pointwise tensor formula required by `SchwingerOS.lean:804-807` | `constructSchwinger_cluster` |
     | `constructSchwinger_cluster` | same reverse packaging layer, final target `Wightman/Reconstruction/SchwingerOS.lean:792` | `wickRotatedBoundaryPairing_cluster` plus the manufactured witnesses `g_a` and `fg_a`; no black-box tensor-restriction shortcut | literal norm inequality demanded by `OsterwalderSchraderAxioms.E4_cluster` | final field packaging only |
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
   - downstream-consumer contract only: it may first consume the finished
     `WightmanQFT` surface exported after the checked GNS queue
     `GNSHilbertSpace.lean :1005 -> :1062 -> :1249 -> :1643 -> :2114`, and
     then close at `Main.lean :74`; it is not allowed to become a second home
     for spectrum-bridge, nuclear-bridge, or cyclicity work
   - source-checked file-ownership clarification for this clone: the live tree
     contains no separate `Wightman/Reconstruction/Main/*` or other Main-side
     uniqueness support module, and `Main.lean` itself currently contains only
     the checked declarations `wightman_reconstruction` and
     `:74 :: wightman_uniqueness`. So every earlier uniqueness item is still a
     documentation-owned theorem slot rather than a checked Lean declaration.
     The exact downstream queue is
     `cyclicWordVector/cyclicWordSpan -> cyclicWordVector_inner_cyclicWordVector
     -> uniquenessPreMap -> uniquenessPreMap_inner_formula ->
     uniquenessPreMap_null_of_null -> uniquenessDenseMap ->
     uniquenessDenseMap_inner_preserving ->
     uniquenessDenseMap_norm_preserving -> uniquenessDenseMap_isometry ->
     cyclicWord_in_range_of_uniquenessDenseMap ->
     cyclicWordSpan_le_range_uniquenessDenseMap ->
     uniquenessDenseMap_denseRange ->
     uniquenessDenseMap_extends_to_unitary ->
     uniquenessUnitary_maps_vacuum ->
     uniquenessUnitary_intertwines_field_on_cyclic_core ->
     cyclicWordSpan_is_field_core -> uniquenessUnitary_intertwines_field ->
     wightman_uniqueness`, and later Lean work must interpret that queue as a
     file-creation contract: either create those declarations in that order as
     one contiguous Main-side block in `Main.lean` before the closing theorem,
     or first introduce one explicitly named helper module under
     `Wightman/Reconstruction/` and move a contiguous uniqueness block there
     with the ownership docs/imports updated in the same pass. It is out of
     contract to scatter the queue across unrelated existing reconstruction
     files while still treating the uniqueness lane as having a single hidden
     owner. It is also out of contract to act as if names like
     `uniquenessPreMap`, `uniquenessDenseMap_inner_preserving`, or
     `uniquenessDenseMap` already exist somewhere in the checked tree.
     First-consumer boundaries are part of
     the contract too: `cyclicWordVector_inner_cyclicWordVector` is the only
     matrix-element slot; quotient/null descent ends at
     `uniquenessPreMap_null_of_null`; descended inner/norm preservation starts
     only after `uniquenessDenseMap` exists; dense-range work starts only at
     `cyclicWord_in_range_of_uniquenessDenseMap ->
     cyclicWordSpan_le_range_uniquenessDenseMap`; field-core closure starts
     only at `cyclicWordSpan_is_field_core`; and `Main.lean:74` is
     assembly-only.
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
   - public covariance work is also **not** owned by this lane. The checked
     execution queue is instead:
     `Wightman/Groups/{Lorentz,Poincare}.lean`
     -> `Bridge/AxiomBridge.lean :: lorentzGroupToWightman / wightmanToLorentzGroup`
     -> the specific public consumer file, with no detour through local
     `RestrictedLorentzGroup` aliases unless the task is explicitly internal
     connectedness/BHW geometry;
   - concretely, later Lean work should enter the consumer lane by theorem
     surface, not by vague subsystem name:
     * forward-tube/BHW covariance transport:
       `ForwardTubeLorentz.lean :: lorentz_covariant_distributional_bv`
     * final OS→W covariance wrapper queue:
       `OSToWightmanBoundaryValues.lean :: bvt_lorentz_covariant_restricted -> bvt_lorentz_covariant -> constructWightmanFunctions`
     * reverse E1 split queue:
       `SchwingerAxioms.lean :: F_ext_translation_invariant -> wickRotatedBoundaryPairing_translation_invariant`
       and
       `SchwingerAxioms.lean :: F_ext_rotation_invariant -> wickRotatedBoundaryPairing_rotation_invariant`;
   - any future pass that reprioritizes this lane must preserve both ownership
     boundaries instead of reopening theorem-2 raw-boundary packaging or the
     public covariance migration under the permutation-flow banner

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
     checked frontier shell `OSToWightmanBoundaryValues.lean:398 :: private
     bvt_F_clusterCanonicalEventually_translate`; the boundary is literal and
     exclusive: `canonical_shell_limit_of_rewrite`
     -> `bvt_cluster_canonical_from_positiveTime_core`
     -> `:398 :: private bvt_F_clusterCanonicalEventually_translate`;
   - only then close the remaining transfer chain and `bvt_cluster` in
     `OSToWightmanBoundaryValues.lean`.
5. In parallel or next, attack the live R -> E theorem-level front:
   - `SchwingerTemperedness.lean`: coincidence-singularity / zero-diagonal continuity
   - `SchwingerAxioms.lean`: Euclidean reality, OS=W term, and cluster
   - keep `isPreconnected_baseFiber` in `BHWTranslation.lean` as an old-route residual,
     not as the merged-path blocker
6. Finish the remaining downstream GNS/uniqueness closure in strict owner order:
   - `GNSHilbertSpace.lean :1005 :: continuous_translate_npoint_schwartz`
   - `:1062 :: gns_stronglyContinuous_preHilbert`
   - `:1249 :: gns_matrix_coefficient_holomorphic_axiom`
   - downstream nuclear bridge through the exported `WightmanAxioms.lean` surfaces
   - `:1643 :: gns_cyclicity`
   - `:2114 :: gnsQFT`
   - `Main.lean :74 :: wightman_uniqueness`
   together with any residual `WightmanAxioms` blockers. This step is no longer
   allowed to be summarized as generic "final wiring" because the ownership
   boundary between GNS packages and uniqueness is part of the implementation
   contract. Source-checked file ownership is part of that contract too: the
   live tree has checked support files under `Wightman/NuclearSpaces/*`
   (including `Helpers/PositiveDefiniteKernels.lean` and
   `NuclearOperator.lean`) but no parallel checked Main-side uniqueness helper
   file, so later Lean work may not pretend there is a hidden `Main` support
   package waiting below `:74`. Until such a file is actually added, the Main
   lane must be read as `Main.lean :74` plus the documentation-owned helper
   queue mirrored from `docs/wightman_uniqueness_blueprint.md`. In particular,
   once the queue reaches `Main.lean`, the later Lean transcript must stay
   entirely on the uniqueness lane and preserve the full strict suborder:
   `cyclicWordVector/cyclicWordSpan`
   -> `cyclicWordVector_inner_cyclicWordVector`
   -> `uniquenessPreMap`
   -> `uniquenessPreMap_inner_formula`
   -> `uniquenessPreMap_null_of_null`
   -> `uniquenessDenseMap`
   -> `uniquenessDenseMap_inner_preserving`
   -> `uniquenessDenseMap_norm_preserving`
   -> `uniquenessDenseMap_isometry`
   -> `cyclicWord_in_range_of_uniquenessDenseMap`
   -> `cyclicWordSpan_le_range_uniquenessDenseMap`
   -> `uniquenessDenseMap_denseRange`
   -> `uniquenessDenseMap_extends_to_unitary`
   -> `uniquenessUnitary_maps_vacuum`
   -> `uniquenessUnitary_intertwines_field_on_cyclic_core`
   -> `cyclicWordSpan_is_field_core`
   -> `uniquenessUnitary_intertwines_field`
   -> `wightman_uniqueness`,
   with no reopening of the spectrum bridge, nuclear bridge, or cyclicity
   packaging after `gnsQFT` is exported. Read that queue as a theorem-surface
   contract, not merely a checklist: `cyclicWordVector_inner_cyclicWordVector`
   is the only matrix-element slot; `uniquenessPreMap_inner_formula` may
   consume only that formula plus the equality hypothesis `h` and is the only
   transfer row before quotient descent; `uniquenessPreMap_null_of_null` is the
   sole quotient/null seam; `uniquenessDenseMap_inner_preserving` and
   `uniquenessDenseMap_norm_preserving` begin only after the descended map
   exists; `uniquenessDenseMap_isometry` packages metric data only and may not
   begin dense-range work; dense range begins only at
   `cyclicWord_in_range_of_uniquenessDenseMap -> cyclicWordSpan_le_range_uniquenessDenseMap`;
   field-core closure begins only at `cyclicWordSpan_is_field_core`; and the
   final theorem is assembly-only. This queue is not merely descriptive:
   because the live checked tree still has no Main-side helper module, these
   rows are also the explicit order in which new Main-side declarations must be
   created unless ownership is first moved into one newly added, explicitly
   named support file. They are not licensed to diffuse piecemeal into
   unrelated existing `Wightman/Reconstruction/*.lean` files.

## 6. Deprioritized Work (Unless It Unblocks the Above)

1. Most of `vNA/*`
2. Historical/planned nuclear-space side development beyond the currently
   checked `Wightman/WightmanAxioms.lean` axiom surfaces
   - checked-tree / census correction (2026-04-10): the headline repo census in
     this plan is now the actual whole-project direct-hole count `60`, not the
     older `63`/"tracked tree excludes NuclearSpaces" convention used in some
     older overview notes. Later overview docs should therefore treat the
     `Wightman/NuclearSpaces/*` lane as part of the live project-wide `Wightman`
     bucket unless they explicitly announce a narrower auxiliary policy.
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
