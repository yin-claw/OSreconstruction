# Proof-Docs Completion Plan

Purpose: this note is the execution plan for bringing the proof-document stack
to the standard

> "Lean implementation should require proving the named packages, not
> rediscovering the mathematics, changing theorem surfaces, or making new route
> choices."

This is a documentation-only plan. It does **not** authorize production Lean
deviation from the existing blueprints.

This note should be read together with:

- `docs/sorry_triage.md`
- `docs/mathlib_gap_analysis.md`
- `docs/theorem2_locality_blueprint.md`
- `docs/theorem3_os_route_blueprint.md`
- `docs/theorem4_cluster_blueprint.md`
- `docs/general_k_continuation_blueprint.md`
- `docs/scv_infrastructure_blueprint.md`
- `docs/gns_pipeline_blueprint.md`
- `docs/nuclear_spaces_blueprint.md`
- `docs/vna_infrastructure_blueprint.md`

## 1. What "100% implementation-ready" means

A proof doc counts as complete only when all of the following are true.

1. The theorem route is unique.
   There is one endorsed theorem path, and alternate routes are either deleted
   or explicitly quarantined.
2. The theorem surfaces are fixed.
   The named theorem packages are part of the implementation contract, not loose
   suggestions.
3. The helper-theorem packaging is fixed.
   If the later Lean code is allowed a packaging convenience, the exact allowed
   form is documented.
4. The proof transcript is explicit.
   The doc says which theorem is proved first, which theorem consumes it next,
   and how the proof moves mathematically from one to the next.
5. Existing repo consumers are named exactly.
   The doc does not say "use existing infrastructure"; it says which theorem
   names are consumed.
6. Representation constraints are explicit.
   If the current Lean encoding differs from the paper-level language, the doc
   says exactly how the implementation should adapt without changing the route.
7. Historical alternatives are fenced off.
   Earlier false routes, wrapper-heavy routes, or broader theorem surfaces are
   marked as forbidden rather than left as optional memory.
7a. The OS I / OS II split is explicit wherever relevant.
   If a theorem shape comes from OS I but its analytic input must be repaired by
   OS II because of the broken Lemma 8.8 route, the doc says so explicitly
   rather than leaving that dependency implicit.
8. Exit criteria are checkable.
   The doc can be audited by search for unresolved wording and by theorem-name
   cross-checks.

## 2. Global completion protocol

Every proof-doc completion pass should follow this order.

1. Search for tentative wording:
   - `candidate`
   - `if needed`
   - `if easiest`
   - `may shift`
   - `placeholder`
   - `future theorem slot`
   - `fallback`
   - `later Lean`
2. Classify each hit as:
   - acceptable implementation commentary,
   - harmless historical note,
   - or a real mathematical/documentation gap.
3. For every real gap:
   - fix the route,
   - fix the theorem names,
   - fix the proof-package order,
   - update the global triage docs.
4. Re-audit the nearest downstream and upstream docs so the fix does not leave
   inconsistent language elsewhere.
5. Record any production-relevant doc change in `agents_chat.md` append-only.

## 3. Completion order for the remaining docs

The remaining hardening work should proceed in this order.

### Phase A. Active OS-route frontiers

These are the highest-priority docs because Claude’s production work depends on
them directly.

1. `docs/theorem3_os_route_blueprint.md`
2. `docs/theorem2_locality_blueprint.md`
3. `docs/theorem4_cluster_blueprint.md`
4. `docs/sorry_triage.md`
5. `docs/mathlib_gap_analysis.md`

Completion criterion for Phase A:

1. theorem 2/3/4 each have exactly one endorsed route;
2. each package theorem has a fixed name;
3. each doc explicitly identifies which existing production theorems are
   consumers and which new theorem packages are still missing;
4. each active OS-route doc states explicitly whether it is using:
   - sound OS I theorem shape only,
   - repaired OS II continuation/growth input,
   - or both;
5. no route-level wording still allows fallback to discarded shells, K2
   wrappers, or raw-topology restarts.

### Phase B. Core analysis support

These docs control the mathematical suppliers for theorem 2/3 and general `k`.

1. `docs/scv_infrastructure_blueprint.md`
2. `docs/nuclear_spaces_blueprint.md`
3. `docs/general_k_continuation_blueprint.md`
4. `docs/os1_detailed_proof_audit.md`
5. `docs/os2_detailed_proof_audit.md`

Checked-tree clarification for this phase:
- in the current clone, `docs/nuclear_spaces_blueprint.md` is a contract for a
  lane that already has checked support files under
  `OSReconstruction/Wightman/NuclearSpaces/`;
- a direct checked-tree scan currently shows **7** local `sorry`s there
  (`NuclearSpace.lean`: 2, `BochnerMinlos.lean`: 5), but the repo-wide
  headline `63`-sorry census intentionally excludes that secondary lane so the
  active theorem-2/3/4 ledger stays stable;
- Phase-B hardening must therefore keep three layers separate:
  1. checked downstream axiom surfaces in `Wightman/WightmanAxioms.lean`
     (`schwartz_nuclear_extension`,
     `exists_continuousMultilinear_ofSeparatelyContinuous`),
  2. checked local support files under `Wightman/NuclearSpaces/*`, and
  3. any still-planned import/integration wrappers needed to connect the local
     support lane to the downstream reconstruction consumers;
- any pass that reassigns theorem-package ownership between those layers or
  changes whether the NuclearSpaces lane remains outside the headline census
  must update the phase description and downstream file-ownership notes in the
  same pass.

Completion criterion for Phase B:

1. every SCV supplier is broken into theorem packages rather than invoked as
   "SCV machinery";
2. the nuclear-space doc has one endorsed route and a blocked-only fallback,
   while also marking which theorem surfaces are already checked in
   `Wightman/NuclearSpaces/*`, which are only exported downstream through
   `Wightman/WightmanAxioms.lean`, which remain genuinely planned/open, and
   whether the live local-NuclearSpaces sorrys are being counted inside or
   outside the repo-wide headline census policy;
3. the general-`k` doc fixes file boundaries, theorem slots, indexing, and SCV
   imports before implementation;
4. OS I / OS II audit docs point to exact local theorem-package suppliers and
   no longer leave hidden paper steps implicit.

### Phase C. Downstream reconstruction side lanes

These docs should be hardened after Phases A-B because they consume A-B.

1. `docs/gns_pipeline_blueprint.md`
2. `docs/wightman_uniqueness_blueprint.md`
3. `docs/r_to_e_blueprint.md`
4. `docs/bhw_permutation_blueprint.md`

Completion criterion for Phase C:

1. no theorem surface is still described as "should be possible once...";
2. SCV/nuclear inputs are named exactly;
3. no reverse-direction positivity argument quietly reuses a forward theorem;
4. uniqueness and permutation packages state exact dependency order.

### Phase D. Operator-algebra side backlog

These should be documented precisely, but remain lower priority than A-C.

1. `docs/vna_infrastructure_blueprint.md`
2. `docs/vna_triage.md`

Completion criterion for Phase D:

1. the Stone/spectral route is fixed at the theorem-package level;
2. predual/KMS/modular packages no longer blur foundational and consumer layers;
3. the first theorem to implement in each file is fixed.

## 4. File-by-file acceptance criteria

## 4.1. `theorem3_os_route_blueprint.md`

This doc is complete only when:

1. Package A through Package I each have fixed theorem names;
2. Package C is explicitly marked as false legacy infrastructure, not as a live
   theorem with an active proof strategy;
3. Package I is stated on the corrected Section 4.3 transformed-image theorem
   surface, with the transport codomain on the Section-4.3 half-space
   Schwartz side rather than either
   a support restriction `tsupport ⊆ PositiveEnergyRegion` or a false
   `DenseRange` claim in full `SchwartzNPoint d n`;
4. Package I has concrete theorem slots for the explicit `(4.19)`-`(4.20)`
   test-function transform, the transformed image, the quotient-side
   paper-faithfulness dense-range theorem
   `denseRange_section43PositiveEnergyQuotientMap` (and its 1D precursor)
   kept separate from the live positivity closure route, the kernel-zero
   theorems `os1TransportOneVar_eq_zero_iff` and
   `os1TransportComponent_eq_zero_iff` consumed by the on-image
   well-definedness proof, the transport map on that image, the concrete
   Lemma-4.2 adapter `lemma42_matrix_element_time_interchange`, the quadratic
   identity there, and the final public closure theorem.
   The completion standard here is not merely "name the support file" but
   "freeze the Lean execution order above that file so later implementation
   does not have to guess where the one-variable stage ends, where the
   on-image well-definedness proof becomes the explicit theorem slot
   `bvt_transport_to_osHilbert_onImage_wellDefined`, where that slot consumes
   kernel-zero, or where the Lemma-4.2 interchange adapter first enters the
   quadratic-identity stage".
   The required Package-I acceptance ledger is:

   | Slot | Ownership | Consumes | Exports | Next consumer |
   | --- | --- | --- | --- | --- |
   | checked branch-`3b` SCV foothold | `OSReconstruction/SCV/PartialFourierSpatial.lean` | existing SCV/Schwartz infrastructure already in that file | `partialFourierSpatial_fun`, `partialFourierSpatial_timeSliceSchwartz`, `partialFourierSpatial_timeSlice_hasPaleyWienerExtension`, `partialFourierSpatial_timeSliceCanonicalExtension` | `os1TransportOneVar` |
   | `os1TransportOneVar` | `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | theorem-3 `singleSplit_xiShift` support route plus the checked SCV supplier chain above; first-consumer restriction: the checked scalar anchors `identity_theorem_right_halfplane` (`OSToWightmanPositivity.lean:48`) and `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` (`:110`) may first enter only on this Stage-A slot | one-variable Section-4.3 transport map on the corrected half-space codomain | `os1TransportOneVar_eq_zero_iff`, `os1TransportComponent` |
   | `os1TransportOneVar_eq_zero_iff` | same file | `os1TransportOneVar` together with the positive-half-line boundary-value uniqueness input; the same checked `:48` / `:110` scalar suppliers may be reused here and no later theorem-3 slot may consume them except through the exported Stage-A package | one-variable kernel-zero theorem | `os1TransportComponent`, `bvt_transport_to_osHilbert_onImage_wellDefined` |
   | `os1TransportComponent` | same file | `os1TransportOneVar`, `os1TransportOneVar_eq_zero_iff`, and the explicit Section-4.3 Fourier-Laplace transport formula `(4.19)`-`(4.20)` | degreewise transformed-image transport map | `os1TransportComponent_eq_zero_iff`, `BvtTransportImageSequence` |
   | `os1TransportComponent_eq_zero_iff` | same file | `os1TransportComponent` | degreewise kernel-zero theorem | `BvtTransportImageSequence`, `bvt_transport_to_osHilbert_onImage_wellDefined` |
   | `BvtTransportImageSequence` | same file | `os1TransportComponent` | transformed-image core object carried into the on-image Hilbert transport stage and only later reused inside the quadratic identity | `bvt_transport_to_osHilbert_onImage_wellDefined` only; no theorem may jump directly from this row to the quadratic identity without first passing through the transport-map stage |
   | `bvt_transport_to_osHilbert_onImage_wellDefined` | same file | `BvtTransportImageSequence`, degreewise preimage choice, `os1TransportOneVar_eq_zero_iff`, and `os1TransportComponent_eq_zero_iff` | proof that the OS-Hilbert transport value is independent of the chosen transformed-image preimage | `bvt_transport_to_osHilbert_onImage` |
   | `bvt_transport_to_osHilbert_onImage` | same file | `BvtTransportImageSequence`, `bvt_transport_to_osHilbert_onImage_wellDefined`, and the checked general Hilbert-target package `positiveTimeBorchersVector` with first equality surfaces `positiveTimeBorchersVector_inner_eq` / `positiveTimeBorchersVector_norm_sq_eq`; first-consumer restriction: this general target/equality package first enters here, not earlier in Stage A/B, while `euclideanPositiveTimeSingleVector` / `euclideanPositiveTimeSingleVector_norm_sq_eq` are later single-component specializations rather than the primitive Stage-C target | OS Hilbert-space transport map on transformed-image data | `lemma42_matrix_element_time_interchange` first, then `bvt_wightmanInner_eq_transport_norm_sq_onImage`; the transformed-image core may re-enter the quadratic identity only through this transport-map stage |
   | `lemma42_matrix_element_time_interchange` | same file | `bvt_transport_to_osHilbert_onImage`, transformed-image data, and the repaired OS-II-backed `bvt_F` / `bvt_W` continuation kernel | explicit Lemma-4.2 matrix-element interchange seam | `bvt_wightmanInner_eq_transport_norm_sq_onImage` |
   | `bvt_wightmanInner_eq_transport_norm_sq_onImage` | same file | `bvt_transport_to_osHilbert_onImage_wellDefined` to freeze one representative family first, then `bvt_transport_to_osHilbert_onImage`, then `lemma42_matrix_element_time_interchange`, and only then the repaired OS-II-backed `bvt_F` / `bvt_W` kernel route together with norm-square recognition via the checked general equality `positiveTimeBorchersVector_norm_sq_eq` on the actual transport target | on-image quadratic identity | `bvt_W_positive_of_transportImage_density` |
   | `bvt_W_positive_of_transportImage_density` | same file | on-image quadratic identity plus the checked Hilbert-density support `positiveTimeBorchersVector_dense`; first-consumer restriction: this checked density supplier first enters here rather than in an earlier transport theorem | implementation-side positivity closure theorem | `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean :: bvt_W_positive` |

   Any doc counted as “complete” for theorem 3 must preserve that exact owner /
   consumes / exports / next-consumer order, rather than merely repeating the
   theorem names in a checklist or prose paragraph. In particular, the Stage-C
   quadratic-identity row is not allowed to stop at “after Lemma 4.2”; it must
   say that norm recognition happens on the checked general transport target via
   `positiveTimeBorchersVector_norm_sq_eq`, not by a hidden single-component
   shortcut.
5. the doc explicitly distinguishes the exported wrapper theorem
   `OSToWightmanBoundaryValues.lean :: bvt_W_positive` from the actual
   checked implementation/support locus in `OSToWightmanPositivity.lean`.
   A source check against the live tree should now read that file as exposing
   the landed support surfaces with exact anchors
   `identity_theorem_right_halfplane` (`:48`),
   `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` (`:110`),
   `positiveTimeBorchersVector` (`:1461`) together with the first checked
   equalities `positiveTimeBorchersVector_inner_eq` (`:1467`) and
   `positiveTimeBorchersVector_norm_sq_eq` (`:1480`), then the final-closure
   density supplier `positiveTimeBorchersVector_dense` (`:1506`), and only
   downstream of the transport-map theorem the later single-component
   specialization `euclideanPositiveTimeSingleVector` (`:1523`) with norm
   supplier `euclideanPositiveTimeSingleVector_norm_sq_eq` (`:1530`).
   The completion standard is stronger than naming those theorems: the doc must
   also say which planned Section-4.3 slots are first allowed to consume them.
   Concretely, the scalar pair `:48` / `:110` must be frozen as Stage-A-only
   input consumed first by `os1TransportOneVar` and then
   `os1TransportOneVar_eq_zero_iff`; the vector/norm package first enters at
   `bvt_transport_to_osHilbert_onImage`; and the density package first enters
   only at `bvt_W_positive_of_transportImage_density`. The fully split
   Section-4.3 transport/closure theorem names remain planned
   theorem-slot targets rather than already-landed production theorem names;
6. any surviving mention of Packages F/G/H is clearly marked as withdrawn /
   historical, not endorsed implementation guidance;
7. the exact legacy-consumer status after Package C is named;
8. the branch-`3b` support route is fixed at the concrete checked-present
   `OSReconstruction/SCV/PartialFourierSpatial.lean` companion-file level
   rather than the withdrawn abstract Schwartz-helper route;
   the blueprint must name its live supplier surfaces explicitly — at minimum
   the coordinate reshuffle `nPointTimeSpatialCLE`, the Fourier/time-slice
   chain
   `partialFourierSpatial_fun`
   -> `partialFourierSpatial_timeSliceSchwartz`
   -> `partialFourierSpatial_timeSlice_hasPaleyWienerExtension`
   -> `partialFourierSpatial_timeSliceCanonicalExtension`,
   and the already-landed continuity / derivative transport theorems there —
   and must say that the remaining theorem-3 gap is the Section-4.3 packaging
   above those suppliers, not discovery of a missing support file;
9. the blueprint records the exact checked repo-relative theorem-3 production
   file inventory (`.../OSToWightmanPositivity.lean`,
   `.../OSToWightmanBoundaryValues*.lean`,
   `.../OSToWightmanSemigroup.lean`,
   `.../OSToWightmanSpatialMomentum.lean`,
   `Wightman/Reconstruction/SchwingerOS.lean`) so shortened filenames cannot
   be misread as different implementation loci;
10. the support-work checklist is satisfied literally;
11. the blueprint does not reintroduce a separate active theorem slot
    `bvtTransportImage_dense`: Hilbert-space closure is the live production
    route, while the quotient-side dense-range theorems
    `denseRange_section43PositiveEnergyQuotientMap` and
    `denseRange_section43PositiveEnergyQuotientMap1D` remain only
    paper-faithfulness results on the corrected half-space codomain and are
    not allowed to masquerade as the live positivity-closing step.

## 4.2. `theorem2_locality_blueprint.md`

This doc is complete only when:

1. the continuity route is fixed on the flattened regular representation;
2. Route B is fixed as the primary geometry route;
3. Route A is documented as blocked-only fallback;
4. ET-support and open-edge theorem slots are fully named;
5. the adjacent-only raw-boundary theorem, the adjacent canonical-shift
   adapter, and the final general-swap reduction are split into separate
   theorem packages with explicit consumption order;
6. the blueprint records the exact checked repo-relative theorem-2 production
   file inventory (`.../OSToWightmanBoundaryValues.lean`,
   `.../OSToWightmanBoundaryValuesBase.lean`,
   `.../OSToWightmanBoundaryValuesComparison.lean`,
   `.../OSToWightmanBoundaryValueLimits.lean`,
   `Wightman/Reconstruction/ForwardTubeDistributions.lean`,
   `.../BHWExtension.lean`,
   `Wightman/Reconstruction/AnalyticContinuation.lean`,
   `ComplexLieGroups/JostPoints.lean`,
   `ComplexLieGroups/Connectedness/BHWPermutation.lean`,
   `ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean`, and
   `ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean`),
   together with the checked umbrella-vs-subfile split for the BHW-permutation
   lane and the explicit `Adjacency.lean` vs
   `AdjacencyDistributional.lean` ownership split, so locality work cannot
   drift into the wrong file layer or collapse the continuity supplier and
   canonical-shift adapter back into one vague closing step;
6a. the blueprint includes a compact slot ledger for the live Route-B theorem-2
   package, and for each missing theorem slot it fixes four things explicitly:
   file ownership, exact checked theorem surfaces consumed, exact output
   theorem surface exported, and the next allowed downstream consumer;
7. no section still treats continuity or geometry as abstract "candidate"
   choices;
8. the raw-boundary locality route is fixed at the adjacent-only substitute
   consumer theorem
   `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`, with
   statement/export ownership in `BHWExtension.lean` and any lower helper
   lemmas in `AdjacencyDistributional.lean`; the theorem-2 docs must no longer
   describe the checked public wrapper `W_analytic_swap_boundary_pairing_eq` as
   the actual closure theorem on `W := bvt_W OS lgc`.
8b. the blueprint must also record the checked theorem-surface mismatch that
   forces that choice: both `W_analytic_swap_boundary_pairing_eq` and the lower
   ET-support theorem
   `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity` ask for a
   global `IsLocallyCommutativeWeak d W` input, so neither is directly the
   theorem-2 raw-boundary closure theorem on `W := bvt_W OS lgc`. After source
   checking the surrounding live theorem surfaces, the endorsed theorem-2 route
   is therefore the adjacent-only one: `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`
   must be documented as a consumer of the explicitly named substitute theorem
   `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`, whose proof
   transcript is frozen as
   pointwise `analytic_boundary_local_commutativity_of_boundary_continuous`
   on the chosen Route-B edge -> integrand equality on compact support ->
   pairing equality by integral congruence. `W_analytic_swap_boundary_pairing_eq`
   and `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`
   remain checked-present downstream/lower comparison surfaces, not competing
   theorem-2 endgames. The docs may no longer leave open a second endorsed
   route that first proves the stronger full-global theorem
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)`;
8a. the blueprint explicitly separates checked-present theorem surfaces from
   checked-missing planned theorem-package names, so later Lean work cannot
   mistake doc-introduced names like
   `choose_real_open_edge_for_adjacent_swap`,
   `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`,
   `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`, or
   `bvt_F_swapCanonical_pairing_of_adjacent_chain` for already existing
   helpers somewhere else in the repo tree;
9. the theorem-2 proof transcript does not silently switch back to Route A in
   its endgame pseudocode: the raw-boundary instantiation must be written on
   the primary Route-B open-edge package
   (`choose_real_open_edge_for_adjacent_swap` ->
   `swapped_support_lies_in_swapped_open_edge` ->
   `swapped_open_edge_embeds_in_extendedTube`) before the final
   canonical-shift adapter;
10. the theorem-2 blueprint fixes not only the theorem-slot names but also the
   intended file ownership of those slots: Route-B ET-support geometry in the
   checked BHW-permutation support subfile layer (not the umbrella
   `BHWPermutation.lean` by default), the raw-boundary wrapper in the
   BHW-extension layer, the canonical-shift adapter and the general-swap
   adjacent-chain reducer in `OSToWightmanBoundaryValueLimits.lean`, and the
   frontier theorem in `OSToWightmanBoundaryValues.lean` as a thin consumer
   rather than a catch-all closure file. The blueprint must also keep explicit
   that `OSToWightmanBoundaryValueLimits.lean` is a checked existing file whose
   current contents are still theorem-3-side `singleSplit_xiShift` limit
   machinery only, so the theorem-2 canonical-direction package there is new
   missing support work in a sibling subsection, not a reinterpretation of the
   existing positivity shell;
10a. that sibling-subsection contract must itself be explicit at proof-
   transcript level: the theorem-2 package in
   `OSToWightmanBoundaryValueLimits.lean` must run in the local order
   `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
   -> `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
   -> `bvt_F_swapCanonical_pairing_of_adjacent_chain`, with the first theorem
   documented as a direct specialization of
   `boundary_value_recovery_forwardTube_of_flatRegular_from_bv` at
   `bvt_W`, `bvt_W_continuous`, `bvt_boundary_values`, and
   `canonicalForwardConeDirection`, and the second theorem documented as the
   named adjacent raw-boundary equality
   `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` plus that
   specialization on the `g` side and the `f` side. If that file-local
   transcript is not fixed, theorem 2 is still not
   implementation-ready;
11. the theorem-2 blueprint fixes one unique proof transcript order:
   `choose_real_open_edge_for_adjacent_swap`
   -> `swapped_support_lies_in_swapped_open_edge`
   -> `swapped_open_edge_embeds_in_extendedTube`
   -> `bvt_F_hasFlatRegularRepr`
   -> `bvt_F_boundary_continuous_at_real_support`
   -> `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`
   -> `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
   -> `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
   -> `bvt_F_swapCanonical_pairing_of_adjacent_chain`
   -> `bvt_F_swapCanonical_pairing`,
   with the adjacent-only/raw-boundary versus general-swap frontier mismatch
   documented explicitly rather than hidden in the closing `sorry`, and with
   any forward-Jost upgrade route treated only as blocked fallback unless a
   checked production theorem first makes it available. In particular, the
   theorem-2 pseudocode may not call the adjacent-only theorem surfaces
   `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` or
   `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` directly on
   arbitrary `swap i j` data; the general frontier must pass through the
   separate adjacent-chain reducer `bvt_F_swapCanonical_pairing_of_adjacent_chain`;
12. later sections of the theorem-2 blueprint may introduce subordinate local
   cover / compactness helper lemmas, but they must not silently rename the
   contract-level Route-B theorem slots or introduce a second competing
   top-level geometry vocabulary. More sharply, the checked tree already has
   `ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean ::
   exists_real_open_nhds_adjSwap` as the lower compactness/open-neighborhood
   supplier, so theorem-2 docs should treat any `local_spacelike_open_edge_*`
   pseudocode only as internal proof fragments under
   `choose_real_open_edge_for_adjacent_swap`, not as a rival contract-level
   theorem family. The wrapper-level proof transcript must also stay split
   explicitly: `choose_real_open_edge_for_adjacent_swap` owns the compact-
   support finite-cover packaging, `swapped_support_lies_in_swapped_open_edge`
   owns only support transport along `hswap`, and
   `swapped_open_edge_embeds_in_extendedTube` owns only ET transport from the
   chosen edge to the swapped preimage edge;
13. the theorem-2 continuity package explicitly distinguishes checked-present
   `bvt_F` suppliers from the remaining missing constructor work: the blueprint
   must name `OSToWightmanBoundaryValuesBase.lean :: bvt_F_holomorphic` and
   `OSToWightmanBoundaryValuesBase.lean :: bvt_boundary_values` as the checked
   public unflattened suppliers, and it must also bind them to the flattened
   theorem slots explicitly: `bvt_F_holomorphic` is the source for
   `bvt_F_flattened_holomorphic`, while `bvt_boundary_values` is the source for
   `bvt_F_flattened_distribution_boundary`; `boundary_values_tempered` remains
   the broader public existence theorem rather than the designated source for
   that flattened boundary-distribution slot. The blueprint must record
   `OSToWightman.lean :: full_analytic_continuation_with_symmetry_growth` as
   the checked upstream public growth source those suppliers consume, and keep
   the exact checked field-access pattern explicit too: in the current tree the
   growth package is the tail component
   `(full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.2.2.2.2.2`
   after the holomorphy / Euclidean / permutation / translation /
   canonical-star fields. The visibility split inside
   `OSToWightmanBoundaryValuesBase.lean` must remain explicit:
   `boundary_values_tempered` is public, while
   `forwardTube_boundaryValueData_of_polyGrowth` and
   `full_analytic_continuation_boundaryValueData` are checked-private in-file
   packaging theorems rather than exported cross-file theorem surfaces.
   More sharply, the blueprint must record that the checked growth source is an
   actual exported field of
   `full_analytic_continuation_with_symmetry_growth` for the chosen `bvt_F`
   witness (`∃ C_bd N, 0 < C_bd ∧ ∀ z ∈ ForwardTube d n, ‖bvt_F z‖ ≤ ...`),
   already unpacked in the private theorem
   `OSToWightmanBoundaryValuesBase.lean ::
   full_analytic_continuation_boundaryValueData`; the real open theorem package
   is therefore only the flattened polynomial-growth transport plus the new
   regular constructor `flatRegular_of_boundary_distribution_and_polyGrowth`,
   and the blueprint must assign that missing constructor work to the checked
   `ForwardTubeDistributions.lean` layer rather than leaving ownership vague or
   collapsing it into the final locality theorem file. Within that flattened
   continuity subpackage, the contract-level theorem-slot names must be fixed
   consistently at `bvt_F_flattened_holomorphic`,
   `bvt_F_flattened_distribution_boundary`, and `bvt_F_flattened_growth`; the
   older flipped draft vocabulary `flattened_bvt_F_*` should not survive as a
   competing naming scheme anywhere in the active theorem-2 docs.
14. the theorem-2 canonical-shift adapter must also consume the checked
   forward-tube boundary-recovery surface explicitly rather than talking about
   generic rewrite lemmas in the abstract. In particular, the blueprint should
   record `ForwardTubeDistributions.lean ::
   boundary_value_recovery_forwardTube_of_flatRegular` and
   `boundary_value_recovery_forwardTube_of_flatRegular_from_bv` as
   checked-present recovery theorems, and it should describe the still-missing
   theorem-2-specific package above the adjacent raw-boundary theorem as a
   specialization of that checked recovery surface at
   `canonicalForwardConeDirection`, not as a free-floating request to invent
   new raw/canonical rewrite machinery from scratch.
15. that adapter contract is only implementation-ready if it also names the
   exact checked boundary-functional inputs demanded by
   `boundary_value_recovery_forwardTube_of_flatRegular_from_bv`: the
   specialization must use `OSToWightmanBoundaryValuesBase.lean :: bvt_W` as
   the boundary functional, `bvt_W_continuous` as its continuity witness, and
   `bvt_boundary_values` as the boundary-value theorem supplying the
   `nhdsWithin 0 (Set.Ioi 0)` limit at
   `canonicalForwardConeDirection`. The blueprint should now keep two separate
   theorem packages visible above that checked recovery surface:
   first the theorem-2-specific specialization
   `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`, then the gluing
   theorem `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
   that combines that specialization with the adjacent raw-boundary equality.
   The summary-level acceptance criterion is now stricter too: the blueprint
   may not compress that gluing step into “plus two uses of recovery”. It must
   say explicitly that the local transcript is raw-boundary theorem first,
   canonical recovery on the swapped (`g`) side second, canonical recovery on
   the unswapped (`f`) side third, and only then transitivity/symmetry
   closure. The acceptance standard is stronger than prose order alone: the
   doc must freeze the local theorem surface contract
   `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`
   -> `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` on the swapped
   side
   -> `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` on the unswapped
   side
   -> transitivity/symmetry closure,
   and it must say that no theorem in
   `OSToWightmanBoundaryValueLimits.lean` is allowed to reopen
   `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` or the
   checked recovery theorem itself after this gluing seam has been packaged.
   It must also say that the next theorem
   `bvt_F_swapCanonical_pairing_of_adjacent_chain` is a separate adjacent-
   factorization reducer consuming only that adjacent canonical theorem plus
   explicit factorization data for `swap i j`, not the raw-boundary or
   boundary-recovery theorems directly. That reducer is only implementation-
   ready if its own internal transcript is frozen too: (a) package the finite
   adjacent-transposition factorization data for `swap i j`; (b) derive the
   per-step test-function transport witness from the endpoint swap identity;
   (c) apply `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
   step-by-step along that chain; (d) compose the resulting equalities and
   rewrite the composed permutation back to the target `swap i j` statement.
   The first two subslots may not reopen raw-boundary or recovery theorems,
   and the step-application slot must consume the already-packaged adjacent
   canonical theorem exactly as exported. If those supplier surfaces or either
   of those two endgame theorem packages are not written explicitly, the
   theorem-2 endgame is still under-specified for Lean.
16. the theorem-2 blueprint must also distinguish contract-level theorem slots
   from pseudocode-only helper names inside the general-swap reduction script.
   In particular, schematic names such as `adjacentSwapFactorization` and
   `AdjacentCanonicalSwapPairingStepHolds` may be used to illustrate the
   internal shape of `bvt_F_swapCanonical_pairing_of_adjacent_chain`, but they
   must be marked explicitly as non-checked, non-frozen placeholders rather
   than as theorem surfaces that already exist or that later Lean work must
   preserve literally.

## 4.3. `theorem4_cluster_blueprint.md`

This doc is complete only when:

1. theorem-3-to-one-factor extraction is spelled out through exact theorem
   names;
2. `normalizedZeroDegreeRightVector` has a literal definition and structural
   lemmas;
3. the theorem-4 slot ledger is explicit enough for direct Lean execution,
   namely
   `normalizedZeroDegreeRightVector`
   -> `normalizedZeroDegreeRightVector_bound` / `..._funcs_zero` /
      `..._funcs_pos`
   -> `conjTensorProduct_degreeZeroUnit_eq`
   -> `osConjTensorProduct_degreeZeroUnit_eq`
   -> `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`
   -> `zeroDegree_right_single_wightman_extracts_factor`
   -> `zeroDegree_right_single_os_extracts_factor`
   -> `zero_degree_component_comparison_for_normalized_right_vector`
   -> `cluster_left_factor_transport`
   -> `cluster_right_factor_transport`
   -> `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
   -> `bvt_cluster_positiveTime_singleSplit_core`
   -> `canonical_cluster_integrand_eq_singleSplit_integrand`
   -> `canonical_translate_factor_eq_singleSplit_translate_factor`
   -> `singleSplit_core_rewrites_to_canonical_shell`
   -> `canonical_shell_limit_of_rewrite`
   -> `bvt_cluster_canonical_from_positiveTime_core`
   -> `bvt_F_clusterCanonicalEventually_translate`;
   and that same ledger is grouped explicitly as a theorem-creation queue with
   fixed package counts, not a vague “cluster package”:
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
   - **2-slot base-bridge package** in
     `OSToWightmanBoundaryValuesBase.lean`:
     `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
     then `bvt_cluster_positiveTime_singleSplit_core`;
   - **5-slot public adapter package** in
     `OSToWightmanBoundaryValues.lean`:
     `canonical_cluster_integrand_eq_singleSplit_integrand`,
     `canonical_translate_factor_eq_singleSplit_translate_factor`,
     `singleSplit_core_rewrites_to_canonical_shell`,
     `canonical_shell_limit_of_rewrite`,
     `bvt_cluster_canonical_from_positiveTime_core`;
   - only after those 19 named upstream slots are present may the already
     checked private frontier
     `OSToWightmanBoundaryValues.lean :: bvt_F_clusterCanonicalEventually_translate`
     be treated as the final theorem-4 consumer shell.
   The right-factor lane is frozen sharply enough that later Lean work must
   reuse the same normalized degree-`0` witness package via the definitional
   alias `normalizedZeroDegreeLeftVector d := normalizedZeroDegreeRightVector d`,
   then switch only the checked right-single extraction rewrites and the same
   zero-degree comparison theorem. A second normalization package, a hidden
   left-unit witness, or any extra scalar-normalization clean-up inside
   `cluster_right_factor_transport` is out of contract. More sharply, the
   first extraction pair must itself carry an explicit proof transcript:
   `zeroDegree_right_single_wightman_extracts_factor` must consume exactly
   `WightmanInnerProduct_right_single`
   -> `normalizedZeroDegreeRightVector_funcs_zero`
   -> `normalizedZeroDegreeRightVector_funcs_pos`
   -> `conjTensorProduct_degreeZeroUnit_eq`, while
   `zeroDegree_right_single_os_extracts_factor` must consume exactly
   `OSInnerProduct_right_single`
   -> `normalizedZeroDegreeRightVector_funcs_zero`
   -> `normalizedZeroDegreeRightVector_funcs_pos`
   -> `osConjTensorProduct_degreeZeroUnit_eq`
   -> `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`. Also, there is no
   separate contract-level theorem slot such as
   `normalizedZeroDegreeRightVector_is_unit_normalized`: any scalar evaluation
   fact must be derived locally from `normalizedZeroDegreeRightVector_funcs_zero`
   and the literal `degreeZeroUnit` definition rather than added to the frozen
   theorem-4 queue;
4. the corrected bridge theorem
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
   is named explicitly as the replacement for the legacy same-shell
   `...FactorComparison` surface, and the docs say unambiguously that
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`
   is legacy-only support rather than an endorsed theorem-4 closure surface;
5. the canonical-shell adapter above the positive-time single-split core is
   isolated under exact theorem slots instead of hidden in the final `sorry`,
   and the forward consumption order is now fixed one row at a time:
   `bvt_cluster_positiveTime_singleSplit_core`
   -> `canonical_cluster_integrand_eq_singleSplit_integrand`
   -> `canonical_translate_factor_eq_singleSplit_translate_factor`
   -> `singleSplit_core_rewrites_to_canonical_shell`
   -> `canonical_shell_limit_of_rewrite`
   -> `bvt_cluster_canonical_from_positiveTime_core`
   -> `OSToWightmanBoundaryValues.lean:398 :: private bvt_F_clusterCanonicalEventually_translate`.
   More sharply, `canonical_cluster_integrand_eq_singleSplit_integrand` may
   consume only the checked canonical-direction surfaces
   `canonicalForwardConeDirection` / `canonicalForwardConeDirection_mem` plus
   the repaired base-core shell statement, `canonical_translate_factor_eq_singleSplit_translate_factor`
   may consume only translated-shell data already in scope
   (`translateSchwartzNPoint` together with that same canonical-direction
   surface and the translated statement shape of private
   `bvt_F_clusterCanonicalEventually_translate`), and
   `singleSplit_core_rewrites_to_canonical_shell` must be implemented as a
   literal five-step shell-level transcript rather than a vague wrapper: (i)
   freeze the full frontier quantifier block `(n, m, f, g, ε, a, t)` and state
   the exact canonical-shell goal later consumed by
   `canonical_shell_limit_of_rewrite`; (ii) prove a local integrand-rewrite
   sublemma using `canonical_cluster_integrand_eq_singleSplit_integrand`, and
   that sublemma must rewrite only the analytic kernel visible at
   `OSToWightmanBoundaryValues.lean:398`, namely
   `bvt_F OS lgc (n + m) (fun k μ => ↑(x k μ) + t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)`;
   (iii) prove a separate translated-factor rewrite sublemma using
   `canonical_translate_factor_eq_singleSplit_translate_factor`, and that
   sublemma must rewrite only the test-function factor
   `((f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x)`;
   (iv) check that the eventual/limit quantifier block is otherwise unchanged
   and rewrite the shell statement by those two sublemmas until it matches the
   positive-time single-split core verbatim; (v) only then apply the base
   export `bvt_cluster_positiveTime_singleSplit_core`. Theorem-3 limit
   transport may not enter earlier. Only `canonical_shell_limit_of_rewrite` may
   import the
   checked scalar-holomorphic / limit-transport package from
   `OSToWightmanBoundaryValueLimits.lean`, source-checked at the exact anchors
   `:260 :: bvt_singleSplit_xiShiftHolomorphicValue`,
   `:273 :: differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue`,
   `:290 :: bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`,
   `:314 :: bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`,
   `:350 :: tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`,
   `:446 :: tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`,
   `:494 :: eqOn_rightHalfPlane_of_ofReal_eq`, and
   `:536 :: bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`, but only
   in the explicit internal order
   `singleSplit_core_rewrites_to_canonical_shell`
   -> instantiate the scalar holomorphic object whose positive-real trace is to
   be compared
   -> `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
   -> optional right-half-plane uniqueness via
   `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` and
   `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
   -> final Wightman-target limit transport by
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`
   -> export the exact eventual canonical-shell statement consumed by
   `bvt_cluster_canonical_from_positiveTime_core`.
   So this completion-plan doc now fixes the shell seam sharply enough that the
   public adapter queue has one allowed proof order only: first the analytic
   `bvt_F ... canonicalForwardConeDirection ...` rewrite, second the translated
   `((f.tensorProduct (translateSchwartzNPoint ... a g)) x)` rewrite, third the
   direct application of `bvt_cluster_positiveTime_singleSplit_core`, and only
   after those three shell-local steps the scalar/holomorphic `t -> 0+`
   transport inside `canonical_shell_limit_of_rewrite`.
   The Schwinger-target theorems
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift` and
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
   are lower supplier legs only, and the helper
   `eqOn_rightHalfPlane_of_ofReal_eq` is uniqueness infrastructure only, not a
   separate theorem-4 adapter slot. The deprecated bridge
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
   is forbidden for theorem 4. Also, source-checking the live frontier file now
   fixes the only checked downstream consumer shell at
   `OSToWightmanBoundaryValues.lean :27 :: bv_cluster_transfer_of_canonical_eventually`,
   `:398 :: private bvt_F_clusterCanonicalEventually_translate`,
   `:414 :: private bvt_F_clusterCanonicalEventually`, and
   `:473 :: private bvt_W_cluster`, so
   `bvt_cluster_canonical_from_positiveTime_core` may consume only
   `canonical_shell_limit_of_rewrite`, must be provable by a single direct
   application of that theorem, and private
   `bvt_F_clusterCanonicalEventually_translate` may consume only
   `bvt_cluster_canonical_from_positiveTime_core` rather than hiding any extra
   rewrite or limit-transport work. The literal frontier boundary is therefore
   frozen as
   `canonical_shell_limit_of_rewrite`
   -> `bvt_cluster_canonical_from_positiveTime_core`
   -> `OSToWightmanBoundaryValues.lean:398 :: private bvt_F_clusterCanonicalEventually_translate`;
6. the blueprint explicitly distinguishes repo-present cluster reductions
   (`...singleSplitLargeSpatial`, `...singleSplitSchwingerLargeSpatial`,
   legacy `...singleSplitFactorComparison`, and the final private wrapper
   `OSToWightmanBoundaryValues.lean :: bvt_F_clusterCanonicalEventually_translate`)
   from still-missing named adapter theorems, and it now fixes the final
   wrapper as a pure downstream consumer rather than another mixed repair site.
   More sharply, the exact checked base anchors
   `OSToWightmanBoundaryValuesBase.lean:2214/:2352/:2514` are the only
   admissible checked inputs on the theorem-4 bridge lane below the repaired
   replacement theorem, and `bvt_cluster_positiveTime_singleSplit_core` is the
   sole theorem allowed to leave the base file and enter the public
   canonical-shell adapter ladder;
7. theorem 4 is visibly pure consumer work after theorem 3;
8. theorem-4 file ownership is fixed sharply enough for direct Lean execution:
   one-factor transport extraction in `.../OSToWightmanPositivity.lean`, the
   repaired positive-time bridge in `.../OSToWightmanBoundaryValuesBase.lean`,
   and the public canonical-shell adapter plus final wrapper in
   `.../OSToWightmanBoundaryValues.lean`, with
   `.../OSToWightmanBoundaryValueLimits.lean` explicitly *not* treated as a
   theorem-4 home under the current checked-tree contract;
9. the theorem-4 completion standard is not merely “list the slots”, but
   “freeze the owner / consumes / exports / next-consumer order” for the
   bridge-to-canonical-shell seam, so later implementation does not have to
   infer whether a theorem belongs in `OSToWightmanPositivity.lean`,
   `OSToWightmanBoundaryValuesBase.lean`, or
   `OSToWightmanBoundaryValues.lean`, or whether a given rewrite theorem is
   supposed to act at integrand level, shell-statement level, or eventual-limit
   level. This includes the asymmetry discipline inside the one-factor package:
   `cluster_right_factor_transport` is not a license to build a mirrored
   normalization subtheory, only to reuse the already-fixed degree-`0` witness
   and swap to the right-input extraction surfaces. The same completion
   standard now applies to the small normalization rewrites that sit between
   the witness package and the extraction lemmas: any complete theorem-4 doc
   must make explicit that `conjTensorProduct_degreeZeroUnit_eq`,
   `osConjTensorProduct_degreeZeroUnit_eq`, and
   `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq` belong to
   `OSToWightmanPositivity.lean`, are consumed before the one-factor
   extraction theorems, and exist specifically to prevent hidden casts or
   scalar normalizations from leaking into `cluster_left_factor_transport` or
   `cluster_right_factor_transport`. Any theorem-4 doc counted as complete
   must preserve that execution ledger, not collapse it back into prose.
   In particular, any status summary or secondary checklist is incomplete if it
   says merely “theorem 4 still needs the extraction package plus adapter”
   without also freezing the package split as exactly 12 positivity/extraction
   slots in `OSToWightmanPositivity.lean`, 2 repaired bridge slots in
   `OSToWightmanBoundaryValuesBase.lean`, and 5 public canonical-shell adapter
   slots in `OSToWightmanBoundaryValues.lean`, followed only then by the
   already-checked private frontier consumer.

## 4.4. `general_k_continuation_blueprint.md`

This doc is complete only when:

1. every Chapter V / VI package has a fixed theorem-slot inventory;
2. the envelope/Malgrange-Zerner step is explicit and not a black box;
3. file boundaries and import order are fixed;
4. the SCV dependency surface is named exactly;
5. the trusted-vs-untrusted checklist is explicit.

## 4.5. `scv_infrastructure_blueprint.md`

This doc is complete only when:

1. the one-point forward-tube package has an explicit proof transcript;
2. the flattened regular constructor route is fixed;
3. Vladimirov-Tillmann and Bochner packages are split into real theorem
   packages;
4. no consumer doc needs to invent its own boundary-value constructor.

## 4.6. `r_to_e_blueprint.md`

This doc is complete only when:

1. the current minimal bridge theorem `wightman_to_os_full` is source-checked
   against the live production theorem in
   `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`,
   with its exact existing inputs fixed as
   `constructZeroDiagonalSchwingerFunctions`,
   `constructedSchwinger_tempered_zeroDiagonal`,
   `constructedZeroDiagonalSchwinger_linear`,
   `W_analytic_BHW`, and `bhw_distributional_boundary_values`;
2. any future stronger reverse theorem is documented against the actual field
   inventory of `SchwingerOS.lean :: OsterwalderSchraderAxioms`, namely
   `E0_tempered`, `E0_linear`, `E0_reality`,
   `E1_translation_invariant`, `E1_rotation_invariant`,
   `E2_reflection_positive`, `E3_symmetric`, `E4_cluster`, so the docs do not
   swap `E2`/`E3`, omit `E0_reality`, or confuse the real structure fields
   with the derived accessor `OS.schwinger`;
3. the reverse blueprint distinguishes checked-present honest Euclidean-side
   theorem surfaces from quarantined false/off-paper ones, including the fact
   that `wickRotatedBoundaryPairing_reality` and
   `wickRotatedBoundaryPairing_symmetric` are honest current packaging inputs,
   while `schwingerExtension_os_term_eq_wightman_term`,
   `schwingerExtension_os_inner_product_eq_wightman`, and
   `schwingerExtension_os_inner_product_eq_wightman_positivity` are deleted
   from the active route;
4. the future `E2_reflection_positive` route is written explicitly as a reverse
   Section-4.3 transport/density package on the Wick-restricted family rather
   than as any reuse of the false OS=`Wightman` pairing chain or of the forward
   `E -> R` positivity theorem; the docs must freeze the exact theorem-slot
   ladder
   `wickRotated_positiveTimeCore -> wickRotatedBoundaryPairing_eq_transport_inner_on_core -> wickRotatedBoundaryPairing_nonneg_on_core -> wickRotated_positiveTimeCore_dense -> wickRotatedBoundaryPairing_nonneg_by_density -> constructSchwinger_positive -> OsterwalderSchraderAxioms.E2_reflection_positive`,
   with `constructSchwinger_positive` recorded explicitly as the still-missing
   honest reverse Section-4.3 packaging theorem in
   `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` rather than as
   a reuse of the quarantined wrapper
   `wickRotatedBoundaryPairing_reflection_positive`;
5. the future `E4_cluster` route is written explicitly as the parallel reverse
   Section-4.4 transport/density package rather than as a vague promise to
   reuse `W_analytic_cluster_integral` later; the docs must freeze the exact
   consumer ladder
   `W_analytic_cluster_integral -> wickRotatedBoundaryPairing_cluster -> constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster -> OsterwalderSchraderAxioms.E4_cluster`,
   with the first two surfaces source-checked as already present in
   `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` and the latter
   three surfaces recorded explicitly as the still-missing zero-diagonal
   packaging theorem family targeting `Wightman/Reconstruction/SchwingerOS.lean`.
   More sharply, the proof-doc contract must no longer stop at the slogan
   “restrict the tensor product”: it must freeze the exact local adapter order
   and the exact quantified field obligations from `SchwingerOS.lean:792-804`.
   The first adapter builds the translated witness
   `g_a : ZeroDiagonalSchwartz d m`, the second builds the quantified
   `(n + m)`-point witness `fg_a : ZeroDiagonalSchwartz d (n + m)` with the
   literal tensor-product pointwise formula required by
   `SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster`, and only the
   final theorem consumes `wickRotatedBoundaryPairing_cluster` plus those
   witnesses to discharge the field inequality; later summary docs are not
   allowed to abbreviate this family back down to a black-box
   `constructSchwinger_cluster` step.

   Minimum acceptance ledger for reverse-late-field coordination docs:

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
6. the packaging seam from current `SchwartzNPoint` theorems to future
   `ZeroDiagonalSchwartz` axiom fields is explicit wherever the theorem surface
   changes, especially for `E0_reality` and `E3_symmetric`;
7. the docs explicitly record the sharper late-field status split inside the
   live `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` file:
   `wickRotatedBoundaryPairing_reflection_positive` is only a checked-present
   **quarantined** wrapper because it still depends on the false
   `schwingerExtension_os_inner_product_eq_wightman` chain, whereas
   `W_analytic_cluster_integral` is a live theorem-shaped **supplier** on the
   common-BHW / full-`SchwartzNPoint` level and therefore sits strictly
   upstream of the future `ZeroDiagonalSchwartz` field witness for
   `E4_cluster`; later docs must not compress both into one generic “late
   reverse positivity/cluster” bucket. More sharply, they must preserve the
   exact cluster packaging order
   `W_analytic_cluster_integral -> wickRotatedBoundaryPairing_cluster -> constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster -> OsterwalderSchraderAxioms.E4_cluster`
   instead of jumping directly from the supplier theorem to the final axiom
   field or hiding the quantified `g_a` / `fg_a` witnesses inside an unnamed
   packaging blob;
8. the future split `E1` package is no longer allowed to hide behind a bundled
   `EuclideanInvariance` slogan: the docs must fix separate translation and
   rotation theorem slots, their file ownership in
   `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`, the common-BHW
   transport route they consume, and the exact order
   `E1_translation_invariant -> E1_rotation_invariant` before the final
   stronger wrapper theorem is written.

## 5. Audit queries that must return clean

Before declaring the proof docs complete, rerun searches like:

```text
rg -n "candidate route|if easiest|may shift|future theorem slot|primary route|fallback route|placeholder" docs/*.md
```

and manually justify every remaining hit.

Also rerun theorem-name cross-checks against the live code for:

1. theorem 2 consumer theorems,
2. theorem 3 consumer chain,
3. theorem 4 extraction theorems,
4. SCV one-point constructors,
5. GNS matrix-coefficient bridge dependencies.

## 6. Definition of done

The proof-doc stack is complete only when:

1. every active frontier theorem has one endorsed route;
2. every side-lane theorem package has fixed names or an explicitly quarantined
   blocked-only fallback;
3. the global docs (`sorry_triage.md`, `mathlib_gap_analysis.md`) agree with
   the per-theorem blueprints;
4. production work can proceed by proving named theorem packages rather than by
   making fresh mathematical choices.
