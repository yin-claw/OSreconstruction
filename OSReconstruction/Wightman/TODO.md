# Wightman TODO: OS Reconstruction Priority Queue

Last updated: 2026-03-16

This file tracks the active blocker picture on the OS reconstruction path.
Policy lock: no wrappers, no useless lemmas, no code bloat; close `sorry`s with substantial mathematical proofs.

## Live Sorry Census

Count convention: direct tactic holes only (`^[[:space:]]*sorry([[:space:]]|$)`).

| Scope | Direct `sorry` lines |
|-------|----------------------:|
| `OSReconstruction/Wightman` | 23 |
| `OSReconstruction/SCV` | 2 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 36 |
| **Whole project** | **63** |

Count cross-checked on 2026-03-16 with:
```bash
rg -c '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
```

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
   - critical files: `WickRotation/OSToWightmanSemigroup.lean`, `WickRotation/OSToWightman.lean`, `WickRotation/OSToWightmanBoundaryValues.lean`
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
- for theorem 3 specifically, `OSToWightmanBoundaryValues.lean` contains the
  exported private theorem `bvt_W_positive`, but the actual live
  implementation seam is the Section-4.3 transport package in
  `WickRotation/OSToWightmanPositivity.lean`

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
  - implementation locus: `OSToWightmanPositivity.lean`
  - exported wrapper: `OSToWightmanBoundaryValues.lean :: bvt_W_positive`
  - theorem-4 dependency contract: theorem 4 should consume corrected
    one-factor transport statements extracted from the Section-4.3 transport
    package, not the false same-shell factor identities from older cluster
    notes
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
- For theorem 2 / `bvt_F_swapCanonical_pairing`: the current implementation target is not another continuation theorem. The hard gap is the explicit Route-B real-open-edge support package feeding the checked raw-boundary theorem surface `WickRotation/BHWExtension.lean :: W_analytic_swap_boundary_pairing_eq`, together with the flattened regular constructor package needed to obtain `bvt_F` boundary continuity on the raw real trace.
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
  `bvt_F_boundary_continuous_at_real_support` -> instantiate the checked
  public raw-boundary theorem `W_analytic_swap_boundary_pairing_eq` on the
  identified analytic representative to obtain an **adjacent-only** raw-
  boundary package -> separate adjacent canonical-shift adapter theorem ->
  separate reduction from a general `swap i j` frontier statement to an
  adjacent-transposition chain. The lower pointwise theorem
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
  are implementation targets, not hidden helpers to rediscover.
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
- Theorem-2 file-locus contract is now explicit at the package level too:
  Route-B ET-support geometry theorems belong under the checked
  BHW-permutation adjacent-swap support subfile layer, not in the umbrella
  `.../BHWPermutation.lean` by default; `.../Adjacency.lean` is the default
  home for lower pointwise/open-edge suppliers, while
  `.../AdjacencyDistributional.lean` is the checked distributional pairing
  surface they must feed; the raw-boundary wrapper theorem
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
  Current cross-check against the checked repo-relative loci:
  - `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean`
    already has the base reductions
    `...singleSplitLargeSpatial`, `...singleSplitSchwingerLargeSpatial`, and
    legacy `...singleSplitFactorComparison`;
  - `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
    is still the theorem-3 transport supplier theorem 4 must consume;
  - `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
    has the final private wrapper
    `bvt_F_clusterCanonicalEventually_translate`, its translated wrapper,
    the public transfer theorem `bv_cluster_transfer_of_canonical_eventually`,
    and the exported consumer `bvt_W_cluster`;
  - the intermediate adapter package is still missing under separate theorem
    names and should be introduced explicitly rather than hidden inside the
    final `sorry`.

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

`WickRotation/SchwingerAxioms.lean` (4):
- `schwinger_os_term_eq_wightman_term`
- `bhw_euclidean_reality_ae`
- `bhw_pointwise_cluster_forwardTube`
- `W_analytic_cluster_integral`

Current blocker sharpening (2026-03-10):
- `bhw_euclidean_reality_ae` is now reduced to the honest overlap problem on
  `D = {z ∈ PET | hermitianReverse z ∈ PET}`.
- Infrastructure now present in `SchwingerAxioms.lean`:
  `hermitianReverseOverlap`, `differentiableOn_hermitianReverse_partner`,
  `ae_euclidean_points_in_hermitianReverseOverlap`.
- What still needs to be proved is the Schwarz-reflection identity `F = conj(F ∘ hermitianReverse)`
  on that overlap, extracted from the real Jost-support boundary theorem
  `wightman_real_on_jost_support`.

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
- `Wightman/Reconstruction/Main.lean`: `wightman_uniqueness`
- `Wightman/Reconstruction/GNSHilbertSpace.lean`: one remaining spectral-theory blocker
- `Wightman/WightmanAxioms.lean`: 4 infrastructural sorrys
- `Wightman/NuclearSpaces/*`: side development, not first execution lane
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
