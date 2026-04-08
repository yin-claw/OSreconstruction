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
   - `OSToWightmanPositivity.lean`: the theorem-3 Section-4.3 positivity
     package, in particular
     `bvt_W_eq_inner_on_positiveTimeTransport`,
     `bvt_W_positive_density_reduction`, and
     `bvt_W_positive_direct`
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
   - final wrapper in `OSToWightmanBoundaryValues.lean`
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
- theorem 4 should no longer be described only as the final private wrapper
  `bvt_cluster`: the checked repo already has the base reductions in
  `OSToWightmanBoundaryValuesBase.lean`, but the corrected bridge theorem
  `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
  and the public canonical-shell adapter package are still doc-level targets
  that must be introduced explicitly before the final wrapper proof is treated
  as implementation-ready
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
  flat-regular input, the
  adjacent raw-boundary theorem, the theorem-2-specific canonical pairing
  recovery specialization
  `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` at
  `canonicalForwardConeDirection`, the separate gluing theorem
  `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`, and then a
  separate adjacent-chain reduction theorem
  `bvt_F_swapCanonical_pairing_of_adjacent_chain` before the final frontier
  theorem. `OSToWightmanBoundaryValueLimits.lean` is the checked file locus for
  that planned theorem-2 closure package, but the current tree still uses that
  file only for theorem-3 / `singleSplit_xiShift` limit machinery, so the
  theorem-2 subsection there is still missing support work rather than an
  already-present package to reuse. Those layers must not be hidden in one
  closing `sorry`. Conversely, schematic pseudocode names for the internal
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
   - Euclidean reality / reflection
   - downstream cluster / OS=W term
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
4. `Wightman/NuclearSpaces/*`: 7 sorrys (important but not critical-path)
5. `ComplexLieGroups/*`: 2 remaining BHW-permutation blockers (maintained, not current top lane)

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
2. Non-critical NuclearSpaces side development
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
