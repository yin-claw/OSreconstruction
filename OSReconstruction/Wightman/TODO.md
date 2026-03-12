# Wightman TODO: OS Reconstruction Priority Queue

Last updated: 2026-03-12

This file tracks the active blocker picture on the OS reconstruction path.
Policy lock: no wrappers, no useless lemmas, no code bloat; close `sorry`s with substantial mathematical proofs.

## Live Sorry Census

Count convention: direct tactic holes only (`^[[:space:]]*sorry([[:space:]]|$)`).

| Scope | Direct `sorry` lines |
|-------|----------------------:|
| `OSReconstruction/Wightman` | 29 |
| `OSReconstruction/SCV` | 2 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 39 |
| **Whole project** | **72** |

Count cross-checked on 2026-03-11 with:
```bash
rg -c '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
```

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

Active upstream blockers:
- `OSToWightman.lean` (1):
  - `schwinger_continuation_base_step`
- `OSToWightmanBoundaryValues.lean` (7):
  - `boundary_values_tempered`
  - `bv_translation_invariance_transfer`
  - `bv_lorentz_covariance_transfer`
  - `bv_local_commutativity_transfer`
  - `bv_positive_definiteness_transfer`
  - `bv_hermiticity_transfer`
  - `bvt_cluster`

Current status:
- the fake intermediate Bochner path is off the active chain
- the active continuation chain goes through the honest OS quotient/Hilbert semigroup already built in `OSToWightmanSemigroup.lean`
- `OSLinearGrowthCondition` is already used upstream to prove polynomial growth of time-shift matrix elements and hence contraction of the Euclidean semigroup
- the positive-time spectral-power continuity input is now landed in `vNA/Bochner/SemigroupRoots.lean`
- `Wightman/SchwartzTensorProduct.lean` now contains genuine insertion operators (`productTensorUpdateCLM`, `prependFieldCLMLeft/Right`) for the Schwartz kernel-extension lane
- the real remaining work is still:
  - `schwinger_continuation_base_step` in `OSToWightman.lean`
  - `boundary_values_tempered` in `OSToWightmanBoundaryValues.lean`
  - the six transfer theorems in `OSToWightmanBoundaryValues.lean`
  - `bvt_cluster` in `OSToWightmanBoundaryValues.lean`

Immediate sharpened subgaps:
- For `schwinger_continuation_base_step`: the honest remaining choice is between an OS-side interleaved operator representation and a deeper Schwartz kernel-extension theorem. The new tensor insertion maps only support the latter; they do not close the blocker by themselves.
- For `boundary_values_tempered`: the generic DCT/integrability/tempered-boundary package is now in `SCV/LaplaceSchwartz.lean`; the genuine missing content is deriving the two growth hypotheses `hpoly` and `hunif` from the OS input.

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

`WickRotation/SchwingerAxioms.lean` (7):
- `wick_rotated_kernel_mul_zeroDiagonal_integrable`
- `constructedSchwinger_tempered_zeroDiagonal`
- `polynomial_growth_forwardTube_full`
- `polynomial_growth_on_PET`
- `schwinger_os_term_eq_wightman_term`
- `bhw_euclidean_reality_ae`
- `bhw_pointwise_cluster_euclidean`
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
- `isConnected_permutedExtendedTube_inter_translate`

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
2. Use the extracted SCV boundary-distribution lemmas to reduce `boundary_values_tempered` in `OSToWightmanBoundaryValues.lean` to the genuine missing growth inputs `hpoly` and `hunif`.
3. Keep the new tensor insertion infrastructure in `Wightman/SchwartzTensorProduct.lean` in mind if the continuation blocker turns into a genuine Schwartz kernel-extension theorem, but do not confuse that groundwork with closure of the live blocker.
4. After `boundary_values_tempered`, finish the six transfer theorems and `bvt_cluster` in `OSToWightmanBoundaryValues.lean`.
5. In parallel or next, attack the two honest R→E roots in `SchwingerAxioms.lean`:
   - coincidence-singularity / zero-diagonal integrability
   - Euclidean reality / reflection
6. Defer `StoneTheorem` / GNS operator-theoretic work until the analyticity lane is materially settled.

## Commands

```bash
rg -n '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
lake build OSReconstruction.SCV
lake build OSReconstruction.Wightman
```
