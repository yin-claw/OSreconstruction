# R→E Sorry Elimination Plan

## Status Snapshot (2026-03-19)

**Total R→E sorrys**: 17 across 7 files
**Critical path** (blocks `os_to_wightman_full`): 9 sorrys in 2 files
**R→E direction** (Wightman→Schwinger): 4 sorrys
**GNS/spectral**: 4 sorrys (orthogonal, blocked by Mathlib gaps)

## Dependency Graph

```
os_to_wightman_full
  └─ constructWightmanFunctions
       ├─ boundary_values_tempered ← BOTTLENECK (sorry)
       │   └─ full_analytic_continuation
       │       ├─ schwinger_continuation_base_step_timeParametric (sorry)
       │       └─ schwinger_continuation_spatial_upgrade (sorry)
       ├─ bv_translation_invariance_transfer (sorry)
       ├─ bv_lorentz_covariance_transfer (sorry)
       ├─ bv_local_commutativity_transfer (sorry)
       ├─ bv_positive_definiteness_transfer (sorry)
       ├─ bv_hermiticity_transfer (sorry)
       └─ bvt_cluster (sorry)

wightman_to_os (proved, but depends on:)
  ├─ schwingerExtension_os_term_eq_wightman_term (sorry)
  ├─ bhw_pointwise_cluster_euclidean (sorry)
  ├─ W_analytic_cluster_integral (sorry)
  └─ wickRotation_not_in_PET_null (sorry)

GNS reconstruction (proved, but properties need:)
  ├─ spectrum_condition (sorry — needs Stone's theorem)
  ├─ cyclicity (sorry — needs nuclear theorem, now proved in gaussian-field)
  └─ vacuum_unique (sorry — needs spectral theory)

wightman_uniqueness (sorry — GNS uniqueness)
```

## Phase 1: Axiom Introduction (unlocks 6 transfer sorrys)

### New axiom: `os_ii_tempered_boundary_values`

**Mathematical content**: Osterwalder-Schrader II, Theorem III.1-2.
Given OS axioms E0-E4 with the linear growth condition E0', the
analytic continuation of the Schwinger functions to the forward tube
has tempered distributional boundary values.

This is the deep content of OS II. Stating it as an axiom is appropriate
because:
1. It's a well-known textbook theorem (OS II, 1975)
2. The proof requires Fourier-Laplace transform theory not in Mathlib
3. It cleanly separates the OS-II analytical content from the
   algebraic/structural transfer steps

**What it unlocks**: Once `boundary_values_tempered` is filled (via
this axiom + existing `full_analytic_continuation` infrastructure),
all 6 transfer sorrys (#4-#9) become provable by straightforward
distributional arguments:
- Each transfer theorem takes an OS property (E1/E1_rot/E3/E2/E0/E4)
- Uses the boundary-value pairing to rewrite the OS property
- Applies distributional uniqueness/continuity to transfer to W_n

**Estimated work**: ~50 lines for the axiom statement + ~30 lines to
wire it into `boundary_values_tempered`.

### New axiom: `jost_measure_zero`

**Mathematical content**: Jost, "General Theory of Quantized Fields"
§IV.4, Theorem IV.4; Streater-Wightman, Theorem 2-12.

For a.e. Euclidean configuration x, there exists a permutation σ and
a complex Lorentz transformation Λ such that the Wick-rotated
σ-permuted Λ-boosted configuration lies in the forward tube.

This fills `wickRotation_not_in_PET_null`. The proof requires either:
- The full Jost theorem (extended tube contains all Jost points), or
- A complex Lorentz boost argument handling the k=0 forward cone case

Both are substantial (~100+ lines) and involve complex Lorentz geometry
not currently formalized.

**What it unlocks**: `ae_euclidean_points_in_permutedTube`, used
throughout SchwingerAxioms.lean and OSToWightmanBoundaryValues.lean
for a.e. pointwise arguments.

**Estimated work**: ~20 lines for the axiom statement.

## Phase 2: Transfer Theorem Proofs (6 sorrys → 0)

With `boundary_values_tempered` filled via Phase 1, prove the 6
boundary-value transfer theorems. Each follows the pattern:

1. Extract W_n, F_n, boundary-value pairing from `boundary_values_tempered`
2. Use the OS property (E1/E1_rot/E3/E2/E0/E4) on zero-diagonal functions
3. Transfer to all Schwartz functions via density + continuity

### `bv_translation_invariance_transfer` (~60 lines)
- E1 on zero-diagonal → R1 on all Schwartz
- Key: boundary-value pairing commutes with real translations
- Tools: change of variables in the BV integral

### `bv_lorentz_covariance_transfer` (~60 lines)
- E1_rot → R2
- Key: Lorentz action on BV integral, existing `integral_lorentz_eq_self`

### `bv_local_commutativity_transfer` (~50 lines)
- E3 → R3
- Key: permutation in BV integral

### `bv_positive_definiteness_transfer` (~80 lines)
- E2 → R4 (most complex: involves inner products)
- Key: `schwingerExtension_os_term_eq_wightman_term` for the inner
  product identity; may need Phase 3 first

### `bv_hermiticity_transfer` (~60 lines)
- E0 → R0
- Key: conjugation symmetry in BV integral

### `bvt_cluster` (~50 lines)
- E4 → R5
- Key: cluster property passes through BV limit

**Total estimated**: ~360 lines, unlocking 6 sorrys

## Phase 3: R→E Distributional Layer (3 sorrys)

### `schwingerExtension_os_term_eq_wightman_term` (~100 lines)
- File: SchwingerAxioms.lean:2355
- The OS inner product equals the Wightman inner product for
  positive-time-supported test functions
- Key: boundary-value limit + Wick rotation identity
- Ref: OS I Section 5; Streater-Wightman §3.4

### `bhw_pointwise_cluster_euclidean` (~80 lines)
- File: SchwingerAxioms.lean:2885
- Pointwise cluster for BHW extension at Euclidean points
- Key: BHW multiplicativity for product configurations + polynomial
  growth bounds
- Depends on: Wightman R5 (cluster), BHW extension properties

### `W_analytic_cluster_integral` (~50 lines)
- File: SchwingerAxioms.lean:2910
- Integral cluster from pointwise + dominated convergence
- Key: Schwartz decay provides domination
- Depends on: `bhw_pointwise_cluster_euclidean`

## Phase 4: OS-II Deep Content (2 sorrys)

These are the hardest sorrys — the actual OS-II reconstruction:

### `schwinger_continuation_base_step_timeParametric`
- File: OSToWightman.lean:41
- Construct the time-parametric holomorphic witness
- This IS the core OS-II theorem
- Could remain as a sorry/axiom long-term

### `schwinger_continuation_spatial_upgrade`
- File: OSToWightman.lean:63
- Upgrade time-parametric to full holomorphic surface
- Analytic continuation step

## Phase 5: GNS Properties (4 sorrys, orthogonal)

These are blocked by Mathlib gaps (Stone's theorem, spectral theory)
but partially unblocked by gaussian-field:

### `cyclicity` — unblocked by gaussian-field
- File: GNSHilbertSpace.lean:871
- Needs Schwartz nuclear theorem (NOW PROVED in gaussian-field)
- Can be filled once Lean versions align

### `spectrum_condition` — needs Stone's theorem
### `vacuum_unique` — needs spectral theory
### `wightman_uniqueness` — needs GNS uniqueness

## Axiom Inventory After Plan

**Current axioms** (4):
1. `schwartz_nuclear_extension` — proved in gaussian-field ✓
2. `exists_continuousMultilinear_ofSeparatelyContinuous` — proved in gaussian-field ✓
3. `vladimirov_tillmann` — SCV tube-growth theorem
4. `reduced_bargmann_hall_wightman_of_input` — reduced BHW bridge

**Proposed new axioms** (2):
5. `os_ii_tempered_boundary_values` — OS-II tempered BV package
6. `jost_measure_zero` — Jost PET measure characterization

**Total**: 6 axioms, all well-known textbook theorems.
Axioms 1-2 already proved (pending Lean version update).
Axioms 3-6 are standard results from distribution theory and QFT geometry.

## Priority Order

1. **Phase 1** (axiom introduction): 2 new axioms, ~70 lines → unblocks Phases 2-3
2. **Phase 2** (transfers): 6 sorrys, ~360 lines → completes E'→R' critical path
3. **Phase 3** (distributional): 3 sorrys, ~230 lines → completes R→E
4. **Phase 4** (OS-II): 2 sorrys → long-term or axiom
5. **Phase 5** (GNS): 4 sorrys → blocked by Mathlib, partially by gaussian-field

After Phases 1-3: **11 sorrys eliminated**, leaving 6 (2 OS-II deep, 4 GNS/spectral).
