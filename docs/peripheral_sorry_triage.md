# Peripheral Sorry Triage

Purpose: this note records the non-`vNA` production `sorry`s that are real but
not on the shortest current theorem-2/3/4 OS route.

This note should be read together with:
- `docs/sorry_triage.md`
- `docs/gns_pipeline_blueprint.md`
- `docs/nuclear_spaces_blueprint.md`
- `docs/scv_infrastructure_blueprint.md`
- `docs/bhw_permutation_blueprint.md`
- `docs/r_to_e_blueprint.md`

Here "peripheral" does **not** mean mathematically unimportant. It means:

1. not the current theorem-2 locality frontier,
2. not the current theorem-3 positivity frontier,
3. not the current theorem-4 cluster frontier,
4. not the current final general-`k` OS II documentation core.

## 1. Reverse-direction / historical route residuals

| File:line | Theorem | Why peripheral right now | Primary doc |
|---|---|---|---|
| `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean:2366` | `schwingerExtension_os_term_eq_wightman_term` | false route, should be quarantined not advanced | `docs/r_to_e_blueprint.md` |
| `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean:3581` | `W_analytic_cluster_integral` | reverse-direction cluster, not current `E -> R` target | `docs/r_to_e_blueprint.md` |
| `Wightman/Reconstruction/WickRotation/BHWTranslation.lean:1115` | `isPreconnected_baseFiber` | old-route residual, no longer needed on merged Route 1 path | `docs/r_to_e_blueprint.md` |
| `Wightman/Reconstruction/WickRotation/ForwardTubeLorentz.lean:1129` | `wickRotation_not_in_PET_null` | reverse-direction measure-zero geometry | `docs/r_to_e_blueprint.md` |

## 2. GNS / uniqueness side lane

| File:line | Theorem | Why peripheral right now | Primary doc |
|---|---|---|---|
| `Wightman/Reconstruction/GNSHilbertSpace.lean:1258` | `gns_matrix_coefficient_holomorphic_axiom` | important, but not on theorem-2/3/4 route | `docs/gns_pipeline_blueprint.md` |
| `Wightman/Reconstruction/Main.lean:82` | `wightman_uniqueness` | standalone theorem depending on cyclicity | `docs/wightman_uniqueness_blueprint.md` |

## 3. Nuclear-space / Bochner-Minlos side lane

| File:line | Theorem | Why peripheral right now | Primary doc |
|---|---|---|---|
| `Wightman/NuclearSpaces/NuclearSpace.lean:234` | `gauge_dominates_on_subspace_of_convex_nhd` | infrastructure for GNS/Minlos, not theorem-2/3/4 | `docs/nuclear_spaces_blueprint.md` |
| `Wightman/NuclearSpaces/NuclearSpace.lean:313` | `product_seminorm_dominated` | same | `docs/nuclear_spaces_blueprint.md` |
| `Wightman/NuclearSpaces/BochnerMinlos.lean:285` | `bochner_tightness_and_limit` | Euclidean measure package | `docs/nuclear_spaces_blueprint.md` |
| `Wightman/NuclearSpaces/BochnerMinlos.lean:384` | `minlos_projective_consistency` | Euclidean measure package | `docs/nuclear_spaces_blueprint.md` |
| `Wightman/NuclearSpaces/BochnerMinlos.lean:399` | `minlos_nuclearity_tightness` | Euclidean measure package | `docs/nuclear_spaces_blueprint.md` |
| `Wightman/NuclearSpaces/BochnerMinlos.lean:465` | `eval_maps_generate_sigma_algebra` | Euclidean measure package | `docs/nuclear_spaces_blueprint.md` |
| `Wightman/NuclearSpaces/BochnerMinlos.lean:485` | `eval_charfun_implies_fd_distributions` | Euclidean measure package | `docs/nuclear_spaces_blueprint.md` |

## 4. SCV side infrastructure

| File:line | Theorem | Why peripheral right now | Primary doc |
|---|---|---|---|
| `SCV/BochnerTubeTheorem.lean:126` | `bochner_local_extension` | important SCV infrastructure, but not first live blocker | `docs/scv_infrastructure_blueprint.md` |
| `SCV/BochnerTubeTheorem.lean:220` | `bochner_tube_extension` | same | `docs/scv_infrastructure_blueprint.md` |

## 5. Complex-Lie-group permutation side lane

| File:line | Theorem | Why peripheral right now | Primary doc |
|---|---|---|---|
| `ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlocker.lean:55` | `blocker_isConnected_permSeedSet_nontrivial` | BHW permutation branch, not current theorem-2/3/4 route | `docs/bhw_permutation_blueprint.md` |
| `ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlocker.lean:119` | `blocker_iterated_eow_hExtPerm_d1_nontrivial` | same | `docs/bhw_permutation_blueprint.md` |

## 6. Suggested execution order inside the peripheral backlog

If the user later wants to attack peripheral blockers without entering `vNA`,
the recommended order is:

1. GNS holomorphic bridge,
2. nuclear/kernal theorem package,
3. standalone uniqueness,
4. SCV Bochner tube theorem,
5. BHW permutation blockers,
6. reverse-direction historical residuals.

This order keeps the mathematically reusable packages ahead of the mostly
historical or side-lane blockers.

## 7. What not to do

1. Do not let peripheral work re-contaminate the theorem-2/3/4 route.
2. Do not reopen the false reverse-direction positivity chain.
3. Do not treat all peripheral blockers as equal priority; GNS/nuclear work is
   much more central than old-route PET connectivity.

## 8. Why this file exists

The repo now has enough documentation that "not on the immediate OS route" is
no longer the same thing as "untracked." This file keeps the side backlog
visible without letting it obscure the current active frontiers.
