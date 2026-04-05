# vNA Sorry Triage

Purpose: this note is the detailed triage sheet for the `36` direct `sorry`s
currently living under `OSReconstruction/vNA`.

This note should be read together with:
- `docs/vna_infrastructure_blueprint.md`
- `docs/unbounded_spectral_project.md`
- `docs/sorry_triage.md`

The `vNA` subtree is not on the shortest current theorem-2/3/4 OS route, but
it is large enough that it needs its own execution order and theorem inventory.

## 1. Current census

| File | Direct `sorry`s |
|---|---:|
| `vNA/MeasureTheory/CaratheodoryExtension.lean` | 11 |
| `vNA/ModularTheory.lean` | 6 |
| `vNA/ModularAutomorphism.lean` | 6 |
| `vNA/KMS.lean` | 10 |
| `vNA/Predual.lean` | 2 |
| `vNA/Unbounded/StoneTheorem.lean` | 1 |
| **Total** | **36** |

## 2. Priority order inside `vNA`

The docs should now enforce this order:

1. measure-theory base,
2. unbounded spectral / Stone package,
3. core modular theory,
4. modular automorphism group,
5. KMS package,
6. predual package.

This is the same dependency order as `docs/vna_infrastructure_blueprint.md`,
but written here against the actual live theorem names.

## 3. File-by-file triage

### 3.1. `MeasureTheory/CaratheodoryExtension.lean` (11)

These are foundational. No later modular proof should depend on them remaining
open.

| Line | Theorem | Package role |
|---|---|---|
| 150 | `toOuterMeasure_Icc` | interval outer measure construction |
| 162 | `borel_le_caratheodory` | measurable-space comparison |
| 308 | `toIntervalPremeasure` | premeasure construction |
| 312 | `toIntervalPremeasure` | premeasure construction |
| 319 | `toIntervalPremeasure` | premeasure construction |
| 373 | `toSpectralMeasure_Icc` | spectral-interval measure construction |
| 380 | `toSpectralMeasure_sigma_additive` | sigma-additivity |
| 385 | `toSpectralMeasure_univ` | normalization |
| 407 | `spectralPremeasureFromLimit` | limit-to-premeasure route |
| 410 | `spectralPremeasureFromLimit` | limit-to-premeasure route |
| 415 | `spectralPremeasureFromLimit` | limit-to-premeasure route |

Suggested implementation order:

1. close `toOuterMeasure_Icc`,
2. close `borel_le_caratheodory`,
3. finish the `toIntervalPremeasure` block,
4. finish the spectral-measure block.

### 3.2. `Unbounded/StoneTheorem.lean` (1)

| Line | Theorem | Package role |
|---|---|---|
| 1781 | `timeEvolution_generator` | final unbounded Stone step |

This is the exposed tip of a larger unbounded spectral package. The real
project plan is in `docs/unbounded_spectral_project.md`. No one should treat
this as "just one local lemma."

### 3.3. `ModularTheory.lean` (6)

| Line | Theorem | Package role |
|---|---|---|
| 232 | `conjugates_modular_operator` | modular conjugation algebra |
| 247 | `reverses_modular_flow` | modular flow algebra |
| 282 | `tomita_fundamental` | central theorem |
| 303 | `modular_automorphism_preserves` | downstream corollary |
| 341 | `StandardForm.positiveCone_self_dual` | standard-form package |
| 361 | `standard_form_unique` | standard-form package |

Suggested implementation order:

1. `conjugates_modular_operator`,
2. `reverses_modular_flow`,
3. `tomita_fundamental`,
4. only then the standard-form theorems.

### 3.4. `ModularAutomorphism.lean` (6)

| Line | Theorem | Package role |
|---|---|---|
| 93 | `preserves_algebra` | earliest downstream theorem |
| 369 | `cocycle_in_algebra` | cocycle package |
| 380 | `cocycle_identity` | cocycle package |
| 436 | `modular_relation` | modular relation |
| 464 | `modular_inner_iff` | innerness criterion |
| 476 | `approximately_inner` | late corollary |

These should remain downstream of `ModularTheory.lean`. They are not the place
to repair Tomita theory itself.

### 3.5. `KMS.lean` (10)

| Line | Theorem | Package role |
|---|---|---|
| 99 | `modular_state_is_kms` | base KMS theorem |
| 102 | `modular_state_is_kms` | base KMS theorem |
| 109 | `modular_state_is_kms` | base KMS theorem |
| 127 | `kms_characterizes_modular` | converse theorem |
| 137 | `kms_is_equilibrium` | corollary |
| 149 | `kms_unique_for_factors` | corollary |
| 165 | `high_temperature_limit` | asymptotic theorem |
| 175 | `zero_temperature_limit` | asymptotic theorem |
| 211 | `kms_implies_passive` | consequence theorem |
| 254 | `passive_stable_implies_kms` | converse consequence |

These are late consumers. They should not be mixed back into foundational
modular proofs.

### 3.6. `Predual.lean` (2)

| Line | Theorem | Package role |
|---|---|---|
| 231 | `sigmaWeak_convergence_iff` | sigma-weak topology package |
| 246 | `kaplansky_density` | predual/operator-topology package |

These should stay last in the `vNA` execution order.

## 4. What is genuinely critical inside `vNA`

From a mathematical dependency standpoint:

1. `CaratheodoryExtension.lean` is the foundational measure package,
2. `timeEvolution_generator` is the real operator-theoretic bottleneck,
3. `tomita_fundamental` is the main modular bottleneck,
4. KMS and predual are downstream consumers.

So not all `36` sorries are equally urgent even within the `vNA` subtree.

## 5. Estimated implementation scale

These are rough but now useful estimates:

1. `CaratheodoryExtension.lean` cleanup:
   `180-320` Lean lines.
2. `timeEvolution_generator` plus supporting unbounded-spectral work:
   `250-450` Lean lines, with the real work spread across the spectral files.
3. `ModularTheory.lean` core:
   `180-320` Lean lines.
4. `ModularAutomorphism.lean`:
   `140-240` Lean lines.
5. `KMS.lean`:
   `200-360` Lean lines.
6. `Predual.lean`:
   `80-160` Lean lines.

## 6. What not to do

1. Do not start with KMS.
2. Do not start with `Predual.lean`.
3. Do not let `ModularAutomorphism.lean` rebuild Tomita theory.
4. Do not let `StoneTheorem.lean` quietly depend on unfinished measure
   extension results without documenting that dependency.

## 7. Route consequence for current OS work

This file exists so that operator-algebra work remains documented without
stealing focus from the live theorem-2/3/4 route. Unless the user explicitly
switches priorities, `vNA` should stay a documented side backlog rather than an
active frontier.
