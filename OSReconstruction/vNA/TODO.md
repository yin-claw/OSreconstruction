# vNA Module TODO

## Overview

This module develops von Neumann algebra foundations for rigorous QFT, including:
- Unbounded self-adjoint operators
- Spectral theory via Riesz-Markov-Kakutani (RMK)
- Stone's theorem for one-parameter unitary groups
- Modular theory (Tomita-Takesaki)

## Usage in the Main Proof Chain

The vNA module is consumed at two points in the OS reconstruction:

1. **`Wightman/OperatorDistribution.lean`** imports `vNA.Unbounded.StoneTheorem`
   - Stone's theorem defines momentum operators as generators of translation unitary groups
   - Used for the spectrum condition in `GNSHilbertSpace.lean`

2. **`Wightman/Reconstruction/WickRotation/OSToWightmanSemigroup.lean`** imports:
   - `vNA.Bochner.SemigroupRoots` — fractional semigroup root infrastructure
   - `vNA.Spectral.ComplexSemigroup` — complex spectral semigroup T(z) = e^{-zA}
   - `vNA.Spectral.SelfAdjointFunctionalViaRMK` — self-adjoint functional calculus
   - `vNA.Unbounded.BoundedBridge` — bounded↔unbounded operator bridge
   - Builds the contraction semigroup from OS data for the E→R direction

The modular theory chain (ModularTheory → ModularAutomorphism → KMS) is **not yet consumed**
by any reconstruction file — it is future infrastructure for Tomita-Takesaki applications.

## Current Status

### Spectral Theory via RMK (Primary Approach) — Sorry-Free Chain

| File | Status | Sorrys |
|------|--------|--------|
| `Spectral/SpectralFunctionalViaRMK.lean` | Complete | 0 |
| `Spectral/SpectralMeasurePolarizedViaRMK.lean` | Complete | 0 |
| `Spectral/SpectralTheoremViaRMK.lean` | Complete | 0 |
| `Spectral/CayleyTransform.lean` | Complete | 0 |
| `Spectral/SpectralViaCayleyRMK.lean` | Complete | 0 |
| `Spectral/SigmaAdditivity.lean` | Complete | 0 |
| `Spectral/SpectralProjectionLemmas.lean` | Complete | 0 |
| `Spectral/JensenLinearity.lean` | Complete | 0 |

### Unbounded Operators — Fully Proven

| File | Status | Sorrys |
|------|--------|--------|
| `Unbounded/Basic.lean` | Complete | 0 |
| `Unbounded/Graph.lean` | Complete | 0 |

### Measure Theory Infrastructure

| File | Status | Sorrys |
|------|--------|--------|
| `MeasureTheory/SpectralIntegral.lean` | Complete | 0 |
| `MeasureTheory/SpectralStieltjes.lean` | **Complete** | 0 |
| `MeasureTheory/CaratheodoryExtension.lean` | In Progress | ~16 (measure extension infrastructure) |

### Spectral Theorem & Functional Calculus — Sorry-Free

| File | Status | Sorrys |
|------|--------|--------|
| `Unbounded/Spectral.lean` | **Complete** | 0 |

**Sorry-free results:**
- `spectral_theorem_pvm`: PVM existence
- `spectral_theorem`: `⟨x, f(T)y⟩ = P.spectralIntegral f x y`
- `functionalCalculus_star`: `(f(T))* = f̄(T)`
- `functionalCalculus_mul`: `f(T)g(T) = (fg)(T)`
- `functionalCalculus_inner`: `⟨x, f(T)y⟩ = Bform P f x y`
- `unitaryGroup`: `U(t) = e^{itA} = ∫ exp(itλ) dP(λ)` — redefined using exp(itλ) directly
- `unitaryGroup_zero`: `U(0) = 1`
- `unitaryGroup_mul`: `U(s) ∘ U(t) = U(s+t)`
- `unitaryGroup_inv`: `U(t)* = U(-t)`
- `unitaryGroup_neg_comp`/`unitaryGroup_comp_neg`
- `unitaryGroup_continuous`: `t ↦ U(t)x` is continuous (DCT + weak→strong via isometry)
- `power` integrability/boundedness (uses `Re(s) = 0` hypothesis)

**Key change:** `unitaryGroup` no longer uses `power` (λ^{it}). It uses `exp(itλ)` directly,
which removes the positivity requirement and makes U(0)=1 trivially true.

### Spectral Powers — Isolated, Not on Critical Path

| File | Status | Sorrys |
|------|--------|--------|
| `Unbounded/SpectralPowers.lean` | Isolated | 2 |

- `power_zero` — requires spectral support argument: P((-∞,0]) = 0 for positive T
- `power_imaginary_unitary` — depends on `power_zero`

These are **not referenced** by any file outside `SpectralPowers.lean`. They were superseded
when `unitaryGroup` was redefined to use `exp(itλ)` directly.

### Stone's Theorem — Nearly Complete

| File | Status | Sorrys |
|------|--------|--------|
| `Unbounded/StoneTheorem.lean` | **Nearly Complete** | 1 |

**Sorry-free results (all major components):**
- `OneParameterUnitaryGroup` structure — definition with all axioms
- `generatorDomain`, `generatorApply` — infinitesimal generator on its natural domain
- `generator_densely_defined` — dom(A) is dense (mollification argument)
- `generator_symmetric` — ⟨Ax, y⟩ = ⟨x, Ay⟩ on dom(A)
- `generator_seq_closed` — the generator graph is sequentially closed
- `generator_U_mem` — U(t) preserves the generator domain
- `generator_U_commute` — U(t) commutes with the generator on its domain
- `generator_hasDerivAt` — d/dt U(t)x = iA·U(t)x for x ∈ dom(A)
- `generator_selfadjoint` — **fully proved** (~700 lines, deficiency-index argument)
- `generatorDomain_mem_of_commutes` — commuting operator preserves generator domain
- `generatorApply_commute_of_commutes` — commuting operator commutes with generator
- `unique_from_generator` — if 𝒰.generator = A then U(t) = exp(itA) (energy method)
- `Stone` — the main theorem: every strongly continuous one-parameter unitary group
  has a unique self-adjoint generator
- `timeEvolution` — forward direction (self-adjoint → unitary group)

**Remaining sorry (1):**
- `timeEvolution_generator` — generator of exp(-itH) is H. Convenience theorem,
  **not used** in the main proof chain.

### Complex Spectral Semigroup

| File | Status | Sorrys |
|------|--------|--------|
| `Spectral/ComplexSemigroup.lean` | In Progress | 2 |

- `spectralSemigroupComplex` semigroup law: T(s+t) = T(s)∘T(t)
- `Commute.spectralSemigroupComplex`: operators commuting with A commute with semigroup

Both are used by `OSToWightmanSemigroup.lean` in the E→R direction.

### von Neumann Algebra Basics

| File | Status | Sorrys |
|------|--------|--------|
| `Basic.lean` | **Complete** | 0 |
| `Predual.lean` | In Progress | 2 (`sigmaWeak_convergence_iff`, `kaplansky_density`) |

### Modular Theory — Future Infrastructure (Not Yet Used in Main Chain)

| File | Status | Sorrys |
|------|--------|--------|
| `ModularTheory.lean` | In Progress | 6 (Ω_in_domain, fixed point, JΔJ=Δ⁻¹, J reverses flow, σ_t preserves M, uniqueness) |
| `ModularAutomorphism.lean` | In Progress | 8 (preserves_algebra, multiplicativity, star, continuity, state_invariant, cocycle, Radon-Nikodym) |
| `KMS.lean` | In Progress | 10 (strip_boundary, modular_state_is_KMS, uniqueness, invariance, factor uniqueness, temperature limits, passivity) |

### Bochner Integration — Sorry-Free Helper Infrastructure

| File | Status | Sorrys |
|------|--------|--------|
| `Bochner/CfcInfrastructure.lean` | Complete | 0 |
| `Bochner/OperatorBochner.lean` | Complete | 0 |
| `Bochner/Convergence.lean` | Complete | 0 |
| `Bochner/FunctionalCalculusLinearity.lean` | Complete | 0 |
| `Bochner/Applications.lean` | Complete | 0 |

### Deprecated Files (moved to `/backup_deprecated_vNA/`)

The following files used `UnboundedCFC` which is broken for unbounded T
(returns 0 by Mathlib CFC convention). They have been moved out of the
source tree but backed up for reference:
- `TPConnection.lean` — T-P connection via UnboundedCFC
- `FunctionalCalculusFromCFC.lean` — spectral projections via CFC bump operators
- `FunctionalCalculusFromCFC/Basic.lean` — UnboundedCFC definition, proven infrastructure
- `SpectralIntegralCauchy.lean` — Cauchy sequence approach to spectral integrals

## Critical Issue: UnboundedCFC is Broken

**Problem**: `UnboundedCFC T f = cfc (cfcViaInverseCayley f) U` where U is the Cayley
transform. For unbounded T, `1 ∈ σ(U)` and `cfcViaInverseCayley f` is discontinuous
at 1 for most f (since `inverseCayley(w) → ∞` as `w → 1`). By Mathlib's CFC convention,
`cfc g U = 0` when g is not continuous on σ(U). Therefore `UnboundedCFC T f = 0` for most f.

**Fix**: Use `functionalCalculus P f` from `Unbounded/Spectral.lean` which is defined via
the sesquilinear form `Bform P f x y = polarized spectral integral`. This works correctly
for all bounded measurable f and does not depend on the Cayley transform.

## Action Plan

### ✅ Step 1: Fix SpectralMeasure definition — DONE
### ✅ Step 2: Complete σ-additivity — DONE
### ✅ Step 2.5: Refactor spectral_theorem (sorry-free PVM) — DONE
### ✅ Step 3: Prove spectral_theorem — DONE
### ✅ Step 4: Complete functionalCalculus properties — DONE
### ✅ Step 5: Stone's Theorem — Forward Direction — DONE
### ✅ Step 6: Stone's Theorem — Inverse Direction — DONE

`generator_selfadjoint` is fully proved via the deficiency-index argument:
1. Generator is symmetric (limit manipulation with U(t)* = U(-t))
2. ker(A* ± iI) = {0} (ODE uniqueness: exp(±t)·‖w‖ bounded contradicts growth)
3. ran(A - iI) is closed (bounded-below + sequential closedness)
4. ran(A - iI) = H (closed + trivial orthogonal complement)
5. dom(A*) ⊆ dom(A) (surjectivity of A-iI maps A* elements back to A domain)

`unique_from_generator` proved via energy method (‖V(t)x - U(t)x‖² has zero derivative).
`Stone` assembles all pieces.

## Full Module Dependency Chart

```
Spectral Theory (sorry-free chain)
│
│  SpectralFunctionalViaRMK ✅
│  SpectralMeasurePolarizedViaRMK ✅
│  SpectralTheoremViaRMK ✅
│  CayleyTransform ✅ → SpectralViaCayleyRMK ✅ → SigmaAdditivity ✅
│  SpectralProjectionLemmas ✅, JensenLinearity ✅
│
├── MeasureTheory
│   ├── SpectralIntegral ✅
│   ├── SpectralStieltjes ✅
│   └── CaratheodoryExtension (~16 sorrys, measure extension infrastructure)
│
├── Unbounded Operators
│   ├── Basic ✅, Graph ✅
│   ├── Spectral ✅ (fully sorry-free)
│   ├── SpectralPowers (2 sorrys: power_zero, power_imaginary_unitary — isolated, not used)
│   └── StoneTheorem ✅ (1 sorry: timeEvolution_generator — not used in main chain)
│       │
│       ▼
├── Modular Theory (future infrastructure, not yet consumed by reconstruction)
│   ├── Basic ✅
│   ├── Predual (2 sorrys: sigmaWeak_convergence_iff, kaplansky_density)
│   ├── ModularTheory (6 sorrys: Ω_in_domain, fixed point, JΔJ=Δ⁻¹, J reverses flow,
│   │                            σ_t preserves M, uniqueness)
│   ├── ModularAutomorphism (8 sorrys: preserves_algebra, multiplicativity, star,
│   │                        continuity, state_invariant, cocycle, Radon-Nikodym)
│   └── KMS (10 sorrys: strip_boundary, modular_state_is_KMS, uniqueness,
│            invariance, factor uniqueness, temperature limits, passivity)
│
├── Complex Spectral Semigroup (used by OSToWightmanSemigroup)
│   └── ComplexSemigroup (2 sorrys: semigroup law, commutativity)
│
└── Bochner Integration (sorry-free helper infrastructure)
    ├── CfcInfrastructure ✅
    ├── OperatorBochner ✅
    ├── Convergence ✅
    ├── FunctionalCalculusLinearity ✅
    └── Applications ✅
```

### Critical Chain for Main Proof

```
Spectral (sorry-free) → StoneTheorem ✅ → OperatorDistribution (momentum operators)
                                        → GNSHilbertSpace (spectrum condition — 1 sorry)

ComplexSemigroup (2 sorrys) → OSToWightmanSemigroup (E→R contraction semigroup)
```

Stone's theorem is no longer a bottleneck. The remaining sorry (`timeEvolution_generator`)
is not on the critical path.

### Parallel Work Streams

- **Group A** (spectral powers): power_zero + power_imaginary_unitary (isolated, 2 sorrys, not used)
- **Group B** (complex semigroup): semigroup law + commutativity (2 sorrys, used by E→R)
- **Group C** (measure theory): CaratheodoryExtension sorrys (~16, infrastructure)
- **Group D** (modular theory): 26 sorrys, future infrastructure not yet consumed

Groups A, B, C, and D are all independent of each other.

## Difficulty Assessment and Formalization Effort

### Critical Path (2 sorries) — Easy

| Sorry | Difficulty | Est. effort | Key insight |
|-------|-----------|-------------|-------------|
| `spectralSemigroupComplex_ofReal_add` | Easy | ~1-2 weeks | CFC multiplicativity: λ^{s+t} = λ^s · λ^t |
| `Commute.spectralSemigroupComplex` | Easy | ~1 week | `Commute.cfc` in Mathlib handles this |

Both are straightforward CFC algebraic identities. All required Mathlib infrastructure exists.

**`spectralSemigroupComplex_ofReal_add`** (ComplexSemigroup.lean:392):
T(s+t) = T(s) ∘ T(t) for real s, t > 0. The key identity is λ^{s+t} = λ^s · λ^t for λ ∈ [0,1].
Since T(z) = cfc(fRe_z, A) + I·cfc(fIm_z, A), this reduces to:
- `cfc(f_{s+t}) = cfc(f_s · f_t)` by pointwise identity of the functions
- `cfc(f_s) ∘ cfc(f_t) = cfc(f_s · f_t)` by CFC homomorphism (`cfc_mul`)
The subtlety is decomposing the complex product into real/imaginary parts and recombining.

**`Commute.spectralSemigroupComplex`** (ComplexSemigroup.lean:404):
If B commutes with A, then B commutes with T(z). Since T(z) = cfc(fRe, A) + I·cfc(fIm, A),
and Mathlib provides `Commute.cfc` (B commutes with A implies B commutes with cfc(f, A)),
commutativity with each piece follows directly, and sums/scalar multiples preserve commutativity.

### Off Critical Path — Grouped by Difficulty

| Group | Sorries | Difficulty | Est. effort | Notes |
|-------|---------|-----------|-------------|-------|
| B: Complex semigroup | 2 | **Easy** | 2-3 weeks | **On critical path** — see above |
| A: Spectral powers | 2 | Medium | 1-2 months | Isolated, superseded by exp(itλ) approach |
| C: Caratheodory extension | ~16 | Medium | 2-3 months | Measure extension infrastructure |
| D: Modular theory | 26 | Hard | 6-12 months | Deep Tomita-Takesaki theory |

**Group A** (`SpectralPowers.lean`): `power_zero` needs a spectral support argument
(P((-∞,0]) = 0 for positive T). `power_imaginary_unitary` depends on it. Both are superseded —
`unitaryGroup` now uses exp(itλ) directly.

**Group C** (`CaratheodoryExtension.lean`): Standard measure extension from premeasures on intervals.
Mathlib has `MeasureTheory.OuterMeasure.caratheodory` but the bridge from interval premeasures to
Borel σ-algebra needs manual work. Medium difficulty, no conceptual obstacles.

**Group D** (ModularTheory + ModularAutomorphism + KMS): Deep functional analysis — Tomita-Takesaki
modular theory, Connes cocycle, KMS states. These are future infrastructure for thermal QFT
applications. The 26 sorries span fundamental results like σ_t preserving M (requires the full
Tomita-Takesaki theorem), Connes' Radon-Nikodym theorem, and KMS uniqueness for factor states.
Each is a significant theorem in its own right. Not consumed by any reconstruction file.

### Priority Ordering

1. **`spectralSemigroupComplex_ofReal_add`** + **`Commute.spectralSemigroupComplex`** — on critical
   path, easy, should be done first (~2-3 weeks)
2. **CaratheodoryExtension** — useful infrastructure, medium difficulty (~2-3 months)
3. **SpectralPowers** — isolated, low priority
4. **Modular theory chain** — future infrastructure, not yet consumed

## Sorry Summary by File

| File | Sorrys | Category | On critical path? |
|------|--------|----------|-------------------|
| `Unbounded/Spectral.lean` | 0 | — | — |
| `Unbounded/StoneTheorem.lean` | 1 | `timeEvolution_generator` | **No** |
| `Unbounded/SpectralPowers.lean` | 2 | power_zero + power_imaginary_unitary | **No** (isolated) |
| `Spectral/ComplexSemigroup.lean` | 2 | Semigroup law + commutativity | **Yes** (E→R) |
| `MeasureTheory/SpectralStieltjes.lean` | 0 | — | — |
| `MeasureTheory/CaratheodoryExtension.lean` | ~16 | Measure extension infrastructure | No |
| `Basic.lean` | 0 | — | — |
| `Predual.lean` | 2 | σ-weak topology + Kaplansky density | No (modular) |
| `ModularTheory.lean` | 6 | Tomita-Takesaki fundamentals | No (future) |
| `ModularAutomorphism.lean` | 8 | Automorphism group + Connes cocycle | No (future) |
| `KMS.lean` | 10 | KMS states + passivity | No (future) |
| **Total** | **~47** | | **2 on critical path** |

### Sorry-Free Key Results
- `spectral_theorem_pvm`: PVM existence
- `spectral_theorem`: spectral representation ⟨x, f(T)y⟩ = ∫ f d⟨x, P y⟩
- `functionalCalculus_star`: (f(T))* = f̄(T)
- `functionalCalculus_mul`: f(T)g(T) = (fg)(T)
- `functionalCalculus_inner`: ⟨x, f(T)y⟩ = Bform P f x y
- `unitaryGroup_zero`: U(0) = 1
- `unitaryGroup_mul`: U(s)U(t) = U(s+t)
- `unitaryGroup_inv`: U(t)* = U(-t)
- `unitaryGroup_continuous`: t ↦ U(t)x is continuous (DCT + weak→strong)
- `generator_selfadjoint`: generator of SCOUP is self-adjoint
- `Stone`: every SCOUP has a unique self-adjoint generator
- `UnboundedOperator.spectralMeasure`: spectral measure definition
- `UnboundedOperator.spectralCayley`: Cayley transform definition
- `UnboundedOperator.spectralMeasure_eq_RMK`: agreement with RMK

## What NOT to Pursue

All deprecated files have been moved to `/backup_deprecated_vNA/`:
- **UnboundedCFC**: Broken for unbounded T (returns 0)
- **CFC approach**: Superseded by sesquilinear form
- **TP_connection**: Used broken UnboundedCFC

## Key Technical Notes

### Why RMK?

The traditional approach creates circularity:
1. CFC for bounded normal operators → spectral projections
2. Cayley transform to reduce unbounded to bounded
3. But CFC itself uses spectral theory

The RMK approach breaks this by:
1. Defining spectral functional Λ_z(f) = Re⟨z, cfc(f, U) z⟩
2. Using RMK to get a measure μ_z from Λ_z
3. Extending to polarized measure μ_{x,y} via polarization
4. Defining P(E) via sesquilinear form: ⟨x, P(E) y⟩ = μ_{x,y}(E)

### Why Sesquilinear Form for Functional Calculus?

The `functionalCalculus P f` is defined via:
1. Diagonal measure: `μ_z(E) = ‖P(E)z‖²`
2. Quadratic form: `Q(z) = ∫ f dμ_z`
3. Polarization: `B(x,y) = (1/4)[Q(x+y) - Q(x-y) - iQ(x+iy) + iQ(x-iy)]`
4. Riesz representation: unique T with `⟨x, Ty⟩ = B(x,y)` (sesquilinearToOperator)

This works for ALL bounded measurable f and ANY self-adjoint operator (bounded or unbounded).

### Key Lemmas Available (Sorry-Free)

**From RMK chain:**
- `spectralFunctionalAux_tendsto_of_pointwise_general`: Dominated convergence
- `spectralProjection_polarized_product_closed`: P(E)P(F) product formula
- `spectralProjection_idempotent_closed`: P(F)² = P(F)
- `spectralMeasurePolarized_univ`: μ_{x,y}(Circle) = ⟨x, y⟩
- `spectralMeasurePolarized_integral`: U-P connection for compactly supported
- `one_not_eigenvalue`: U x = x ⟹ x = 0

**From TPConnection.lean:**
- `spectralMeasureDiagonalOnR`: Pullback measure on ℝ
- `TP_connection_indicator`: ⟨x, P(E) y⟩ = μ^ℝ_{x,y}(E)
- `spectralMeasureDiagonal_singleton_one_eq_zero`: μ_z({1}) = 0
- `integral_circle_eq_integral_minus_one`: ∫ g dμ = ∫_{Circle\{1}} g dμ

## References

- Reed-Simon, "Methods of Modern Mathematical Physics I", Ch. VII-VIII
- Rudin, "Functional Analysis", Ch. 13
- Kato, "Perturbation Theory for Linear Operators", Ch. V
