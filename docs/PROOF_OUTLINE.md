# Osterwalder-Schrader Reconstruction: Formal Proof Outline

> Status note (2026-02-27, tightened 2026-04-08): this file mixes historical
> snapshots with useful structural explanations. Do **not** use it as the live
> blocker ledger or current file map unless a section explicitly says it has been
> resynced. For current blocker status and checked file ownership, use
> `docs/development_plan_systematic.md`, `docs/proof_docs_completion_plan.md`,
> `docs/theorem2_locality_blueprint.md`,
> `docs/theorem3_os_route_blueprint.md`,
> `docs/theorem4_cluster_blueprint.md`, and
> `OSReconstruction/Wightman/TODO.md`.

A complete outline of the Lean 4 formalization of the OS reconstruction theorems,
mapping the mathematical proof structure to the codebase.

## Table of Contents

1. [Overview](#overview)
2. [Layer 0: Foundations](#layer-0-foundations)
3. [Layer 1: Axiom Systems](#layer-1-axiom-systems)
4. [Layer 2: GNS Construction](#layer-2-gns-construction)
5. [Layer 3: Complex Analysis Infrastructure](#layer-3-complex-analysis-infrastructure)
6. [Layer 4: Analytic Continuation](#layer-4-analytic-continuation)
7. [Layer 5: Wick Rotation Bridge](#layer-5-wick-rotation-bridge)
8. [Layer 6: Main Reconstruction Theorems](#layer-6-main-reconstruction-theorems)
9. [Dependency Graph](#dependency-graph)
10. [Sorry Census](#sorry-census)
11. [Mathematical References](#mathematical-references)

---

## Overview

The project formalizes the **Osterwalder-Schrader reconstruction theorems** in Lean 4,
establishing the mathematical equivalence between:

- **Wightman QFT** (Lorentzian, operator-valued distributions on Minkowski space)
- **Euclidean QFT** (Schwinger functions satisfying the OS axioms)

The proof proceeds in two directions:

| Direction | Theorem | Method |
|-----------|---------|--------|
| **R → E** (Wightman → OS) | `wightman_to_os` | Wick rotation t → it, verify E0–E4 |
| **E → R** (OS → Wightman) | `os_to_wightman` | Analytic continuation back to Minkowski, GNS construction |

**Current status:** the numerical counts in this file are historical and should
not be used operationally. The live production ledger now tracks a `63`-sorry /
`6`-axiom theorem-2/3/4 frontier in the split production tree, plus a separate
checked secondary `Wightman/NuclearSpaces/*` lane with 7 local `sorry`s kept
outside that headline count. Infrastructure layers described below remain useful
context, but the actual implementation surface is no longer the old monolithic
`WickRotation.lean` story. In particular, the active `E -> R` route now runs
through the split file family
`OSToWightmanSemigroup.lean -> OStoWightman.lean -> OStoWightmanPositivity.lean
-> OStoWightmanBoundaryValuesBase.lean -> OStoWightmanBoundaryValueLimits.lean
-> OStoWightmanBoundaryValuesComparison.lean -> OStoWightmanBoundaryValues.lean`,
and theorem-level work should be planned against those file contracts rather
than against the historical monolith below.

---

## Layer 0: Foundations

All files in this layer are **sorry-free**.

### Spacetime/Metric.lean — Minkowski metric

Defines (d+1)-dimensional Minkowski space with mostly-positive signature η = diag(−1,+1,…,+1).

| Definition/Theorem | Description |
|---|---|
| `MinkowskiSpace d` | Type alias `Fin (d+1) → ℝ` |
| `metricSignature` | η_μ: returns −1 for μ=0, +1 for μ≥1 |
| `minkowskiInner` | Indefinite inner product η(x,y) = Σ_μ η_μ x_μ y_μ |
| `minkowskiNormSq` | Quadratic form η(x,x) |
| `metricSignature_sq` | η_μ² = 1 |

### Spacetime/MinkowskiGeometry.lean — Geometric lemmas

Component decomposition and Cauchy-Schwarz for spatial parts.

| Definition/Theorem | Description |
|---|---|
| `spatialNormSq` | Σ_{i≥1} x_i² |
| `minkowskiInner_decomp` | η(x,y) = −x₀y₀ + Σ x_i y_i |
| `timelike_time_dominates_space` | IsTimelike x → x₀² > Σ x_i² |
| `spatial_cauchy_schwarz` | Cauchy-Schwarz for spatial components |

### Groups/Lorentz.lean — connected Lorentz group SO⁺(1,d) and full O(1,d)

| Definition/Theorem | Description |
|---|---|
| `IsLorentzMatrix` | Λᵀ η Λ = η |
| `IsLorentzMatrix.mul` | Closure under multiplication |
| `IsLorentzMatrix.isUnit` | det(Λ) = ±1 |
| `IsLorentzMatrix.inv_eq` | Λ⁻¹ = η Λᵀ η |

### Groups/Poincare.lean — connected Poincare group ISO⁺(1,d) and full ISO(1,d)

| Definition/Theorem | Description |
|---|---|
| `PoincareGroup d` | Pairs (a, Λ) with semidirect product |
| `PoincareGroup.Mul` | (a₁,Λ₁)·(a₂,Λ₂) = (a₁+Λ₁a₂, Λ₁Λ₂) |
| `PoincareGroup.Inv` | (a,Λ)⁻¹ = (−Λ⁻¹a, Λ⁻¹) |

### Basic.lean — Re-exports

Aggregates MinkowskiSpace, lightcone definitions (`ForwardLightCone`, `IsSpacelike`, etc.),
and dimension conventions.

### SchwartzTensorProduct.lean — Schwartz space tensor products

External tensor product of Schwartz functions, essential for multi-point distributions.

| Definition/Theorem | Description |
|---|---|
| `SchwartzMap.conj` | Complex conjugation on Schwartz space |
| `SchwartzMap.reverse` | Argument reversal for n-point functions |
| `SchwartzMap.tensorProduct` | f ⊗ g ∈ S(ℝ^{(m+k)d}) |
| `SchwartzMap.conj_conj` | Conjugation is an involution |

---

## Layer 1: Axiom Systems

### WightmanAxioms.lean — Wightman axioms W0–W4 (2 downstream axiom surfaces)

Complete axiomatization of relativistic QFT in the Wightman framework.

**Structure `WightmanQFT d`:**

| Axiom | Field | Description |
|-------|-------|-------------|
| W0 | `hilbertSpace`, `poincareRep` | Hilbert space with unitary Poincare representation |
| W1 | `spectrumCondition` | Energy-momentum spectrum in forward cone |
| W2 | `vacuum`, `vacuumInvariant` | Unique Poincare-invariant vacuum Ω |
| W3 | `fieldOperator`, `fieldSmeared` | Operator-valued distributions φ(f) |
| W4 | `locality` | [φ(f), φ(g)] = 0 for spacelike-separated supports |

**Key definitions:**
- `wightmanFunction n` — n-point function W_n(f₁,…,f_n) = ⟨Ω, φ(f₁)···φ(f_n)Ω⟩
- `ForwardTube n` — current repo forward tube for the public literal `n`-point
  family: an absolute-coordinate tube with `Im(z₀) ∈ V₊` and
  `Im(z_k - z_{k-1}) ∈ V₊` for `k ≥ 1`; this is slightly stronger than the
  minimal standard literal `n`-point tube
- `ExtendedForwardTube n` — T'_n = ∪_Λ Λ·T_n (complex Lorentz orbit)

**Current downstream axiom / bridge surfaces:**
- `schwartz_nuclear_extension` — downstream reconstruction-facing package for the nuclear-extension route; the supporting mathematics may live in the checked `Wightman/NuclearSpaces/*` subtree and/or imported `gaussian-field` results, but GNS-side consumers should treat this exported `WightmanAxioms.lean` surface as the contract point
- `exists_continuousMultilinear_ofSeparatelyContinuous` — downstream reconstruction-facing package for the separate-to-joint continuity route; again, local NuclearSpaces work, imported support, and exported consumer surface must stay distinct in the docs and later Lean implementation

So the implementation contract here is three-layered, not "WightmanAxioms only" and not "NuclearSpaces only":
1. checked local support files under `Wightman/NuclearSpaces/*`,
2. optional bridge/import packaging,
3. downstream exported theorem surfaces in `Wightman/WightmanAxioms.lean` consumed by `GNSHilbertSpace.lean`.

### OS Axioms (historically described under `WickRotation.lean`; now consumed via the split Wick-rotation family)

The Euclidean axiom system, encoded as the `IsOsterwalderSchrader` structure:

Implementation caution (current tree): this section is about the mathematical
surface, not a claim that one checked file named `WickRotation.lean` still owns
all production proof work. In the current repo the OS -> Wightman route is split
across the `OSToWightman*` family listed above, and theorem-2/3/4 work must be
attached to those explicit file owners rather than to the historical monolith.

| Axiom | Field | Description |
|-------|-------|-------------|
| E0 | `tempered` | Schwinger functions are tempered distributions |
| E0' | `linear_growth` | Linear growth bound (OS II refinement) |
| E1 | `euclidean_covariant` | SO(d+1) covariance |
| E2 | `reflection_positive` | θ-positivity: S(θf, f) ≥ 0 |
| E3 | `symmetric` | Permutation symmetry of arguments |
| E4 | `cluster` | Cluster decomposition |

---

## Layer 2: GNS Construction

### GNSConstruction.lean — Sorry-free

The Gelfand-Naimark-Segal construction, building a Hilbert space from Wightman functions.

**Mathematical content:** Given Wightman functions {W_n} satisfying positivity (W0+),
construct:
1. A pre-inner product space from formal polynomials in test functions
2. A vacuum vector Ω
3. Field operators φ(f) acting on the space

| Theorem | Line | Description |
|---------|------|-------------|
| `WightmanInnerProduct_hermitian` | 596 | ⟨F,G⟩ = conj(⟨G,F⟩) |
| `null_inner_product_zero` | 660 | ⟨X,X⟩.re = 0 → ⟨X,Y⟩ = 0 for all Y |
| `fieldOperator_well_defined` | ~1000 | φ(f) descends to quotient |
| `gns_reproduces_wightman` | 220 | ⟨Ω, φ(f₁)···φ(f_n)Ω⟩ = W_n(f₁⊗···⊗f_n) |
| `translation_preserves_inner` | 277 | Translation covariance of inner product |

**Proof strategy for `null_inner_product_zero`:**
The key step uses the quadratic positivity argument: if ⟨X,X⟩.re = 0,
then for any Y and scalar λ, positivity of ⟨X+λY, X+λY⟩ forces ⟨X,Y⟩ = 0.

**Proof strategy for `fieldOperator_well_defined`:**
Chain: adjoint relation → φ(f) preserves null space → well-defined on quotient.

---

## Layer 3: Complex Analysis Infrastructure

### Helpers/EdgeOfWedge.lean — Sorry-free

The 1-dimensional edge-of-the-wedge theorem, serving as the base case for induction.

**Theorem `edge_of_the_wedge_1d`** (line 112):

> If f₊ is holomorphic on the upper half-plane, f₋ on the lower half-plane,
> both extend continuously to ℝ, and f₊|_ℝ = f₋|_ℝ, then the glued function
> is entire (holomorphic on all of ℂ).

**Proof method:** Define the glued function g on ℂ, then verify holomorphicity using
**Morera's theorem** (vanishing of contour integrals over triangles) combined with
the **Cauchy-Goursat theorem** for triangles that cross the real axis.

Additional results:
- `identity_theorem_connected` — Analytic identity theorem on connected domains
- `holomorphic_translation_invariant` — Translation-invariant holomorphic functions are constant

### Helpers/SeparatelyAnalytic.lean — Sorry-free

Osgood's lemma and related results for separately holomorphic functions.

#### Proven results:

**Osgood's Lemma** (`osgood_lemma`, line 540):

> A separately holomorphic function f : (Fin m → ℂ) → ℂ that is continuous
> is jointly holomorphic.

**Proof method (for `osgood_lemma_prod`, line 413):**
Direct construction of the Frechet derivative. Given f : ℂ × E → ℂ continuous
and holomorphic in each variable separately:
1. The candidate derivative is `D f(z,x)(h,k) = ∂_z f · h + ∂_x f · k`
2. Decompose the remainder into three terms:
   - T₁: Taylor remainder in z (controlled by `taylor_remainder_single`)
   - T₂: Derivative variation in x (controlled by `continuousAt_deriv_of_continuousOn`)
   - T₃: Frechet remainder in x (controlled by differentiability in x)
3. Each term is o(‖(h,k)‖), giving `HasFDerivAt`

**Induction step** (`osgood_lemma`, line 540): Reduce `Fin (m+1) → ℂ` to `ℂ × (Fin m → ℂ)`
using `osgood_lemma_prod` and the inductive hypothesis.

**Taylor remainder helpers** (all proven):

| Helper | Line | Description |
|--------|------|-------------|
| `cauchyPowerSeries_one_eq_deriv_mul` | 99 | p₁(h) = (deriv g z₀) · h |
| `tsum_geometric_tail_le` | 116 | Σ_{n≥2} M·r^n ≤ 2M·r² for r < 1/2 |
| `cauchyPowerSeries_coeff_bound` | 133 | ‖p_n(h,…,h)‖ ≤ M·(‖h‖/ρ)^n via Cauchy estimates |
| `taylor_remainder_eq_tsum` | 181 | g(z₀+h) − g(z₀) − g'(z₀)h = Σ_{n≥2} p_n(h) |
| `taylor_tail_summable` | 215 | Tail series is summable for ‖h‖ < ρ |
| `taylor_tail_norm_le` | 234 | ‖Σ_{n≥2} p_n(h)‖ ≤ 4M/ρ² · ‖h‖² for ‖h‖ < ρ/2 |
| `taylor_remainder_single` | 276 | Combines above: remainder is O(‖h‖²) |
| `uniform_bound_near_point` | 288 | Compact slice → uniform bound near any point |
| `taylor_remainder_bound` | 386 | Final estimate for Osgood proof |

**Holomorphic extension** (proven):
- `holomorphic_extension_across_real` (line 815) — Multi-D extension across real hyperplane
- `tube_domain_gluing` (line 895) — Gluing holomorphic functions on opposite tubes

**Cauchy integral with holomorphic parameter** (`differentiableOn_cauchyIntegral_param`, line 975):

> If f(ζ, x) is jointly continuous and holomorphic in x for each ζ,
> then G(z, x) = (2πi)⁻¹ ∮ f(ζ, x)/(ζ − z) dζ is jointly holomorphic.

**Proof method:** Combine `osgood_lemma` with parametric differentiation under the integral:
1. Transfer to coordinates via a linear equiv φ : E ≃L[ℂ] (Fin n → ℂ)
2. Apply `osgood_lemma` to the bare integral H(y) = ∮ (ζ−z)⁻¹ f(ζ, φ⁻¹y) dζ
   (without the (2πi)⁻¹ factor, to avoid kernel `isDefEq` timeout)
3. Per-coordinate differentiability via `differentiableAt_circleIntegral_param_coord`,
   which uses the Leibniz rule (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`)
   with an explicit derivative parameter `(F' := ...)`
4. Scale by (2πi)⁻¹ via `DifferentiableOn.const_smul` at the `suffices` level

**Continuity of z-derivative** (`continuousAt_deriv_of_continuousOn`, line 68):

> If f(z, x) is jointly continuous and holomorphic in z, then
> x ↦ ∂_z f(z₀, x) is continuous.

**Proof method:** Express the derivative via the Cauchy integral formula
(cderiv at radius ρ/2), then use a tube lemma argument for uniform control
of |f(w, x) − f(w, x₀)| on the integration circle.

---

## Layer 4: Analytic Continuation

### AnalyticContinuation.lean — 2 named axioms (0 sorrys)

Tube domain geometry and the key theorems of axiomatic QFT.

#### Proven results:

**Complex Lorentz group embeddings:**
- `ComplexLorentzGroup.ofReal` (line 104) — Real Lorentz ↪ Complex Lorentz
- `ComplexLorentzGroup.ofEuclidean` (line 142) — Euclidean SO(d+1) ↪ Complex Lorentz via Wick rotation

**Tube domain inclusions:**
- `ForwardTube_subset_ComplexExtended` (line 265) — T_n ⊂ T'_n
- `ComplexExtended_subset_Permuted` (line 283) — T'_n ⊂ T''_n

**Euclidean point geometry:**
- `euclidean_ordered_in_forwardTube` (line 322) — Ordered Euclidean points (τ₁ > τ₂ > ⋯) lie in the forward tube T_n
- `euclidean_distinct_in_permutedTube` (line 392) — Distinct Euclidean points lie in the permuted extended tube T''_n (uses sorting permutation)

**Jost's Lemma** (`jost_lemma`, line 545):
> At "Jost points" (certain real boundary points of the extended tube),
> all difference vectors are spacelike.

**Schwinger function analyticity:**
- `schwingerFromWightman_analytic` — Analytic on tube domain
- `differentiable_complexWickRotate` — Wick rotation is holomorphic
- `schwinger_euclidean_invariant` — Euclidean invariance of Schwinger functions
- `schwinger_permutation_symmetric` — Permutation symmetry at Jost points

#### ~~Named axiom~~ Proved theorem: `edge_of_the_wedge`

**Multi-dimensional edge-of-the-wedge theorem (Bogoliubov):**

> If F₊ is holomorphic on ℝⁿ + iΓ and F₋ is holomorphic on ℝⁿ − iΓ
> (where Γ is an open convex cone), and their continuous boundary values agree,
> then they extend to a single holomorphic function on a complex neighborhood of ℝⁿ.

**NOW PROVED** (no longer an axiom). The full multi-dimensional theorem is proved
in `SCV/TubeDomainExtension.lean` as `edge_of_the_wedge_theorem`, and
`AnalyticContinuation.lean` delegates to it. The proof uses iterated Cauchy
integrals and Osgood's lemma, all formalized in the `SCV/` module.

#### Named axiom: `bargmann_hall_wightman`

**Bargmann-Hall-Wightman theorem:**

> A holomorphic function on the forward tube T_n that is invariant under the
> (real) restricted Lorentz group extends holomorphically to the permuted
> extended tube T''_n, and the extension is invariant under permutations.

Promoted to a named axiom (no `sorryAx`). The proof requires connectedness of
SO⁺(1,d;ℂ), the identity theorem on complex manifolds, and holomorphicity of the
group action — none of which are available in Mathlib (~1200-1700 LOC to formalize).
See [BHW status](BHW_STATUS.md) for current details.

---

## Layer 5: Wick Rotation Bridge

### Historical monolith view: `WickRotation.lean — 17 sorrys`

This section is preserved as a historical blueprint for the mathematical route,
not as the live file/blocker map. In the checked production tree, the work once
lumped into `WickRotation.lean` has been split across the `BHW*`,
`OSToWightman*`, `SchwingerTemperedness.lean`, and related support files. Read
all count statements and sorry numbers in this section as historical labels
unless they are restated in the canonical live docs.

The heart of the reconstruction: translating between Wightman and OS axioms.

#### R → E Direction: `constructedSchwinger_*` (sorrys #3–7)

Given Wightman functions {W_n}, define Schwinger functions S_n by Wick rotation
and verify the OS axioms.

| Sorry | Theorem | OS Axiom | Proof idea |
|-------|---------|----------|------------|
| #3 | `constructedSchwinger_tempered` | E0 | Polynomial growth of W_analytic × Schwartz decay |
| #4 | `constructedSchwinger_euclidean_covariant` | E1 | Change of variables + complex Lorentz invariance |
| #5 | `constructedSchwinger_reflection_positive` | E2 | Borchers involution + Wightman positivity |
| #6 | `constructedSchwinger_symmetric` | E3 | BHW permutation symmetry (needs #2) |
| #7 | `constructedSchwinger_cluster` | E4 | Propagate Wightman cluster through Wick rotation |

**Already proven:** `wightman_to_os_full` (line 385) — Top-level wiring assuming the above.

#### E → R Direction: Analytic Continuation Chain (sorrys #8–10)

The reverse direction, following Osterwalder-Schrader II (1975).

| Sorry | Theorem | Reference | Description |
|-------|---------|-----------|-------------|
| #8 | `inductive_analytic_continuation` | OS II Thm 4.1 | One step: C_k^(r) → C_k^(r+1) |
| #9 | `full_analytic_continuation` | OS II §V | Iterate d+1 times to reach forward tube |
| #10 | `boundary_values_tempered` | OS II §VI | Tempered boundary values with factorial growth |

**Proof idea for #8:** The Schwinger functions, restricted to the half-space
τ₁ > τ₂ > ⋯ > 0, have a Laplace transform representation (from E0' linear growth).
Each inductive step analytically continues one time variable τ_r → complex,
using Hartogs' theorem and the tube lemma.

**Proof idea for #10:** The linear growth condition E0' (strengthening of E0)
provides polynomial bounds that are preserved through the analytic continuation chain,
yielding tempered distributional boundary values on the real Minkowski boundary.

#### Constructing Wightman Functions (sorrys #11–17)

Given the analytic continuation to the forward tube, extract the 7 Wightman axiom fields.

| Sorry | Field | Derived from | Notes |
|-------|-------|-------------|-------|
| #11 | `normalized` | S₀ = 1 | W₀ = 1 from normalization |
| #12 | `translation_invariant` | E1 | Euclidean translation → Minkowski translation |
| #13 | `lorentz_covariant` | E1 + BHW | SO(d+1) covariance → Lorentz covariance via BHW |
| #14 | `spectrum_condition` | E0' | Laplace transform → support in forward cone |
| #15 | `locally_commutative` | E3 + EOW | Permutation symmetry + edge-of-wedge → locality |
| #16 | `positive_definite` | E2 | Reflection positivity → Wightman positivity |
| #17 | `hermitian` | Reality | Real Schwinger functions → Hermiticity |

#### E → R Wiring (sorry #18)

| Sorry | Theorem | Description |
|-------|---------|-------------|
| #18 | `os_to_wightman_full` (line 415) | Wire `constructWightmanFunctions` into `IsWickRotationPair` |

---

## Layer 6: Main Reconstruction Theorems

### Reconstruction.lean — 4 sorrys

The top-level theorems that the entire development builds toward.

#### Sorry #19: `wightman_reconstruction` (line 1028)

**Wightman Reconstruction Theorem:**

> Given a sequence of Wightman functions {W_n} satisfying axioms W0–W4,
> there exists a Wightman QFT (H, U, Ω, φ) whose n-point functions
> reproduce the given W_n.

**Proof:** Apply the GNS construction (Layer 2, complete) to build H, Ω, φ.
Verify each axiom using the properties proven in GNSConstruction.lean.
The remaining work is primarily wiring.

#### Sorry #20: `wightman_uniqueness` (line 1053)

**Uniqueness (up to unitary equivalence):**

> Any two Wightman QFTs with the same n-point functions are unitarily equivalent.

**Proof:** Standard GNS uniqueness: the map φ₁(f₁)···φ₁(f_n)Ω₁ ↦ φ₂(f₁)···φ₂(f_n)Ω₂
is well-defined (by equality of inner products), isometric, and intertwines field operators.

#### Sorry #21: `wightman_to_os` (line 1220)

**R → E direction:**

> Wightman QFT → Schwinger functions satisfying OS axioms.

**Proof:** Wire to `wightman_to_os_full` (already proven in WickRotation.lean),
pending completion of `constructedSchwinger_*` theorems (#3–7).

#### Sorry #22: `os_to_wightman` (line 1251)

**E → R direction:**

> OS axioms + linear growth E0' → Wightman QFT.

**Proof:** Wire to `os_to_wightman_full` (#18), which depends on the full
E→R analytic continuation chain (#8–10) and axiom extraction (#11–17).

---

## Dependency Graph

```
Layer 0: Foundations (all sorry-free)
  Metric.lean ← MinkowskiGeometry.lean
  Lorentz.lean ← Poincare.lean
  SchwartzTensorProduct.lean

Layer 1: Axioms
  WightmanAxioms.lean (2 sorrys, non-blocking)

Layer 2: GNS (sorry-free)
  GNSConstruction.lean

Layer 3: Complex Analysis (all sorry-free)
  EdgeOfWedge.lean
  SeparatelyAnalytic.lean
       │
       ├── osgood_lemma
       ├── differentiableOn_cauchyIntegral_param
       ├── holomorphic_extension_across_real
       └── tube_domain_gluing

Layer 4: Analytic Continuation
  AnalyticContinuation.lean
       │
       ├── edge_of_the_wedge (PROVED THEOREM) — SCV tube domain extension
       └── bargmann_hall_wightman (AXIOM) — complex Lie group theory

Layer 5: Wick Rotation Bridge
  WickRotation.lean
       │
       ├── R→E: constructedSchwinger_* (#3-7) ← BHW axiom for E3
       ├── E→R: inductive/full analytic continuation (#8-10)
       ├── constructWightmanFunctions (#11-17) ← BHW axiom, #10
       └── os_to_wightman_full (#18) ← #11-17

Layer 6: Main Theorems
  Reconstruction.lean
       │
       ├── wightman_reconstruction (#19) ← GNS (done)
       ├── wightman_uniqueness (#20) ← #19
       ├── wightman_to_os (#21) ← wightman_to_os_full + #3-7
       └── os_to_wightman (#22) ← #18
```

**Historical critical path:** ~~#0a, #0b1~~ (proved), ~~#1~~ (proved theorem), ~~#2~~ (axiom) → #3-7 (R→E) and independently #8 → #9 → #10 → #11-17 → #18 → #22.

**Current implementation reading:** the live theorem frontier should instead be
read from the split contracts:
- theorem 2 locality frontier in `docs/theorem2_locality_blueprint.md`, ending
  at `OSToWightmanBoundaryValues.lean :: bvt_F_swapCanonical_pairing` but with
  an explicit four-layer proof transcript that must stay split: Route-B
  real-open-edge geometry in
  `ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean`, adjacent raw-
  boundary distributional support on the
  `AdjacencyDistributional.lean` / `BHWExtension.lean` seam, theorem-2-specific
  canonical-shift recovery in `OSToWightmanBoundaryValueLimits.lean`, and only
  then the final general-swap consumer in
  `OSToWightmanBoundaryValues.lean`. In particular, theorem 2 does **not**
  close by directly instantiating `BHWExtension.lean ::
  W_analytic_swap_boundary_pairing_eq`: that public wrapper asks for
  `IsLocallyCommutativeWeak d W`, so the non-circular route must first pass
  through the planned adjacent-only substitute consumer
  `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`, then the
  theorem-2 wrapper `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`, and
  only after that the canonical package
  `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
  -> `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
  -> `bvt_F_swapCanonical_pairing_of_adjacent_chain`;
- theorem 3 positivity frontier in `docs/theorem3_os_route_blueprint.md`, with
  Section-4.3 transport/positivity work split between
  `OSToWightmanPositivity.lean` and the final wrapper in
  `OSToWightmanBoundaryValues.lean`;
- theorem 4 cluster frontier in `docs/theorem4_cluster_blueprint.md`, with base
  cluster reductions in `OSToWightmanBoundaryValuesBase.lean` and the remaining
  transport/adapter package above them.

---

## Sorry Census

### By file (critical path only)

| File | Sorrys | IDs |
|------|--------|-----|
| SeparatelyAnalytic.lean | 0 | ✅ Complete |
| AnalyticContinuation.lean | 0 (1 axiom) | `bargmann_hall_wightman` (note: `edge_of_the_wedge` is now a proved theorem) |
| WickRotation.lean | 17 | #3–7, #8–10, #11–17, #18 |
| Reconstruction.lean | 4 | #19–22 |
| **Total** | **21** (+1 axiom) | |

### By difficulty and blocking status

| Category | IDs | Count | Notes |
|----------|-----|-------|-------|
| **Deep complex analysis** | ~~#0a, #0b1, #1~~ | 0 | #0a, #0b1 proved; #1 now proved as theorem (was axiom, see [history](edge_of_the_wedge_gap_analysis.md)) |
| **BHW theorem** | ~~#2~~ | 0 | Promoted to axiom ([details](BHW_STATUS.md)) |
| **R→E axiom verification** | #3, #4, #5, #7 | 4 | Independent of each other |
| **R→E needing BHW** | #6 | 1 | Needs #2 |
| **E→R analytic continuation** | #8, #9, #10 | 3 | Sequential chain |
| **Wightman axiom extraction** | #11–17 | 7 | Mostly need #10; #13,#15 need #2 |
| **Wiring** | #18–22 | 5 | Straightforward once dependencies met |

### Next steps (recommended order)

1. **#3–5, #7** (independent R→E theorems) — Can proceed in parallel.
   Don't depend on any axioms.

2. **#6** (`constructedSchwinger_symmetric`) — Uses `bargmann_hall_wightman` axiom.
   Now unblocked.

3. **#8–10** (E→R chain) — Can proceed independently.
   Laplace transform + Hartogs for #8, iteration for #9, growth estimates for #10.

4. **#11–17** (Wightman axiom extraction) — Most need #10; #13, #15 use BHW axiom.

5. **#18–22** — Wiring, once the above are complete.

---

## Mathematical References

| Reference | Content | Used in |
|-----------|---------|---------|
| Osterwalder-Schrader I (1973) | Axioms for Euclidean Green's functions | E0–E4 definitions, R→E direction |
| Osterwalder-Schrader II (1975) | Linear growth E0', analytic continuation | E→R direction (#8–10) |
| Streater-Wightman, Ch. 3 | PCT, Spin and Statistics | Wightman axioms, BHW, Jost lemma |
| Glimm-Jaffe, Ch. 19 | Quantum Physics: Reconstruction | Overall proof structure |
| Bogoliubov (1957) | Edge-of-the-wedge theorem | #1 |
| Bargmann-Hall-Wightman (1957) | Lorentz covariance → permuted tube | #2 |
| Osgood (1899) | Separately analytic → jointly analytic | Infrastructure for #1 |

---

## File Map

```text
OSReconstruction/Wightman/
├── Basic.lean                              ← re-exports
├── WightmanAxioms.lean                     ← downstream exported FA/theorem surfaces used by reconstruction consumers
├── OperatorDistribution.lean               ← operator-distribution layer
├── SchwartzTensorProduct.lean              ← Schwartz tensor products
├── Reconstruction.lean                     ← top-level umbrella import
├── Groups/
│   ├── Lorentz.lean                        ← Lorentz-group surfaces
│   └── Poincare.lean                       ← Poincaré-group surfaces
├── Spacetime/
│   ├── Metric.lean                         ← Minkowski metric
│   └── MinkowskiGeometry.lean              ← spacelike / cone geometry
├── Reconstruction/
│   ├── Main.lean                           ← top-level theorem wiring
│   ├── Core.lean                           ← shared reconstruction contracts
│   ├── AnalyticContinuation.lean           ← tube-domain / continuation interfaces
│   ├── GNSConstruction.lean                ← algebraic GNS layer
│   ├── GNSHilbertSpace.lean                ← completion / cyclicity / spectrum consumers
│   ├── SchwingerOS.lean                    ← Schwinger-side reduction layer
│   ├── BlockIntegral.lean                  ← finite-block integral packaging
│   ├── HeadBlockTranslationInvariant.lean  ← head-block descent invariance
│   ├── CenterSpatialTranslationInvariant.lean ← center-variable descent invariance
│   ├── TwoPointDescent.lean                ← specialized two-point descent helpers
│   └── WickRotation/
│       ├── BHWExtension.lean               ← checked public/raw-boundary BHW comparison surfaces
│       ├── OSToWightmanSemigroup.lean      ← semigroup / finite-block route
│       ├── OSToWightman.lean               ← main E -> R continuation route
│       ├── OSToWightmanBoundaryValuesBase.lean ← theorem-4 base transport lane
│       ├── OSToWightmanBoundaryValueLimits.lean ← theorem-3 live limit machinery; planned theorem-2 canonical-shift support sibling subsection
│       ├── OSToWightmanBoundaryValuesComparison.lean ← theorem-2 downstream locality consumer bridge
│       ├── OSToWightmanBoundaryValues.lean ← theorem-2/theorem-3 public boundary-value wrappers
│       ├── OStoWightmanPositivity.lean     ← theorem-3 positivity transfer lane
│       ├── SchwingerAxioms.lean            ← R -> E route
│       └── K2VI1/*                         ← active theorem-1 local package
└── NuclearSpaces/
    ├── NuclearOperator.lean                ← checked local support
    ├── NuclearSpace.lean                   ← checked local support (2 live sorrys)
    ├── SchwartzNuclear.lean                ← checked local support
    ├── GaussianFieldBridge.lean            ← checked local bridge/support layer
    ├── BochnerMinlos.lean                  ← checked local support (5 live sorrys)
    ├── EuclideanMeasure.lean               ← checked local support
    └── ComplexSchwartz.lean                ← checked local support
```

Implementation caution: the NuclearSpaces subtree is **not** a fake historical path and **not** the sole consumer surface either. The route contract for the GNS/nuclear lane is
`Wightman/NuclearSpaces/*` -> optional bridge/import packaging -> `Wightman/WightmanAxioms.lean` -> `Wightman/Reconstruction/GNSHilbertSpace.lean`.
Later Lean work should preserve that ownership split instead of proving ad hoc nuclearity facts directly inside `gns_cyclicity` or treating the downstream `WightmanAxioms.lean` exports as if they already identified their exact upstream implementation source.

Second implementation caution for theorem 2: `OSToWightmanBoundaryValueLimits.lean`
is a checked present file, but in the current tree its proved content is still
on the theorem-3 `singleSplit_xiShift` limit lane. The theorem-2 names
`bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`,
`bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`, and
`bvt_F_swapCanonical_pairing_of_adjacent_chain` are therefore planned support
packages in an existing file, not already-available helper theorems. Later Lean
work must add that sibling subsection explicitly rather than treating the
existing theorem-3 shell as if it already owned theorem-2 raw-boundary closure.
