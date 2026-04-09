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
not be used operationally. The live production ledger now distinguishes:
- a **headline `60`-sorry / `6`-axiom** theorem-2/3/4 frontier across the
  currently tracked `Wightman + SCV + ComplexLieGroups + vNA` buckets used by
  `docs/sorry_triage.md`, and
- a separate checked secondary `Wightman/NuclearSpaces/*` lane with **7** local
  `sorry`s that is intentionally kept outside that headline count.

If a later doc needs the whole-project direct-hole number, it must say so
explicitly rather than silently replacing the headline frontier count.
Infrastructure layers described below remain useful context, but the actual
implementation surface is no longer the old monolithic `WickRotation.lean`
story. In particular, the active `E -> R` route now runs through the split file
family
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

#### R → E Direction: reverse field-packaging lane (historical sorrys #3–7)

Given Wightman functions {W_n}, define Schwinger functions S_n by Wick rotation
and verify the OS axioms.

| Sorry | Theorem | OS Axiom | Proof idea |
|-------|---------|----------|------------|
| #3 | `constructedSchwinger_tempered` | E0 | Polynomial growth of W_analytic × Schwartz decay |
| #4 | split `E1_translation_invariant` / `E1_rotation_invariant` package | E1 | Change of variables + the checked BHW covariance seam `F_ext_translation_invariant -> wickRotatedBoundaryPairing_translation_invariant` and `F_ext_rotation_invariant -> wickRotatedBoundaryPairing_rotation_invariant` |
| #5 | `constructSchwinger_positive` | E2 | Reverse Section-4.3 transport/density package with frozen execution order `wickRotated_positiveTimeCore -> wickRotatedBoundaryPairing_eq_transport_inner_on_core -> wickRotatedBoundaryPairing_nonneg_on_core -> wickRotated_positiveTimeCore_dense -> wickRotatedBoundaryPairing_nonneg_by_density -> constructSchwinger_positive -> OsterwalderSchraderAxioms.E2_reflection_positive`; not a direct OS=`Wightman` shortcut |
| #6 | `E0_reality` + `E3_symmetric` packaging | E0 / E3 | Repackage checked `wickRotatedBoundaryPairing_reality` and `wickRotatedBoundaryPairing_symmetric` into the exact `OsterwalderSchraderAxioms` field shapes on `OS.S` |
| #7 | `constructSchwinger_cluster` | E4 | Reverse Section-4.4 packaging above the checked full-`SchwartzNPoint` wrapper, with frozen consumer order `W_analytic_cluster_integral -> wickRotatedBoundaryPairing_cluster -> constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster -> OsterwalderSchraderAxioms.E4_cluster` |

**Already proven:** `wightman_to_os_full` (line 385) — the weaker top-level bridge to `IsWickRotationPair`, not a full packaged `OsterwalderSchraderAxioms` witness.

Source-checked reverse-lane status split (2026-04-08): the late reverse fields are no longer allowed to blur together in this outline. In the live `SchwingerAxioms.lean` file, `wickRotatedBoundaryPairing_reflection_positive` already exists but is only a **quarantined wrapper** because it still closes through the false OS=`Wightman` chain `schwingerExtension_os_inner_product_eq_wightman -> schwingerExtension_os_inner_product_eq_wightman_positivity`; it therefore does **not** count as an honest checked supplier for `constructSchwinger_positive` / `E2_reflection_positive`. The honest E2 route is now frozen slot-by-slot: `wickRotated_positiveTimeCore` defines the Wick-restricted positive-time dense core, `wickRotatedBoundaryPairing_eq_transport_inner_on_core` identifies the reverse Euclidean pairing with the forward Section-4.3 transport inner product on that core, `wickRotatedBoundaryPairing_nonneg_on_core` imports positivity there, `wickRotated_positiveTimeCore_dense` supplies the density step, `wickRotatedBoundaryPairing_nonneg_by_density` extends nonnegativity to the ambient positive-time Euclidean space, and only then may `constructSchwinger_positive` package the result as `OsterwalderSchraderAxioms.E2_reflection_positive`. By contrast, `W_analytic_cluster_integral` is a live theorem-shaped reverse cluster supplier on the common-BHW/full-Schwartz level, but it is still only the upstream input to the future `constructSchwinger_cluster` / `E4_cluster` packaging on `ZeroDiagonalSchwartz`, not that final axiom-field witness itself. The implementation-facing consumer ladder is therefore frozen as `W_analytic_cluster_integral -> wickRotatedBoundaryPairing_cluster -> constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster -> OsterwalderSchraderAxioms.E4_cluster`, with `wickRotatedBoundaryPairing_cluster` owned by `SchwingerAxioms.lean` as the checked full-`SchwartzNPoint` wrapper and the three later slots reserved for the explicit zero-diagonal witness manufacture plus final packaging theorem on `constructSchwingerFunctions Wfn`.

The supplier theorem `W_analytic_cluster_integral` is no longer allowed to remain a vague “transport/density” box in this outline. Its proof transcript is now fixed in the same implementation order used by the detailed reverse-cluster note:

1. partition the `(n+m)`-point integration domain into finitely many time-ordering sectors;
2. prove the identity-sector ForwardTube membership needed to apply
   `bhw_pointwise_cluster_forwardTube` directly;
3. on every bad sector, rewrite the common-BHW integrand into an order-compatible chart by BHW permutation invariance, using within-block permutation symmetry of the factorized limit explicitly rather than a generic “by symmetry” phrase;
4. dominate every sector uniformly in the spatial translation parameter by the existing `HasForwardTubeGrowth` majorant together with Schwartz decay of `f.tensorProduct g_a`;
5. run dominated convergence sectorwise and then sum the finitely many sector contributions;
6. only after that supplier theorem is closed, pass to the checked wrapper `wickRotatedBoundaryPairing_cluster`, and only later to the still-missing zero-diagonal packager `constructSchwinger_cluster`.

So the reverse E4 lane in this outline is not just “Section 4.4 later”; it is the explicit three-level contract:
- first close `W_analytic_cluster_integral` by sector decomposition on the common-BHW/full-`SchwartzNPoint` side,
- then pass through the checked full-`SchwartzNPoint` wrapper `wickRotatedBoundaryPairing_cluster`, still owned by `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`,
- then add the still-missing zero-diagonal packaging theorem `constructSchwinger_cluster`, whose only acceptable owner is the reverse theorem-packaging layer targeting `Wightman/Reconstruction/SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster`.

That final packaging step is no longer allowed to be described as a vague “restrict tensor product / descend to zero diagonal” move. The implementation-facing transcript above `SchwingerOS.lean:792` is now frozen as:
1. `constructSchwinger_cluster_translate_adapter`: given `g : ZeroDiagonalSchwartz d m` and a spatial translation vector `a`, build the exact quantified witness `g_a : ZeroDiagonalSchwartz d m` with pointwise equation `g_a.1 x = g.1 (fun i => x i - a)`;
2. `constructSchwinger_cluster_tensor_adapter`: given `f : ZeroDiagonalSchwartz d n` and that translated witness `g_a`, build the exact `(n+m)`-point witness `fg_a : ZeroDiagonalSchwartz d (n + m)` with pointwise equation `fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)`;
3. `constructSchwinger_cluster`: consume `wickRotatedBoundaryPairing_cluster` together with those two adapters and discharge the literal norm inequality required by `OsterwalderSchraderAxioms.E4_cluster`.

To make that handoff executable rather than descriptive, the reverse `E4` lane is
now frozen here as a compact slot ledger too:

| Slot | Ownership | Must consume exactly | Must export exactly | Next allowed consumer |
|------|-----------|----------------------|---------------------|-----------------------|
| `W_analytic_cluster_integral` | `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` | the common-BHW/full-`SchwartzNPoint` cluster setup, with the proof transcript fixed as sector partition -> identity-sector ForwardTube step -> bad-sector permutation rewrites -> uniform majorant -> sectorwise dominated convergence -> finite sector sum | the reverse Section-4.4 supplier estimate on the common-BHW/full-`SchwartzNPoint` side | `wickRotatedBoundaryPairing_cluster` only |
| `wickRotatedBoundaryPairing_cluster` | `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` | `W_analytic_cluster_integral` only | the checked Wick-rotated full-`SchwartzNPoint` wrapper, still below any zero-diagonal packaging | `constructSchwinger_cluster_translate_adapter`, `constructSchwinger_cluster_tensor_adapter`, `constructSchwinger_cluster` |
| `constructSchwinger_cluster_translate_adapter` | reverse packaging layer targeting `Wightman/Reconstruction/SchwingerOS.lean` | `g : ZeroDiagonalSchwartz d m` plus a spatial translation vector `a` | the exact witness `g_a : ZeroDiagonalSchwartz d m` with pointwise translate equation | `constructSchwinger_cluster_tensor_adapter`, `constructSchwinger_cluster` |
| `constructSchwinger_cluster_tensor_adapter` | same reverse packaging layer | `f : ZeroDiagonalSchwartz d n` plus the translated witness `g_a` | the exact witness `fg_a : ZeroDiagonalSchwartz d (n + m)` with pointwise tensor equation | `constructSchwinger_cluster` |
| `constructSchwinger_cluster` | same reverse packaging layer, final target `SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster` | `wickRotatedBoundaryPairing_cluster` plus the manufactured witnesses `g_a` and `fg_a`; no vague tensor-restriction shortcut | the literal norm inequality demanded by the final `E4_cluster` field | final reverse field packaging only |

So later Lean work is not allowed to stop at the supplier/wrapper prose level or to leave the zero-diagonal witnesses implicit: `SchwingerAxioms.lean` owns the supplier theorem plus the full-`SchwartzNPoint` wrapper, while the final `g_a` / `fg_a` witness manufacture belongs to the reverse packaging layer above it.

#### E → R Direction: Analytic Continuation Chain (sorrys #8–10)

The reverse direction, following Osterwalder-Schrader II (1975).

Source-checked reverse-direction caution (2026-04-08): if this lane is later upgraded from `IsWickRotationPair` to a full `OsterwalderSchraderAxioms` witness, the structure target is `OS.S = constructSchwingerFunctions Wfn`, not the derived accessor `OS.schwinger = ...`. The already-landed packaging inputs for the early reverse fields are `constructedSchwinger_tempered_zeroDiagonal`, `constructedZeroDiagonalSchwinger_linear`, `wickRotatedBoundaryPairing_reality`, and `wickRotatedBoundaryPairing_symmetric`; later docs must not blur those into a vague bundled “reality / Euclidean symmetry” slogan. More sharply, the remaining late reverse fields have distinct source-checked statuses that should stay explicit: `E2_reflection_positive` still lacks an honest checked supplier theorem because the currently available wrapper is quarantined behind the false OS=`Wightman` chain, while `E4_cluster` already has the live supplier theorem `W_analytic_cluster_integral`, but only at the full-Schwartz/common-BHW-integral level rather than the final `ZeroDiagonalSchwartz` axiom-field level.

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
pending completion of the remaining reverse field-packaging theorems (#3–7).

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
       ├── R→E: reverse field-packaging lane (#3-7) ← BHW axiom for split E1 / E3 packaging
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
  -> `bvt_F_swapCanonical_pairing_of_adjacent_chain`.

  For later Lean execution, the same route is frozen here as a compact slot
  ledger rather than only a prose file map:

  | Slot | Ownership | Consumes | Exports | Next consumer |
  |------|-----------|----------|---------|---------------|
  | `choose_real_open_edge_for_adjacent_swap` | `ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean` | checked `exists_real_open_nhds_adjSwap` plus theorem-2 compact-support/open-edge packaging data | a chosen Route-B real edge together with its swapped mate | `swapped_support_lies_in_swapped_open_edge`, `swapped_open_edge_embeds_in_extendedTube`, `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` |
  | `bvt_F_boundary_continuous_at_real_support` | `Wightman/Reconstruction/ForwardTubeDistributions.lean` | theorem-2 flat-regular witness package above checked `boundary_function_continuous_forwardTube_of_flatRegular` | boundary continuity of `bvt_F` on the chosen real edge | `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` |
  | `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` | statement home `Wightman/Reconstruction/WickRotation/BHWExtension.lean`; lower helper lemmas in `ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean` | Route-B geometry package + `bvt_F_boundary_continuous_at_real_support` + checked `analytic_boundary_local_commutativity_of_boundary_continuous` | the actual non-circular adjacent raw-boundary pairing equality for theorem 2 | `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` |
  | `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` | `Wightman/Reconstruction/WickRotation/BHWExtension.lean` | `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` plus the checked ET-support wrapper shape | theorem-2-facing adjacent raw-boundary equality in exported boundary-pairing format | `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` |
  | `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean` | theorem-2 flat-regular witness package + checked `boundary_value_recovery_forwardTube_of_flatRegular_from_bv` specialized using checked `bvt_W`, `bvt_W_continuous`, `bvt_boundary_values`, `canonicalForwardConeDirection` | canonical-direction pairing recovery equality | `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` |
  | `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` | same theorem-2 sibling subsection in `OSToWightmanBoundaryValueLimits.lean` | `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` + two uses of `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` | adjacent canonical pairing equality for one adjacent transposition | `bvt_F_swapCanonical_pairing_of_adjacent_chain` |
  | `bvt_F_swapCanonical_pairing_of_adjacent_chain` | same theorem-2 sibling subsection in `OSToWightmanBoundaryValueLimits.lean` | adjacent-step canonical theorem plus explicit adjacent-factor decomposition of `swap i j` | full canonical swap pairing equality | `OSToWightmanBoundaryValues.lean :: bvt_F_swapCanonical_pairing` |
- theorem 3 positivity frontier in `docs/theorem3_os_route_blueprint.md`, with
  an explicit ownership and slot ledger that later Lean work should read
  literally rather than reconstructing from prose:

  | Slot / layer | Ownership | Checked-present now | Planned next slot / consumer |
  |------|-----------|---------------------|-------------------------------|
  | one-variable identity support | `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | exact checked anchors `identity_theorem_right_halfplane` (`:48`) and `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` (`:110`) | theorem-3 `singleSplit_xiShift` support layer in `OSToWightmanBoundaryValueLimits.lean`, and from there only the Stage-A slots `os1TransportOneVar` then `os1TransportOneVar_eq_zero_iff`; Lean should consume these exact scalar right-half-plane equality surfaces rather than reproving an alternate Package-A/B wrapper or letting later Section-4.3 slots pull them directly |
  | one-variable holomorphic/limit support | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean` | the checked `singleSplit_xiShift` holomorphic trace, its positive-real identification theorems, and its `t -> 0+` limit-transfer theorems used by theorem 3 | the one-variable Section-4.3 slots `os1TransportOneVar` then `os1TransportOneVar_eq_zero_iff` in `OSToWightmanPositivity.lean`; no later theorem-3 slot may bypass this file by appealing to an unnamed generic boundary-value uniqueness principle |
  | checked Hilbert-vector support | `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | exact checked general-target anchors `positiveTimeBorchersVector` (`:1461`), `positiveTimeBorchersVector_inner_eq` (`:1467`), and `positiveTimeBorchersVector_norm_sq_eq` (`:1480`), with the later single-component specialization `euclideanPositiveTimeSingleVector` (`:1523`) and `euclideanPositiveTimeSingleVector_norm_sq_eq` (`:1530`) kept explicitly downstream | only `bvt_transport_to_osHilbert_onImage` may first consume the general Hilbert target/equality package; `lemma42_matrix_element_time_interchange` and `bvt_wightmanInner_eq_transport_norm_sq_onImage` may reuse it only downstream of that transport-map theorem, while the single-component wrapper is reserved for later specialization rather than the primitive Stage-C transport target |
  | checked Hilbert-density support | `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | exact checked anchor `positiveTimeBorchersVector_dense` (`:1506`) | only `bvt_W_positive_of_transportImage_density` may first consume this density theorem; no earlier transport-map, kernel-zero, or quadratic-identity slot may use it |
  | Section-4.3 transformed-image package | `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | no landed theorem-slot names yet under the blueprint names `os1TransportOneVar`, `os1TransportOneVar_eq_zero_iff`, `os1TransportComponent`, `os1TransportComponent_eq_zero_iff`, `BvtTransportImageSequence`, `bvt_transport_to_osHilbert_onImage_wellDefined`, `bvt_transport_to_osHilbert_onImage`, `lemma42_matrix_element_time_interchange`, `bvt_wightmanInner_eq_transport_norm_sq_onImage`, `bvt_W_positive_of_transportImage_density`; the Lean execution order is frozen as `partialFourierSpatial_fun -> partialFourierSpatial_timeSliceSchwartz -> partialFourierSpatial_timeSlice_hasPaleyWienerExtension -> partialFourierSpatial_timeSliceCanonicalExtension -> os1TransportOneVar -> os1TransportOneVar_eq_zero_iff -> os1TransportComponent -> os1TransportComponent_eq_zero_iff -> BvtTransportImageSequence -> bvt_transport_to_osHilbert_onImage_wellDefined -> bvt_transport_to_osHilbert_onImage -> lemma42_matrix_element_time_interchange -> bvt_wightmanInner_eq_transport_norm_sq_onImage -> bvt_W_positive_of_transportImage_density`, and the on-image transport stage must first close the explicit preimage-independence theorem `bvt_transport_to_osHilbert_onImage_wellDefined`, consuming the degreewise kernel-zero theorems rather than an unnamed injectivity slogan, before the transport map itself is available | `OSToWightmanBoundaryValues.lean :: bvt_W_positive` |
  | exported frontier consumer | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean` | the private frontier theorem `bvt_W_positive` and downstream wrappers/transfer consumers | public reconstruction consumers only |

  Two theorem-3 anti-drift rules are now part of that contract too:
  1. the transformed-image / Section-4.3 package belongs entirely in
     `OSToWightmanPositivity.lean`, not in
     `OSToWightmanBoundaryValueLimits.lean` or
     `OSToWightmanBoundaryValues.lean`; its first missing slot is packaging
     work above the already-checked SCV foothold in
     `OSReconstruction/SCV/PartialFourierSpatial.lean`, not discovery of a
     missing companion support file;
  2. `bvtTransportImage_dense` is **not** an endorsed active production slot;
     if the paper Lemma-4.1 dense-range statement is formalized later, it must
     appear as `os1TransportComponent_denseRange` on the corrected half-space
     codomain and be kept separate from the live positivity-closure package.

  Later positive-time / compact-approximation statements in
  `OSToWightmanBoundaryValuesBase.lean`,
  `OSToWightmanBoundaryValuesCompactApprox.lean`, and
  `OSToWightmanBoundaryValues.lean` remain legacy consumers rather than the
  endorsed theorem-3 route;
- theorem 4 cluster frontier in `docs/theorem4_cluster_blueprint.md`, with a
  fixed three-layer ownership split that later Lean work should read literally
  rather than reconstructing from prose. The current checked tree already has
  the base reductions in
  `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean`
  and the final private wrapper in
  `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`, but
  the normalization / one-factor extraction package and the public canonical-
  shell adapter package below are still planned theorem-slot work unless a
  later source check says otherwise:

  | Slot | Ownership | Consumes | Exports | Next consumer |
  |------|-----------|----------|---------|---------------|
  | `normalizedZeroDegreeRightVector` | `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | the degree-`0` unit shell only | the literal positive-time Borchers vector concentrated in degree `0` with value `1` | `normalizedZeroDegreeRightVector_bound`, `normalizedZeroDegreeRightVector_funcs_zero`, `normalizedZeroDegreeRightVector_funcs_pos`, the two right-single extraction lemmas |
  | `normalizedZeroDegreeRightVector_bound` / `..._funcs_zero` / `..._funcs_pos` | same file | `normalizedZeroDegreeRightVector` | the exact structural facts `bound = 0`, degree-`0` shell is the unit, and all positive-degree shells vanish | `zeroDegree_right_single_wightman_extracts_factor`, `zeroDegree_right_single_os_extracts_factor`, `zero_degree_component_comparison_for_normalized_right_vector` |
  | `zeroDegree_right_single_wightman_extracts_factor` | same file | checked `WightmanInnerProduct_right_single` plus the normalized degree-`0` structural lemmas | extraction of the left Wightman factor against the normalized zero-degree right vector | `cluster_left_factor_transport` |
  | `zeroDegree_right_single_os_extracts_factor` | same file | checked `OSInnerProduct_right_single` plus the same structural lemmas | extraction of the left OS factor against the normalized zero-degree right vector | `cluster_left_factor_transport` |
  | `zero_degree_component_comparison_for_normalized_right_vector` | same file | corrected theorem-3 Section-4.3 transport package plus the normalized degree-`0` vanishing facts | the unique surviving `m = 0` transport comparison needed for theorem-4 factor extraction | `cluster_left_factor_transport`, `cluster_right_factor_transport` |
  | `cluster_left_factor_transport` | `Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | `zeroDegree_right_single_wightman_extracts_factor`, `zeroDegree_right_single_os_extracts_factor`, `zero_degree_component_comparison_for_normalized_right_vector` | corrected theorem-3-to-theorem-4 left one-factor transport equality | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` |
  | `cluster_right_factor_transport` | same file | the exact right-lane transport transcript, with no new normalization package allowed: first instantiate the alias `normalizedZeroDegreeLeftVector d := normalizedZeroDegreeRightVector d` by definitional equality only; then import no new structural lemmas beyond the already-landed degree-`0` witness facts `normalizedZeroDegreeRightVector_bound`, `..._funcs_zero`, `..._funcs_pos`; then package only the checked supplier theorems `WightmanInnerProduct_right_single` and `OSInnerProduct_right_single` into the right-side extraction slots; then consume `zero_degree_component_comparison_for_normalized_right_vector`; and only after those four steps prove the final right one-factor transport equality moving the nontrivial shell to the second input | corrected theorem-3-to-theorem-4 right one-factor transport equality | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` |
  | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean` | checked large-spatial reductions there (`...singleSplitLargeSpatial`, `...singleSplitSchwingerLargeSpatial`) plus `cluster_left_factor_transport` and `cluster_right_factor_transport` | corrected positive-time single-split cluster bridge with the exact one-factor transport inputs theorem 4 is allowed to use | `bvt_cluster_positiveTime_singleSplit_core` |
  | `bvt_cluster_positiveTime_singleSplit_core` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean` | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` | thin base-file wrapper exposing the repaired positive-time cluster core in the eventual-translate format | `singleSplit_core_rewrites_to_canonical_shell` |
  | `canonical_cluster_integrand_eq_singleSplit_integrand` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean` | only the checked canonical-shell direction surfaces imported through `OSToWightmanBoundaryValuesComparison.lean` (`canonicalForwardConeDirection`, `canonicalForwardConeDirection_mem`) plus the repaired base-core shell statement exported by `bvt_cluster_positiveTime_singleSplit_core` | the theorem-4-specific integrand rewrite from the public canonical shell to the repaired positive-time single-split shell | `singleSplit_core_rewrites_to_canonical_shell` |
  | `canonical_translate_factor_eq_singleSplit_translate_factor` | same file | only the checked translated-shell data already in scope (`translateSchwartzNPoint` together with the same canonical-direction surface) plus the translated-shell statement shape appearing in private `bvt_F_clusterCanonicalEventually_translate` | the translated-right-factor rewrite needed to match the positive-time core surface exactly, before any limit transport is invoked | `singleSplit_core_rewrites_to_canonical_shell` |
  | `singleSplit_core_rewrites_to_canonical_shell` | same file | `bvt_cluster_positiveTime_singleSplit_core`, `canonical_cluster_integrand_eq_singleSplit_integrand`, `canonical_translate_factor_eq_singleSplit_translate_factor` | exact shell-statement-level reduction of the public canonical-shell cluster problem to the repaired positive-time single-split core, with both the integrand and translated-factor rewrites already discharged | `canonical_shell_limit_of_rewrite` |
  | `canonical_shell_limit_of_rewrite` | same file | `singleSplit_core_rewrites_to_canonical_shell` plus only the checked scalar-holomorphic / limit-transport package imported from `OSToWightmanBoundaryValueLimits.lean`; its internal proof transcript is fixed as `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq` -> optional right-half-plane uniqueness only via `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` + `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq` -> final Wightman-target `t → 0+` transport only via `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`. The Schwinger-target theorems `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift` and `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger` are lower supplier legs only, and the deprecated bridge `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift` is forbidden on this lane | transport from the rewritten canonical-shell statement to the eventual/limit form consumed immediately by `bvt_cluster_canonical_from_positiveTime_core` and then private `bvt_F_clusterCanonicalEventually_translate` | `bvt_cluster_canonical_from_positiveTime_core` |
  | `bvt_cluster_canonical_from_positiveTime_core` | same file | `canonical_shell_limit_of_rewrite` only | theorem-4-facing canonical-shell adapter theorem, stated as the immediate input to private `bvt_F_clusterCanonicalEventually_translate` | `bvt_F_clusterCanonicalEventually_translate` |

  Two route rules are now part of this outline too:
  1. theorem 4 may not reopen theorem 3 analytically inside the cluster proof;
     it must consume only the explicit one-factor transport theorems named
     above, with the degree-zero normalization/extraction package visible as a
     separate theorem-4 bookkeeping layer rather than hidden inside
     `cluster_left_factor_transport` / `cluster_right_factor_transport`;
  2. `OSToWightmanBoundaryValueLimits.lean` is not part of the theorem-4 file
     ownership chain under the current checked-tree contract, but the theorem-4
     adapter may consume only the already-named imported support theorems from
     that file at the single place `canonical_shell_limit_of_rewrite`; more
     sharply, that slot must itself run in the fixed suborder
     `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
     -> optional right-half-plane uniqueness via
     `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` and
     `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
     -> final Wightman-target limit transport by
     `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`,
     with the Schwinger-target limit theorems kept as supplier-only lower legs;
     no earlier theorem-4 slot may silently pull in extra limit machinery.

  Source-check status summary for that ledger, against the current repo tree:
  1. checked-present today in `OSToWightmanBoundaryValuesBase.lean` at exact
     anchors `:2214 :: bvt_F_clusterCanonicalEventually_translate_of_singleSplitLargeSpatial`,
     `:2352 :: bvt_F_clusterCanonicalEventually_translate_of_singleSplitSchwingerLargeSpatial`,
     and the legacy theorem
     `:2514 :: bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`;
  2. checked-present today in `OSToWightmanBoundaryValues.lean` at exact
     anchors `:27 :: bv_cluster_transfer_of_canonical_eventually`,
     `:398 :: private bvt_F_clusterCanonicalEventually_translate`,
     `:414 :: private bvt_F_clusterCanonicalEventually`, and
     `:473 :: private bvt_W_cluster`; there are not yet checked
     theorem-4-specific cluster rewrite lemmas in that file for the canonical
     integrand or translate factor, so those rows in the ledger above remain
     fully planned adapter slots rather than already-landed local support;
  3. still planned theorem-slot names, not landed production theorem names yet:
     `normalizedZeroDegreeRightVector`, its three structural lemmas,
     `zeroDegree_right_single_wightman_extracts_factor`,
     `zeroDegree_right_single_os_extracts_factor`,
     `zero_degree_component_comparison_for_normalized_right_vector`,
     `cluster_left_factor_transport`, `cluster_right_factor_transport`,
     `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`,
     `bvt_cluster_positiveTime_singleSplit_core`,
     `canonical_cluster_integrand_eq_singleSplit_integrand`,
     `canonical_translate_factor_eq_singleSplit_translate_factor`,
     `singleSplit_core_rewrites_to_canonical_shell`,
     `canonical_shell_limit_of_rewrite`, and
     `bvt_cluster_canonical_from_positiveTime_core`.

  So the implementation-facing theorem-4 ambiguity is no longer “what is the
  route?” but “which parts of the route are already checked code versus still
  missing slot work.” Later Lean implementation should read the ledger above as
  a route contract, not as a claim that those intermediate theorem names are
  already available in the files.

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
│       ├── OSToWightmanBoundaryValueLimits.lean ← theorem-3 `singleSplit_xiShift` holomorphic/limit support only; planned theorem-2 canonical-shift support sibling subsection
│       ├── OSToWightmanBoundaryValuesComparison.lean ← theorem-2 downstream locality consumer bridge
│       ├── OSToWightmanBoundaryValues.lean ← theorem-2 frontier wrapper + theorem-3 exported positivity wrapper + downstream transfer consumers
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
More sharply, this file is not allowed to absorb the earlier raw-boundary seam:
its first theorem-2-owned import is the already-exported wrapper
`bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`, not the Route-B geometry
package and not the substitute consumer theorem
`adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` itself.
