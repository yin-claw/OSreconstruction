/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.PaleyWienerSchwartz

/-!
# Concrete Construction of the Cone-Adapted Schwartz Family

This file constructs the multi-dimensional Schwartz family ψ_{z,R} concretely
from a `FixedConeCutoff` adapted to the dual cone.

## The construction

Given:
- C : an open convex salient cone in ℝ^m
- χ : a `FixedConeCutoff` for `DualConeFlat C` (the dual cone)
- R > 0 : the cutoff radius
- z ∈ T(C) : a point in the tube

Define:
  `psiZR χ R z ξ = χ(ξ/R) * exp(i z·ξ)`

where `z·ξ = ∑_j z_j * ξ_j`.

## Properties

- **Smooth in ξ**: χ is C^∞, exp is C^∞, product is C^∞
- **Schwartz decay**: On supp(χ(·/R)), ξ is within distance R of DualConeFlat(C).
  For y ∈ C (salient), `y·ξ ≥ c·‖ξ‖ - c'·R·‖y‖` on this support, giving
  `exp(-y·ξ) ≤ exp(c'·R·‖y‖) * exp(-c·‖ξ‖)` — exponential decay.
  Combined with polynomial growth of χ-derivatives (bounded by R^{-|α|}),
  the product is Schwartz.
- **Seminorm bound** (fixed R=1): `‖ψ_z‖_{k,n} ≤ B·(1+‖x‖)^N·exp(C·‖y‖)`
  (exponential in y — this is why fixed R doesn't give Vladimirov bound)
- **Seminorm bound** (dynamic R=1/(1+‖y‖)): `‖ψ_z‖_{k,n} ≤ B·(1+‖x‖)^N·(1+‖y‖)^M`
  (polynomial in y — the Vladimirov bound!)

## References

- Vladimirov, "Methods of Generalized Functions", §25
- See docs/vladimirov_tillmann_gemini_reviews.md for the dynamic scaling trick
-/

open scoped Classical ComplexConjugate BigOperators NNReal
open MeasureTheory Complex
noncomputable section

variable {m : ℕ}

/-! ### The raw function (not yet a SchwartzMap) -/

/-- The raw cone-adapted exponential-cutoff function.
    `psiZRaw χ R z ξ = χ(ξ/R) * exp(i z·ξ)` -/
def psiZRaw {C : Set (Fin m → ℝ)} (χ : FixedConeCutoff (DualConeFlat C))
    (R : ℝ) (z : Fin m → ℂ) (ξ : Fin m → ℝ) : ℂ :=
  (χ.val (fun i => R⁻¹ * ξ i) : ℂ) * cexp (I * ∑ i, z i * (ξ i : ℂ))

/-- The raw function is smooth in ξ (for fixed z and R > 0). -/
theorem psiZRaw_contDiff {C : Set (Fin m → ℝ)} (χ : FixedConeCutoff (DualConeFlat C))
    (R : ℝ) (z : Fin m → ℂ) :
    ContDiff ℝ ⊤ (psiZRaw χ R z) := by
  -- χ(ξ/R) is C^∞ (composition of smooth functions)
  -- exp(iz·ξ) is C^∞ (exponential of linear function)
  -- Product of C^∞ functions is C^∞
  sorry

/-- The raw function vanishes for ξ far from the dual cone (distance > R). -/
theorem psiZRaw_support {C : Set (Fin m → ℝ)} (χ : FixedConeCutoff (DualConeFlat C))
    {R : ℝ} (hR : 0 < R) (z : Fin m → ℂ) (ξ : Fin m → ℝ)
    (hξ : Metric.infDist ξ (DualConeFlat C) > R) :
    psiZRaw χ R z ξ = 0 := by
  -- dist(R⁻¹ξ, DualConeFlat C) = R⁻¹ * dist(ξ, DualConeFlat C) > 1
  -- (using DualConeFlat is a cone, so scaling preserves it)
  sorry

/-- Two cutoff radii give the same function on the dual cone itself. -/
theorem psiZRaw_eq_on_dualCone {C : Set (Fin m → ℝ)} (χ : FixedConeCutoff (DualConeFlat C))
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (z : Fin m → ℂ) (ξ : Fin m → ℝ)
    (hξ : ξ ∈ DualConeFlat C) :
    psiZRaw χ R₁ z ξ = psiZRaw χ R₂ z ξ := by
  -- Both χ(ξ/R₁) and χ(ξ/R₂) equal 1 on DualConeFlat C
  -- because DualConeFlat is a cone, so R⁻¹ξ ∈ DualConeFlat C,
  -- and χ equals 1 near the cone
  sorry

/-! ### Schwartz decay (the hard part) -/

/-- The raw function has Schwartz decay when the cone is salient.
    This is the key analytic estimate: on supp(χ(·/R)),
    `exp(-y·ξ) ≤ exp(c·R·‖y‖)` (bounded in the transition region),
    combined with exponential decay `exp(-c'·‖ξ‖)` on the cone interior,
    gives overall rapid decay. -/
theorem psiZRaw_schwartz_decay
    {C : Set (Fin m → ℝ)}
    (hC_salient : IsSalientCone C)
    (χ : FixedConeCutoff (DualConeFlat C))
    {R : ℝ} (hR : 0 < R)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C)
    (k : ℕ) :
    ∃ (D : ℝ), ∀ (ξ : Fin m → ℝ),
      ‖ξ‖ ^ k * ‖psiZRaw χ R z ξ‖ ≤ D := by
  sorry

/-! ### Packaging as SchwartzMap -/

/-- The cone-adapted Schwartz function, packaged as a `SchwartzMap`.
    Requires the cone to be salient for Schwartz decay. -/
def psiZRSchwartz
    {C : Set (Fin m → ℝ)}
    (hC_salient : IsSalientCone C)
    (χ : FixedConeCutoff (DualConeFlat C))
    (R : ℝ) (hR : 0 < R)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) :
    SchwartzMap (Fin m → ℝ) ℂ where
  toFun := psiZRaw χ R z
  smooth' := sorry -- psiZRaw_contDiff χ R z (universe level mismatch)
  decay' := by
    intro k n
    -- Need: ∃ C, ∀ ξ, ‖ξ‖^k * ‖iteratedFDeriv ℝ n (psiZRaw χ R z) ξ‖ ≤ C
    -- The iterated derivative of χ(ξ/R) * exp(iz·ξ) involves:
    -- - Derivatives of χ(ξ/R): bounded by R^{-n} * ‖D^n χ‖_∞ (from deriv_bound)
    -- - Derivatives of exp(iz·ξ): multiply by (iz)^α, still exponentially decaying
    -- - Product rule: sum of terms, each bounded
    -- Combined with psiZRaw_schwartz_decay for the ‖ξ‖^k factor
    sorry

end
