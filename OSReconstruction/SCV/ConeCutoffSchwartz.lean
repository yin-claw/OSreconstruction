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

/-! ### Cone-scaling of infDist -/

/-- For a set S closed under positive scaling (a cone), the infDist scales:
    `infDist (a • ξ) S = |a| * infDist ξ S` for a > 0.
    Proof: inf_{η ∈ S} ‖aξ - η‖ = inf_{η ∈ S} ‖a(ξ - η/a)‖ = |a| * inf_{η' ∈ S} ‖ξ - η'‖
    where η' = η/a ranges over S. -/
theorem infDist_smul_cone {S : Set (Fin m → ℝ)}
    (hS_cone : ∀ (y : Fin m → ℝ), y ∈ S → ∀ (t : ℝ), 0 < t → t • y ∈ S)
    {a : ℝ} (ha : 0 < a) (ξ : Fin m → ℝ) :
    Metric.infDist (a • ξ) S = a * Metric.infDist ξ S := by
  have ha_inv : 0 < a⁻¹ := inv_pos.mpr ha
  let e : ↥S ≃ ↥S :=
    { toFun := fun y => ⟨a • y.1, hS_cone y.1 y.2 a ha⟩
      invFun := fun y => ⟨a⁻¹ • y.1, hS_cone y.1 y.2 a⁻¹ ha_inv⟩
      left_inv := by
        intro y
        ext i
        simp [Pi.smul_apply]
        rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
      right_inv := by
        intro y
        ext i
        simp [Pi.smul_apply]
        rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] }
  rw [Metric.infDist_eq_iInf, Metric.infDist_eq_iInf]
  calc
    (⨅ y : S, dist (a • ξ) y) = ⨅ y : S, dist (a • ξ) (e y) := by
      symm
      exact Equiv.iInf_congr e fun _ => rfl
    _ = ⨅ y : S, a * dist ξ y := by
      congr with y
      change ‖a • ξ - a • (y : Fin m → ℝ)‖ = a * ‖ξ - y‖
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg ha.le]
    _ = a * ⨅ y : S, dist ξ y := by
      rw [← Real.mul_iInf_of_nonneg ha.le]

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
  unfold psiZRaw
  have hscale : ContDiff ℝ ⊤ (fun ξ : Fin m → ℝ => fun i => R⁻¹ * ξ i) := by
    refine contDiff_pi.2 fun i => ?_
    simpa [Pi.smul_apply, smul_eq_mul] using
      (((R⁻¹ : ℝ) •
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) i)).contDiff :
        ContDiff ℝ ⊤ ((R⁻¹ : ℝ) •
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) i)))
  have hcutoff : ContDiff ℝ ⊤
      (fun ξ : Fin m → ℝ => (χ.val (fun i => R⁻¹ * ξ i) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (χ.smooth.comp hscale)
  have hexpArg : ContDiff ℝ ⊤
      (fun ξ : Fin m → ℝ => I * ∑ i, z i * (ξ i : ℂ)) := by
    refine contDiff_const.mul <| ContDiff.sum fun i _ => ?_
    exact contDiff_const.mul <|
      Complex.ofRealCLM.contDiff.comp
        ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin m) (φ := fun _ => ℝ) i).contDiff)
  exact hcutoff.mul (Complex.contDiff_exp.comp hexpArg)

/-- The raw function vanishes for ξ far from the dual cone (distance > R). -/
theorem psiZRaw_support {C : Set (Fin m → ℝ)} (χ : FixedConeCutoff (DualConeFlat C))
    {R : ℝ} (hR : 0 < R) (z : Fin m → ℂ) (ξ : Fin m → ℝ)
    (hξ : Metric.infDist ξ (DualConeFlat C) > R) :
    psiZRaw χ R z ξ = 0 := by
  simp only [psiZRaw]
  have hχ_zero : χ.val (fun i => R⁻¹ * ξ i) = 0 := by
    apply χ.support_bound
    -- infDist(R⁻¹ξ, DualConeFlat C) = R⁻¹ * infDist(ξ, DualConeFlat C) > R⁻¹ * R = 1
    -- DualConeFlat C is a cone (scaling-closed)
    have hS_cone : ∀ (y : Fin m → ℝ), y ∈ DualConeFlat C →
        ∀ (t : ℝ), 0 < t → t • y ∈ DualConeFlat C := by
      intro y hy t ht
      rw [mem_dualConeFlat] at hy ⊢
      intro w hw
      have := hy w hw
      simp [Pi.smul_apply, smul_eq_mul]
      calc ∑ i, w i * (t * y i) = t * ∑ i, w i * y i := by
            rw [Finset.mul_sum]; congr 1; ext i; ring
        _ ≥ 0 := mul_nonneg (le_of_lt ht) this
    have hscale : Metric.infDist (R⁻¹ • ξ) (DualConeFlat C) =
        R⁻¹ * Metric.infDist ξ (DualConeFlat C) :=
      infDist_smul_cone hS_cone (inv_pos.mpr hR) ξ
    show Metric.infDist (fun i => R⁻¹ * ξ i) (DualConeFlat C) > 1
    simp only [show (fun i => R⁻¹ * ξ i) = R⁻¹ • ξ from rfl]
    rw [hscale]
    calc 1 = R⁻¹ * R := by rw [inv_mul_cancel₀ (ne_of_gt hR)]
      _ < R⁻¹ * Metric.infDist ξ (DualConeFlat C) := by
          apply mul_lt_mul_of_pos_left hξ (inv_pos.mpr hR)
  simp [hχ_zero]

/-- Two cutoff radii give the same function on the dual cone itself. -/
theorem psiZRaw_eq_on_dualCone {C : Set (Fin m → ℝ)} (χ : FixedConeCutoff (DualConeFlat C))
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (z : Fin m → ℂ) (ξ : Fin m → ℝ)
    (hξ : ξ ∈ DualConeFlat C) :
    psiZRaw χ R₁ z ξ = psiZRaw χ R₂ z ξ := by
  simp only [psiZRaw]
  -- Both χ(ξ/R₁) = 1 and χ(ξ/R₂) = 1 because:
  -- ξ ∈ DualConeFlat C, DualConeFlat is a cone, so R⁻¹ξ ∈ DualConeFlat C
  have hξ₁ : (fun i => R₁⁻¹ * ξ i) ∈ DualConeFlat C := by
    rw [mem_dualConeFlat] at hξ ⊢
    intro y hy
    have := hξ y hy
    calc ∑ i, y i * (R₁⁻¹ * ξ i)
        = R₁⁻¹ * ∑ i, y i * ξ i := by
          rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≥ 0 := mul_nonneg (inv_nonneg.mpr (le_of_lt hR₁)) this
  have hξ₂ : (fun i => R₂⁻¹ * ξ i) ∈ DualConeFlat C := by
    rw [mem_dualConeFlat] at hξ ⊢
    intro y hy
    have := hξ y hy
    calc ∑ i, y i * (R₂⁻¹ * ξ i)
        = R₂⁻¹ * ∑ i, y i * ξ i := by
          rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≥ 0 := mul_nonneg (inv_nonneg.mpr (le_of_lt hR₂)) this
  rw [χ.one_on_set _ hξ₁, χ.one_on_set _ hξ₂]

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
  smooth' := by
    exact (psiZRaw_contDiff χ R z).of_le (by simp)
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
