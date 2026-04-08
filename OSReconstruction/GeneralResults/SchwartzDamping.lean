/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Schwartz Damping Convergence

Multiplying a Schwartz function by `exp(-ε · L)` converges to the
original function in Schwartz topology as ε → 0⁺.

## Main result

`schwartz_exp_damping_tendsto`: For a Schwartz function h and a CLM L
with L(ξ) ≥ 0 on supp(h), there exists a Schwartz-valued family h_ε
with h_ε(ξ) = exp(-εL(ξ)) · h(ξ), and h_ε → h in Schwartz topology.

## Mathematical content

The proof uses the Leibniz rule + |exp(-εt) - 1| ≤ εt for t ≥ 0,
giving ‖h_ε - h‖_{k,n} = O(ε) → 0 for each seminorm.

## References

- Hörmander, "The Analysis of Linear PDOs I", §7.1
- Vladimirov, "Methods of Generalized Functions", §25
-/

open MeasureTheory Filter
noncomputable section

variable {m : ℕ}

-- **Axiom: Schwartz exponential damping convergence.**
--
-- For h ∈ S(ℝᵐ) and L : ℝᵐ →L[ℝ] ℝ with L ≥ 0 on supp(h):
-- there exists a family h_ε ∈ S(ℝᵐ) with h_ε(ξ) = exp(-εLξ)·h(ξ)
-- and h_ε → h in Schwartz topology as ε → 0⁺.
--
-- Provable from Leibniz rule + |exp(-εt)-1| ≤ εt for t ≥ 0.
axiom schwartz_exp_damping_tendsto
    (h : SchwartzMap (Fin m → ℝ) ℂ)
    (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (hL_nonneg : ∀ ξ : Fin m → ℝ, h ξ ≠ 0 → 0 ≤ L ξ) :
    ∃ (h_ε : ℝ → SchwartzMap (Fin m → ℝ) ℂ),
      (∀ ε > 0, ∀ ξ, h_ε ε ξ = Complex.exp (-(ε : ℂ) * (L ξ : ℂ)) * h ξ) ∧
      Tendsto h_ε (nhdsWithin 0 (Set.Ioi 0)) (nhds h)

end
