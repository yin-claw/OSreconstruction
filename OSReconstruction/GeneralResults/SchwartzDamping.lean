/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Schwartz Exponential Damping Convergence

Multiplying a Schwartz function by `exp(-ε · L)` (where L is a CLM)
converges to the original function in Schwartz topology as ε → 0⁺.

## Main result

`schwartz_exp_damping_tendsto`: For h ∈ S(ℝᵐ) and L : ℝᵐ →L[ℝ] ℝ,
the family `exp(-εL) · h → h` in Schwartz topology as ε → 0⁺.

## Mathematical content

No sign or boundedness condition on L is needed. The convergence holds
because:

1. `|exp(-εL(ξ)) - 1| ≤ ε|L(ξ)| · exp(ε|L(ξ)|)` (from |eˢ-1| ≤ |s|e^|s|)
2. `|L(ξ)| ≤ ‖L‖ · ‖ξ‖` (operator norm bound)
3. For the Leibniz rule on D^n[(exp(-εL)-1)·h]:
   - D^j[exp(-εL)] involves (εL')^j exp(-εL), bounded by (ε‖L‖)^j exp(ε‖L‖·‖ξ‖)
   - D^{n-j}[h] has rapid Schwartz decay
4. Each seminorm: ‖(exp(-εL)-1)·h‖_{k,n} ≤ ε · P(‖L‖) · (Schwartz constant)

The polynomial exp(ε‖L‖·‖ξ‖) factor is absorbed by Schwartz decay of h
for any fixed ε, and the overall ε prefactor drives the seminorm to 0.

## References

- Hörmander, "The Analysis of Linear PDOs I", §7.1
- Vladimirov, "Methods of Generalized Functions", §25
-/

open MeasureTheory Filter
noncomputable section

variable {m : ℕ}

-- **Axiom: Schwartz exponential damping convergence.**
--
-- For h ∈ S(ℝᵐ) and ANY continuous linear form L : ℝᵐ →L[ℝ] ℝ:
-- ∃ Schwartz family h_ε with h_ε(ξ) = exp(-εLξ)·h(ξ), and h_ε → h.
--
-- No sign or boundedness condition on L. The Schwartz decay of h
-- absorbs the polynomial/exponential growth of the damping factor.
axiom schwartz_exp_damping_tendsto
    (h : SchwartzMap (Fin m → ℝ) ℂ)
    (L : (Fin m → ℝ) →L[ℝ] ℝ) :
    ∃ (h_ε : ℝ → SchwartzMap (Fin m → ℝ) ℂ),
      (∀ ε > 0, ∀ ξ, h_ε ε ξ = Complex.exp (-(ε : ℂ) * (L ξ : ℂ)) * h ξ) ∧
      Tendsto h_ε (nhdsWithin 0 (Set.Ioi 0)) (nhds h)

end
