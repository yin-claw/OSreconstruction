/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Schwartz Damping Convergence

Multiplying a Schwartz function by `exp(-ε · L)` converges to the
original function in Schwartz topology as ε → 0⁺, provided L is
bounded on the support of h.

## Main result

`schwartz_exp_damping_tendsto`: For h ∈ S(ℝᵐ) and L : ℝᵐ →L[ℝ] ℝ
with |L(ξ)| bounded on supp(h), there exists a Schwartz family h_ε
with h_ε(ξ) = exp(-εL(ξ)) · h(ξ), and h_ε → h as ε → 0⁺.

## Mathematical content

Since L is bounded on supp(h), |exp(-εL(ξ)) - 1| ≤ ε|L(ξ)|exp(ε|L(ξ)|)
≤ ε · M · exp(M) for ε ≤ 1, where M = sup_{supp(h)} |L|. By the Leibniz
rule, each seminorm of (exp(-εL) - 1)·h is O(ε) → 0.

Note: the hypothesis "L bounded on supp(h)" is weaker than "L ≥ 0 on supp(h)".
It is satisfied when h has support in a bounded neighborhood of a cone
(as for FixedConeCutoff × Schwartz).

## References

- Hörmander, "The Analysis of Linear PDOs I", §7.1
- Vladimirov, "Methods of Generalized Functions", §25
-/

open MeasureTheory Filter
noncomputable section

variable {m : ℕ}

-- **Axiom: Schwartz exponential damping convergence.**
--
-- For h ∈ S(ℝᵐ) and L : ℝᵐ →L[ℝ] ℝ with |L| bounded on supp(h):
-- ∃ Schwartz family h_ε with h_ε(ξ) = exp(-εLξ)·h(ξ), and h_ε → h.
--
-- Provable from Leibniz rule + |exp(-εt)-1| ≤ ε|t|exp(ε|t|).
axiom schwartz_exp_damping_tendsto
    (h : SchwartzMap (Fin m → ℝ) ℂ)
    (L : (Fin m → ℝ) →L[ℝ] ℝ)
    -- L is bounded on the support of h
    (hL_bdd : ∃ M : ℝ, ∀ ξ : Fin m → ℝ, h ξ ≠ 0 → |L ξ| ≤ M) :
    ∃ (h_ε : ℝ → SchwartzMap (Fin m → ℝ) ℂ),
      (∀ ε > 0, ∀ ξ, h_ε ε ξ = Complex.exp (-(ε : ℂ) * (L ξ : ℂ)) * h ξ) ∧
      Tendsto h_ε (nhdsWithin 0 (Set.Ioi 0)) (nhds h)

end
