/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Fubini Exchange for Schwartz-Valued Integrals

A continuous linear functional on Schwartz space commutes with
parameter integrals of Schwartz-valued families.

## Main result

`schwartz_clm_fubini_exchange`: For T : S(ℝᵐ) →L[ℂ] ℂ and a
family g : ℝᵐ → S(ℝᵐ) satisfying regularity conditions,
  T(∫ g(x) f(x) dx) = ∫ T(g(x)) f(x) dx
where f is a Schwartz test function.

## Mathematical content

This is a consequence of the fact that continuous linear functionals
on Fréchet spaces commute with Bochner integrals. Since the Schwartz
space is nuclear Fréchet, and T is bounded by a finite sup of seminorms,
the exchange follows from:
1. The integrand x ↦ g(x) · f(x) converges in Schwartz topology
   (rapid decay of f kills any polynomial growth of seminorms of g)
2. T is continuous, so T(lim Σ) = lim Σ T(...)

This is NOT the same as `ContinuousLinearMap.integral_comp_comm`
(which requires Banach-valued integration). The Schwartz space version
needs the Fréchet topology, which is defined via WithSeminorms.

## References

- Treves, "Topological Vector Spaces", Ch. 34 (nuclear spaces)
- Reed-Simon I, §V.3 (distributions and Schwartz space)
- Vladimirov, "Methods of Generalized Functions", §25
-/

open MeasureTheory
noncomputable section

variable {m : ℕ}

-- **Axiom: CLM-integral exchange for Schwartz-valued families.**
--
-- If T is a CLM on Schwartz space, g : ℝᵐ → S(ℝᵐ) is a Schwartz-valued
-- family, Φ is a Schwartz function, and Φ(ξ) = ∫ g(x)(ξ) f(x) dx pointwise,
-- then T(Φ) = ∫ T(g(x)) f(x) dx.
--
-- The hypothesis hΦ_eq gives the pointwise identity: for each ξ,
-- Φ(ξ) equals the scalar integral of g(x)(ξ) * f(x) over x.
-- The conclusion exchanges T with the x-integral.
--
-- This is provable from Schwartz-valued Bochner integration theory
-- (not yet in Mathlib). The pointwise hypothesis avoids needing to
-- construct the Schwartz-valued integral explicitly.
axiom schwartz_clm_fubini_exchange {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (Φ : SchwartzMap (Fin m → ℝ) ℂ)
    -- Pointwise identity: Φ(ξ) = ∫ g(x)(ξ) * f(x) dx for each ξ
    (hΦ_eq : ∀ ξ : Fin m → ℝ,
      Φ ξ = ∫ x : Fin m → ℝ, g x ξ * f x)
    -- The scalar integrand T(g(x)) * f(x) is integrable
    (hint : Integrable (fun x => T (g x) * f x) volume)
    -- Uniform seminorm bound on g (ensures the Schwartz integral converges)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ (x : Fin m → ℝ),
        SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    T Φ = ∫ x : Fin m → ℝ, T (g x) * f x

end
