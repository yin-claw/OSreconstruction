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
continuous family g : ℝᵐ → S(ℝᵐ) with polynomial seminorm growth,
there exists a Schwartz function Φ such that
  Φ(ξ) = ∫ g(x)(ξ) f(x) dx  and  T(Φ) = ∫ T(g(x)) f(x) dx.

## Mathematical content

This combines two facts:
1. The Schwartz-valued integral Φ = ∫ g(x) f(x) dx is well-defined
   as a Schwartz function (polynomial growth of seminorms × rapid
   decay of f gives convergent Schwartz-valued integral).
2. T is continuous linear, so T(∫ ...) = ∫ T(...) (CLM exchange).

Both follow from the nuclearity/Fréchet structure of Schwartz space.

## References

- Hörmander, "The Analysis of Linear PDOs I", Ch. 5
- Reed-Simon I, §V.3
- Vladimirov, "Methods of Generalized Functions", §25
-/

open MeasureTheory
noncomputable section

variable {m : ℕ}

-- **Axiom: CLM-integral exchange for Schwartz-valued families.**
--
-- Given:
-- - T : continuous linear functional on Schwartz space
-- - g : continuous Schwartz-valued family with polynomial seminorm growth
-- - f : Schwartz test function
--
-- Conclusion: there exists a Schwartz function Φ (the Schwartz-valued integral)
-- such that Φ(ξ) = ∫ g(x)(ξ) f(x) dx pointwise, and T(Φ) = ∫ T(g(x)) f(x) dx.
--
-- The axiom constructs Φ rather than taking it as input, to avoid redundancy
-- and ensure coherence. The continuity hypothesis on g (in Schwartz topology)
-- ensures the Bochner integral is well-defined.
axiom schwartz_clm_fubini_exchange {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    -- Continuity of the Schwartz-valued family (ensures Bochner integrability)
    (hg_cont : Continuous g)
    -- Uniform seminorm bound (polynomial growth in x)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ (x : Fin m → ℝ),
        SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ (Φ : SchwartzMap (Fin m → ℝ) ℂ),
      (∀ ξ : Fin m → ℝ, Φ ξ = ∫ x : Fin m → ℝ, g x ξ * f x) ∧
      (T Φ = ∫ x : Fin m → ℝ, T (g x) * f x)

/-- **Finite-dimensional real-parameter CLM exchange.**

This is the finite-dimensional mixed-domain form needed by the GNS
spectral-condition argument.  The parameter space is one-dimensional (`ℝ`),
while the Schwartz functions live on a finite-dimensional real normed space
`E`; in the current downstream uses, `E` is an `NPointSpacetime` finite product
of real coordinates.

Given a continuous ℂ-linear functional `w` on `SchwartzMap E ℂ`, a continuous
Schwartz-valued family `G : ℝ → SchwartzMap E ℂ` with polynomial seminorm
growth in the real parameter, and a one-variable Schwartz test function `φ`,
the pointwise integral

`Θ ξ = ∫ t, φ t * G t ξ`

defines a Schwartz function on `E`, and `w` commutes with this integral.

This theorem is intentionally narrower than the previous arbitrary-domain
surface: finite dimensionality is the exact setting required by GNS and is the
setting in which this should be reducible to the existing same-domain axiom
`schwartz_clm_fubini_exchange`.

Lean-facing reduction plan from `schwartz_clm_fubini_exchange`:

1. Choose a continuous linear equivalence `E ≃L[ℝ] (Fin N → ℝ)` and transport
   `w` and `G t` to Schwartz functions on `Fin N → ℝ`.
2. Split `Fin N → ℝ` as `ℝ × (Fin (N - 1) → ℝ)`.
3. Choose a fixed Schwartz bump `ρ` on the tail coordinates with
   `∫ u, ρ u = 1`.
4. Apply `schwartz_clm_fubini_exchange` in dimension `N` to the padded data
   `x ↦ G (x₀)` and `x ↦ φ x₀ * ρ x_tail`.
5. Use finite-product Fubini and the normalization of `ρ` to collapse the
   `Fin N → ℝ` integral back to the real-parameter integral above.
6. Transport the resulting Schwartz function back along the chosen coordinate
   equivalence.

The remaining formal work is this coordinate-transport/padding/Fubini package;
the mathematical content is the same Schwartz-valued integral exchange as the
existing axiom, but with different finite-dimensional parameter and target
domains. -/
theorem schwartz_clm_fubini_exchange_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (w : SchwartzMap E ℂ → ℂ) (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w)
    (G : ℝ → SchwartzMap E ℂ) (hG_cont : Continuous G)
    (hG_poly : ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ t : ℝ,
        SchwartzMap.seminorm ℝ k j (G t) ≤ C * (1 + ‖t‖) ^ N)
    (φ : SchwartzMap ℝ ℂ) :
    ∃ Θ : SchwartzMap E ℂ,
      (∀ ξ : E, Θ ξ = ∫ t : ℝ, (φ : ℝ → ℂ) t * G t ξ) ∧
      w Θ = ∫ t : ℝ, w (G t) * (φ : ℝ → ℂ) t := by
  sorry

end
