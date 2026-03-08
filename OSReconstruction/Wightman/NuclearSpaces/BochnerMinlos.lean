/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OSReconstruction.Wightman.NuclearSpaces.NuclearSpace
import OSReconstruction.Wightman.NuclearSpaces.GaussianFieldBridge
import OSReconstruction.Wightman.NuclearSpaces.Helpers.PositiveDefiniteKernels

/-!
# Positive-Definite Functionals and Gaussian Characteristic Helpers

This file retains the sorry-free positive-definite and characteristic-functional
infrastructure used by the nuclear-space side lane.

The classical Bochner/Minlos measure-construction chain that previously lived here
was unused by the active reconstruction path and remained isolated behind `sorry`s.
That theorem surface has been removed rather than carried as dead unfinished code.

## Main Definitions

* `IsPositiveDefiniteFn` - A function φ : E → ℂ is positive-definite if
  Σᵢⱼ c̄ᵢ cⱼ φ(xⱼ - xᵢ) ≥ 0 for all finite families.
* `CharacteristicFunctional` - A continuous positive-definite functional C : E → ℂ
  with C(0) = 1, on a nuclear space E.
* `gaussianCharacteristicFunctional` - Gaussian characteristic kernel on a Hilbert space

## Mathematical Background

The remaining content here is purely algebraic/analytic infrastructure around
positive-definite functions and normalized characteristic functionals. The actual
measure-construction theorems are deferred until the project needs a genuine proof.

## References

* Minlos, "Generalized random processes and their extension to a measure" (1959)
* Gel'fand-Vilenkin, "Generalized Functions IV" (1964), Ch. IV
* Reed-Simon, "Methods of Modern Mathematical Physics I", Theorem V.10
* Glimm-Jaffe, "Quantum Physics" (1987), Ch. 6
-/

noncomputable section

open MeasureTheory Complex
open scoped NNReal Topology

/-! ### Positive-Definite Functions -/

/-- A function φ : E → ℂ on an abelian group is **positive-definite** if
    for every finite family of points x₁, ..., xₙ ∈ E and scalars c₁, ..., cₙ ∈ ℂ,
    the Hermitian form Σᵢ Σⱼ c̄ᵢ · cⱼ · φ(xⱼ - xᵢ) is a non-negative real number.

    This is equivalent to requiring the kernel matrix [φ(xⱼ - xᵢ)] to be
    positive semi-definite (Hermitian with non-negative eigenvalues).

    The standard notion from harmonic analysis (Rudin, Folland). -/
def IsPositiveDefiniteFn {E : Type*} [AddCommGroup E] (φ : E → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → E) (c : Fin n → ℂ),
    let S := ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * φ (x j - x i)
    S.im = 0 ∧ 0 ≤ S.re

section PositiveDefiniteProps

variable {E : Type*} [AddCommGroup E] {φ : E → ℂ}

/-- A positive-definite function satisfies φ(0) ≥ 0 (taking n=1, c₁=1, x₁=0).
    Moreover, φ(0) is real (imaginary part is 0). -/
theorem IsPositiveDefiniteFn.eval_zero_nonneg (hφ : IsPositiveDefiniteFn φ) :
    0 ≤ (φ 0).re := by
  have h := hφ 1 (fun _ => 0) (fun _ => 1)
  simp only [Fin.sum_univ_one, sub_self, map_one, one_mul] at h
  exact h.2

/-- φ(0) is real for a positive-definite function. -/
theorem IsPositiveDefiniteFn.eval_zero_im (hφ : IsPositiveDefiniteFn φ) :
    (φ 0).im = 0 := by
  have h := hφ 1 (fun _ => 0) (fun _ => 1)
  simp only [Fin.sum_univ_one, sub_self, map_one, one_mul] at h
  exact h.1

/-- A positive-definite function satisfies φ(-x) = conj(φ(x)).

    Proof: The 2×2 kernel matrix M = [[φ(0), φ(x)], [φ(-x), φ(0)]] must be
    Hermitian (since c*Mc is real for all c). The off-diagonal Hermiticity
    M₂₁ = conj(M₁₂) gives φ(-x) = conj(φ(x)). -/
theorem IsPositiveDefiniteFn.conj_neg (hφ : IsPositiveDefiniteFn φ) (x : E) :
    starRingEnd ℂ (φ x) = φ (-x) := by
  have h1 := hφ 2 ![0, x] ![1, 1]
  have h2 := hφ 2 ![0, x] ![1, Complex.I]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, sub_zero, zero_sub, neg_zero, map_one, one_mul, mul_one] at h1 h2
  obtain ⟨h1_im, _⟩ := h1
  obtain ⟨h2_im, _⟩ := h2
  have hφ0_im := hφ.eval_zero_im
  apply Complex.ext
  · -- Re(conj(φ x)) = Re(φ(-x)), i.e., Re(φ x) = Re(φ(-x))
    simp only [Complex.conj_re]
    -- Extract imaginary parts using mul_im AND mul_re (needed for (conj(I)*I).re evaluation)
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im] at h2_im
    -- Clean up numerical arithmetic (0*a, 1*a, a-(-b), etc.)
    ring_nf at h2_im
    linarith
  · -- Im(conj(φ x)) = Im(φ(-x)), i.e., -Im(φ x) = Im(φ(-x))
    simp only [Complex.conj_im]
    simp only [Complex.add_im] at h1_im
    linarith

/-- A positive-definite function satisfies |φ(x)| ≤ φ(0) for all x.

    Proof: The 2×2 PSD matrix [[φ(0), φ(x)], [conj(φ(x)), φ(0)]] has
    non-negative determinant: φ(0)² - |φ(x)|² ≥ 0. -/
theorem IsPositiveDefiniteFn.norm_le_eval_zero (hφ : IsPositiveDefiniteFn φ) (x : E) :
    ‖φ x‖ ≤ (φ 0).re := by
  by_cases hφx : φ x = 0
  · simp [hφx, hφ.eval_zero_nonneg]
  · -- Use c₁=‖φ x‖, c₂=-conj(φ x). Then S.re = 2‖φ x‖²((φ 0).re - ‖φ x‖) ≥ 0.
    have hznorm_pos : (0 : ℝ) < ‖φ x‖ := norm_pos_iff.mpr hφx
    have hφ_neg := hφ.conj_neg x
    have hφ0_im := hφ.eval_zero_im
    have h := hφ 2 ![0, x] ![(↑‖φ x‖ : ℂ), -(starRingEnd ℂ (φ x))]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      sub_self, sub_zero, zero_sub, neg_zero] at h
    -- Replace φ(-x) → starRingEnd ℂ (φ x), so hss can simplify conj(conj(φ x)) = φ x
    -- hφ_neg : starRingEnd ℂ (φ x) = φ (-x), so ← replaces φ(-x) with starRingEnd ℂ (φ x)
    rw [← hφ_neg] at h
    -- Simplify: conj(conj(z))=z, conj(↑r)=↑r, conj(-z)=-conj(z)
    have hss : starRingEnd ℂ (starRingEnd ℂ (φ x)) = φ x := star_star (φ x)
    simp only [map_neg, hss, Complex.conj_ofReal] at h
    obtain ⟨_, h_re⟩ := h
    -- Fully expand .re to real arithmetic (need mul_im for intermediate .im terms)
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im,
      mul_zero, zero_mul, sub_zero, add_zero,
      neg_mul, mul_neg, neg_neg, neg_zero] at h_re
    -- Normalize the real polynomial expression (collects terms, cancels double negations)
    ring_nf at h_re
    -- Key identity: ‖z‖² = z.re² + z.im²
    have hnormsq : (φ x).re ^ 2 + (φ x).im ^ 2 = ‖φ x‖ ^ 2 := by
      rw [sq, sq]; exact (RCLike.norm_sq_eq_def (K := ℂ)).symm
    -- Factor out using hnormsq: the sum = 2‖φ x‖²·((φ 0).re - ‖φ x‖)
    -- Derive (φ 0).re ≥ ‖φ x‖ by dividing by 2‖φ x‖² > 0
    suffices hsuff : 0 ≤ (φ 0).re - ‖φ x‖ by linarith
    by_contra h_neg
    push_neg at h_neg
    -- Substitute hnormsq into h_re via helper equalities
    have hp : (φ 0).re * (φ x).re ^ 2 + (φ 0).re * (φ x).im ^ 2 =
        (φ 0).re * ‖φ x‖ ^ 2 := by rw [← mul_add, hnormsq]
    have hr : ‖φ x‖ * (φ x).re ^ 2 + ‖φ x‖ * (φ x).im ^ 2 = ‖φ x‖ ^ 3 := by
      rw [← mul_add, hnormsq]; ring
    -- 0 < ‖φ x‖² * (‖φ x‖ - (φ 0).re) since both factors positive
    have h_prod : 0 < ‖φ x‖ ^ 2 * (‖φ x‖ - (φ 0).re) :=
      mul_pos (by positivity) (by linarith)
    -- Linear combination: h_re + hp substitution + hr substitution + h_prod → 0 > 0
    linarith [hp, hr, h_prod]

end PositiveDefiniteProps

/-! ### Characteristic Functionals -/

/-- A **characteristic functional** on a topological vector space E is a continuous
    function C : E → ℂ that is positive-definite and satisfies C(0) = 1.

    When E is a nuclear space, Minlos' theorem guarantees that C is the
    "Fourier transform" of a unique probability measure on E*.

    Examples:
    - Free scalar field: C(f) = exp(-½ ⟨f, (-Δ+m²)⁻¹ f⟩)
    - Gaussian: C(f) = exp(-½ ⟨f, Af⟩) for positive operator A -/
structure CharacteristicFunctional (E : Type*) [AddCommGroup E]
    [TopologicalSpace E] where
  /-- The functional C : E → ℂ -/
  toFun : E → ℂ
  /-- C is continuous -/
  continuous_toFun : Continuous toFun
  /-- C is positive-definite -/
  positive_definite : IsPositiveDefiniteFn toFun
  /-- C(0) = 1 -/
  eval_zero : toFun 0 = 1

namespace CharacteristicFunctional

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]

/-- The characteristic functional is bounded by 1. -/
theorem norm_le_one (C : CharacteristicFunctional E) (x : E) : ‖C.toFun x‖ ≤ 1 := by
  have h := C.positive_definite.norm_le_eval_zero x
  rw [C.eval_zero] at h
  simp at h
  exact h

end CharacteristicFunctional

/-! ### Deferred measure-construction lane

The finite-dimensional Bochner theorem and infinite-dimensional Minlos theorem are
not part of the active reconstruction path in this repository. Their previous theorem
surface was unused outside the isolated `EuclideanMeasure` side lane and remained
behind `sorry`s, so it has been removed.

If the measure-construction lane is revived, it should return with a genuine proof of
the finite-dimensional existence/tightness step and the infinite-dimensional projective
limit/tightness step, rather than placeholder theorem fronts. -/

/-! ### Gaussian Characteristic Functionals -/

/-- A **Gaussian characteristic functional** on a Hilbert space H is given by
    C(f) = exp(-½ ⟨f, Af⟩) where A : H → H is a positive trace-class operator.

    This is the characteristic functional of a centered Gaussian measure on H. -/
def gaussianCharacteristicFunctional {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (_hA_pos : ∀ x, 0 ≤ @inner ℝ H _ x (A x)) :
    H → ℂ :=
  fun f => exp (-(1/2 : ℂ) * ↑(@inner ℝ H _ f (A f)))

/-- The Gaussian characteristic functional at 0 equals 1. -/
theorem gaussianCharacteristicFunctional_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (hA_pos : ∀ x, 0 ≤ @inner ℝ H _ x (A x)) :
    gaussianCharacteristicFunctional A hA_pos 0 = 1 := by
  simp [gaussianCharacteristicFunctional]

/-- The Gaussian characteristic functional is positive-definite.

    This follows from the fact that exp(-½ Q(f)) where Q is a positive quadratic
    form is positive-definite (by expanding the exponential and using the positive
    definiteness of each power of Q). -/
theorem gaussianCharacteristicFunctional_posdef {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (hA_pos : ∀ x, 0 ≤ @inner ℝ H _ x (A x)) :
    IsPositiveDefiniteFn (gaussianCharacteristicFunctional A hA_pos) := by
  intro n x c
  -- Convert complex exponential to real exponential cast to ℂ
  have hconv : ∀ f : H,
      gaussianCharacteristicFunctional A hA_pos f =
      ↑(Real.exp (-(1/2 : ℝ) * @inner ℝ H _ f (A f))) := by
    intro f
    simp only [gaussianCharacteristicFunctional]
    rw [show -(1/2 : ℂ) * ↑(@inner ℝ H _ f (A f)) =
        ↑(-(1/2 : ℝ) * @inner ℝ H _ f (A f)) from by push_cast; ring]
    exact Complex.ofReal_exp (-(1/2 : ℝ) * @inner ℝ H _ f (A f)) |>.symm
  simp_rw [hconv]
  exact gaussian_kernel_posdef A hA_pos x c

end
