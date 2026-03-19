import OSReconstruction.SCV.SemigroupBochner

/-!
# Semigroup-Group Bochner Theorem

This file records the joint semigroup-group Bochner theorem for bounded
continuous positive-definite functions on `[0,∞) × ℝ^d`.

Mathematically, this is the Fourier-Laplace representation theorem for the
involutive semigroup
`(t, a) * (s, b) = (t + s, a + b)` with involution `(t, a)^* = (t, -a)`.

Reference: Berg--Christensen--Ressel, Theorem 4.1.13.
-/

open MeasureTheory Complex Set Filter Finset BigOperators
open scoped Topology

noncomputable section

namespace SCV

/-- A function on `[0,∞) × ℝ^d` is positive-definite with respect to the
involutive semigroup structure `(t, a)^* = (t, -a)`. -/
def IsSemigroupGroupPD (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ) (ts : Fin n → ℝ) (as : Fin n → (Fin d → ℝ)),
    (∀ i, 0 ≤ ts i) →
    let q := ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j *
        F (ts i + ts j) (as j - as i)
    q.im = 0 ∧ 0 ≤ q.re

/-- **Semigroup-group Bochner theorem** (BCR Theorem 4.1.13).

Bounded continuous positive-definite functions on `[0,∞) × ℝ^d` are
Fourier-Laplace transforms of finite positive measures on `[0,∞) × ℝ^d`. -/
axiom semigroupGroup_bochner (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : Continuous (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2))
    (hbdd : ∃ C : ℝ, ∀ t a, ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        F t a = ∫ p : ℝ × (Fin d → ℝ),
          Complex.exp (-(↑(t * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i))
          ∂μ

end SCV
