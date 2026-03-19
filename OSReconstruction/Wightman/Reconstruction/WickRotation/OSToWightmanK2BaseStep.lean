/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.SCV.SemigroupGroupBochner

/-!
# `k = 2` Base-Step Decomposition

This file isolates the genuine mathematical subproblems behind the root blocker
`schwinger_continuation_base_step_timeParametric`.

The active decomposition is:

1. construct a positive-time approximate identity sequence,
2. apply semigroup-group Bochner to each approximate-identity vector state,
3. remove the `|φ̂_n|²` smearing and recover the Schwinger difference pairing,
4. prove the resulting limit kernel is holomorphic in the time variable,
5. assemble the `k = 2` time-parametric base-step witness.

These are theorem-level `sorry`s by design: they are the real intermediate
mathematical gaps on the OS route, not wrappers or repackagings.
-/

noncomputable section

open MeasureTheory Complex Filter Topology

variable {d : ℕ} [NeZero d]

/-- A sequence of nonnegative normalized positive-time Schwartz bumps with
compact support shrinking to the origin. -/
theorem exists_approx_identity_sequence :
    ∃ (φ : ℕ → SchwartzSpacetime d),
      (∀ n x, 0 ≤ (φ n x).re) ∧
      (∀ n x, (φ n x).im = 0) ∧
      (∀ n, ∫ x : SpacetimeDim d, φ n x = 1) ∧
      (∀ n, HasCompactSupport (φ n : SpacetimeDim d → ℂ)) ∧
      (∀ n, tsupport (φ n : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0}) ∧
      (∀ n, tsupport (φ n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ))) := by
  classical
  let φ : ℕ → SchwartzSpacetime d := fun n =>
    Classical.choose
      (exists_approx_identity_schwartz (d := d) (1 / (n + 1 : ℝ)) (by positivity))
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    rcases
      (Classical.choose_spec
        (exists_approx_identity_schwartz (d := d) (1 / (n + 1 : ℝ)) (by positivity))) with
      ⟨h_nonneg, -, -, -, -, -⟩
    exact h_nonneg x
  · intro n x
    rcases
      (Classical.choose_spec
        (exists_approx_identity_schwartz (d := d) (1 / (n + 1 : ℝ)) (by positivity))) with
      ⟨-, h_im, -, -, -, -⟩
    exact h_im x
  · intro n
    rcases
      (Classical.choose_spec
        (exists_approx_identity_schwartz (d := d) (1 / (n + 1 : ℝ)) (by positivity))) with
      ⟨-, -, h_int, -, -, -⟩
    exact h_int
  · intro n
    rcases
      (Classical.choose_spec
        (exists_approx_identity_schwartz (d := d) (1 / (n + 1 : ℝ)) (by positivity))) with
      ⟨-, -, -, h_compact, -, -⟩
    exact h_compact
  · intro n
    rcases
      (Classical.choose_spec
        (exists_approx_identity_schwartz (d := d) (1 / (n + 1 : ℝ)) (by positivity))) with
      ⟨-, -, -, -, h_pos, -⟩
    exact h_pos
  · intro n
    rcases
      (Classical.choose_spec
        (exists_approx_identity_schwartz (d := d) (1 / (n + 1 : ℝ)) (by positivity))) with
      ⟨-, -, -, -, -, h_ball⟩
    exact h_ball

/-- Apply semigroup-group Bochner to the OS matrix element attached to a
single normalized positive-time one-point vector. -/
theorem exists_bochner_measure_for_approx_identity
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
        osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d φ : SchwartzNPoint d 1))
              hφ_pos⟧) : OSHilbertSpace OS)) t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ := by
  sorry

/-- The Laplace-Fourier kernel associated to a finite measure on
`[0,∞) × ℝ^d`. -/
def laplaceFourierKernel
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (ξ : SpacetimeDim d) : ℂ :=
  ∫ p : ℝ × (Fin d → ℝ),
    Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
      Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) ∂μ

/-- Smearing removal for the approximate-identity/Bochner route: the limit
Laplace-Fourier kernel reproduces the normalized-center two-point Schwinger
difference shell on positive-time compact-support tests. -/
theorem limit_bochner_kernel_reproduces_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀_int : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      ContinuousOn (laplaceFourierKernel (d := d) μ) {ξ : SpacetimeDim d | 0 < ξ 0} ∧
      (∃ C : ℝ, ∀ ξ, 0 < ξ 0 → ‖laplaceFourierKernel (d := d) μ ξ‖ ≤ C) ∧
      AEStronglyMeasurable (laplaceFourierKernel (d := d) μ) volume ∧
      ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * h ξ =
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) := by
  sorry

/-- The limit Laplace-Fourier kernel extends holomorphically in the time
variable on the right half-plane. -/
theorem limit_kernel_time_holomorphic
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0) :
    ∃ (K_ext : ℂ → (Fin d → ℝ) → ℂ),
      (∀ ξ_s : Fin d → ℝ,
        DifferentiableOn ℂ (fun z => K_ext z ξ_s) {z : ℂ | 0 < z.re}) ∧
      (∀ (t : ℝ) (ξ_s : Fin d → ℝ), 0 < t →
        K_ext (t : ℂ) ξ_s =
          laplaceFourierKernel (d := d) μ (Fin.cons t (fun i => ξ_s i))) := by
  sorry

/-- The `k = 2` time-parametric base step obtained by assembling the previous
sub-lemmas. -/
theorem schwinger_continuation_base_step_timeParametric_k2
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))) * (f.1 x)) := by
  sorry

end
