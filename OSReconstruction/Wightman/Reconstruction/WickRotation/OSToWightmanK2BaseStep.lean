/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.SCV.SemigroupGroupBochner
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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
  have hs :
      ∀ n,
        (∀ x : SpacetimeDim d, 0 ≤ ((φ n) x).re) ∧
        (∀ x : SpacetimeDim d, ((φ n) x).im = 0) ∧
        (∫ x : SpacetimeDim d, φ n x = 1) ∧
        HasCompactSupport (φ n : SpacetimeDim d → ℂ) ∧
        tsupport (φ n : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} ∧
        tsupport (φ n : SpacetimeDim d → ℂ) ⊆
          Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) := by
    intro n
    simpa [φ] using
      (Classical.choose_spec
        (exists_approx_identity_schwartz (d := d) (1 / (n + 1 : ℝ)) (by positivity)))
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    exact (hs n).1 x
  · intro n x
    exact (hs n).2.1 x
  · intro n
    exact (hs n).2.2.1
  · intro n
    exact (hs n).2.2.2.1
  · intro n
    exact (hs n).2.2.2.2.1
  · intro n
    exact (hs n).2.2.2.2.2

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
  let f1 : SchwartzNPoint d 1 :=
    SchwartzNPoint.osConj (d := d) (n := 1)
      (onePointToFin1CLM d φ : SchwartzNPoint d 1)
  let Fseq : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1 f1 hφ_pos
  let x : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from (⟦Fseq⟧)) : OSHilbertSpace OS))
  let Kext : ℝ → (Fin d → ℝ) → ℂ := fun t a =>
    if ht : 0 < t then
      osSemigroupGroupMatrixElement (d := d) OS lgc x t a
    else
      @inner ℂ (OSHilbertSpace OS) _ x
        ((osSpatialTranslateHilbert (d := d) OS a) x)
  have hf1_compact : HasCompactSupport ((f1 : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) := by
    let θSpace : SpacetimeDim d ≃ₜ SpacetimeDim d :=
      { toEquiv :=
          { toFun := timeReflection d
            invFun := timeReflection d
            left_inv := timeReflection_timeReflection (d := d)
            right_inv := timeReflection_timeReflection (d := d) }
        continuous_toFun := by
          refine continuous_pi ?_
          intro j
          by_cases hj : j = 0
          · subst hj
            simpa [timeReflection] using
              (continuous_apply (0 : Fin (d + 1))).neg
          · simpa [timeReflection, hj] using
              (continuous_apply j : Continuous fun y : SpacetimeDim d => y j)
        continuous_invFun := by
          refine continuous_pi ?_
          intro j
          by_cases hj : j = 0
          · subst hj
            simpa [timeReflection] using
              (continuous_apply (0 : Fin (d + 1))).neg
          · simpa [timeReflection, hj] using
              (continuous_apply j : Continuous fun y : SpacetimeDim d => y j) }
    have hreflect_space : HasCompactSupport (fun y : SpacetimeDim d => φ (timeReflection d y)) := by
      simpa using hφ_compact.comp_homeomorph θSpace
    have hreflect_fin1 :
        HasCompactSupport (fun y : NPointDomain d 1 => φ (timeReflection d (y 0))) := by
      simpa [onePointToFin1CLM] using
        (hreflect_space.comp_homeomorph
          ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph))
    simpa [f1, SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply] using
      (hreflect_fin1.comp_left (show starRingEnd ℂ (0 : ℂ) = 0 by simp))
  have hF_compact :
      ∀ n,
        HasCompactSupport ((((Fseq : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro n
    by_cases hn : n = 1
    · subst hn
      simpa [Fseq, f1, PositiveTimeBorchersSequence.single_toBorchersSequence] using
        hf1_compact
    · have hzero :
          ((((Fseq : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n :
              SchwartzNPoint d n) :
            NPointDomain d n → ℂ) = 0 := by
        simp [Fseq, PositiveTimeBorchersSequence.single_toBorchersSequence,
          BorchersSequence.single, hn]
      rw [hzero]
      simpa using (HasCompactSupport.zero : HasCompactSupport (0 : NPointDomain d n → ℂ))
  have hcont : Continuous (fun p : ℝ × (Fin d → ℝ) => Kext p.1 p.2) := by
    simpa [Kext, x, Fseq] using
      (continuous_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
        (d := d) OS lgc Fseq hF_compact)
  have hbdd : ∃ C : ℝ, ∀ t a, ‖Kext t a‖ ≤ C := by
    refine ⟨2 * ‖x‖ ^ 2, ?_⟩
    intro t a
    by_cases ht : 0 < t
    · have hU : osSpatialTranslateHilbert (d := d) OS a ∈
          unitary (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) := by
        constructor
        · exact osSpatialTranslateHilbert_unitary_left (d := d) OS a
        · exact osSpatialTranslateHilbert_unitary_right (d := d) OS a
      have hnormU :
          ‖(osSpatialTranslateHilbert (d := d) OS a) x‖ = ‖x‖ :=
        ContinuousLinearMap.norm_map_of_mem_unitary
          (u := osSpatialTranslateHilbert (d := d) OS a) hU x
      have hEq :
          osSemigroupGroupMatrixElement (d := d) OS lgc x t a =
            @inner ℂ (OSHilbertSpace OS) _
              ((osSpatialTranslateHilbert (d := d) OS (0 : Fin d → ℝ)) x)
              ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS a) x)) := by
        simpa using
          (osSemigroupGroupMatrixElement_eq_inner_timeShift_right
            (d := d) OS lgc x (0 : Fin d → ℝ) a t ht)
      calc
        ‖Kext t a‖ =
            ‖@inner ℂ (OSHilbertSpace OS) _
                ((osSpatialTranslateHilbert (d := d) OS (0 : Fin d → ℝ)) x)
                ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                  ((osSpatialTranslateHilbert (d := d) OS a) x))‖ := by
              simp [Kext, ht, hEq]
        _ =
            ‖@inner ℂ (OSHilbertSpace OS) _
                x
                ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                  ((osSpatialTranslateHilbert (d := d) OS a) x))‖ := by
              simp [osSpatialTranslateHilbert_zero]
        _ ≤ ‖x‖ *
            ‖(osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS a) x)‖ := by
              exact norm_inner_le_norm _ _
        _ ≤ ‖x‖ *
            (‖osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)‖ *
              ‖(osSpatialTranslateHilbert (d := d) OS a) x‖) := by
              gcongr
              exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖x‖ * (2 * ‖(osSpatialTranslateHilbert (d := d) OS a) x‖) := by
              gcongr
              exact osTimeShiftHilbertComplex_norm_le (d := d) OS lgc (t : ℂ) ht
        _ = ‖x‖ * (2 * ‖x‖) := by rw [hnormU]
        _ = 2 * ‖x‖ ^ 2 := by ring
    · have hU : osSpatialTranslateHilbert (d := d) OS a ∈
          unitary (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) := by
        constructor
        · exact osSpatialTranslateHilbert_unitary_left (d := d) OS a
        · exact osSpatialTranslateHilbert_unitary_right (d := d) OS a
      have hnormU :
          ‖(osSpatialTranslateHilbert (d := d) OS a) x‖ = ‖x‖ :=
        ContinuousLinearMap.norm_map_of_mem_unitary
          (u := osSpatialTranslateHilbert (d := d) OS a) hU x
      calc
        ‖Kext t a‖ =
            ‖@inner ℂ (OSHilbertSpace OS) _
                x ((osSpatialTranslateHilbert (d := d) OS a) x)‖ := by
              simp [Kext, ht]
        _ ≤ ‖x‖ * ‖(osSpatialTranslateHilbert (d := d) OS a) x‖ := by
              exact norm_inner_le_norm _ _
        _ = ‖x‖ * ‖x‖ := by rw [hnormU]
        _ ≤ 2 * ‖x‖ ^ 2 := by
              nlinarith [sq_nonneg ‖x‖]
  have hpd : SCV.IsSemigroupGroupPD d Kext := by
    simpa [Kext, x, Fseq] using
      (isSemigroupGroupPD_osSemigroupGroupMatrixElement_extension
        (d := d) OS lgc Fseq)
  rcases SCV.semigroupGroup_bochner d Kext hcont hbdd hpd with
    ⟨μ, hμfin, hμneg, hμrepr⟩
  refine ⟨μ, hμfin, hμneg, ?_⟩
  intro t a ht
  simpa [Kext, ht] using hμrepr t a (le_of_lt ht)

/-- The Laplace-Fourier kernel associated to a finite measure on
`[0,∞) × ℝ^d`. -/
def laplaceFourierKernel
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (ξ : SpacetimeDim d) : ℂ :=
  ∫ p : ℝ × (Fin d → ℝ),
    Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
      Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) ∂μ

/-- Fubini bridge for the finite-measure Laplace-Fourier kernel: pairing the
kernel against a positive-time compact Schwartz test is the same as integrating
the pointwise Fourier-Laplace transform of that test against the measure. This
is the exact first rewrite needed in theorem 3. -/
private theorem integral_laplaceFourierKernel_mul_eq
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * h ξ ∂volume =
      ∫ p : ℝ × (Fin d → ℝ),
        ∫ ξ : SpacetimeDim d,
          Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
            h ξ ∂volume ∂μ := by
  let f : SpacetimeDim d → (ℝ × (Fin d → ℝ)) → ℂ := fun ξ p =>
    Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
      Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
      h ξ
  let G : SpacetimeDim d × (ℝ × (Fin d → ℝ)) → ℂ := fun z => f z.1 z.2
  have hf_meas :
      AEStronglyMeasurable (Function.uncurry f) (volume.prod μ) := by
    have hcont_sum :
        Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
          ∑ i : Fin d, z.2.2 i * z.1 (Fin.succ i)) := by
      refine continuous_finset_sum _ fun i _hi => ?_
      exact
        (((continuous_apply i).comp (continuous_snd.comp continuous_snd)) : Continuous
          fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => z.2.2 i).mul
          (((continuous_apply (Fin.succ i)).comp continuous_fst) : Continuous
            fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => z.1 (Fin.succ i))
    have hcont :
        Continuous G := by
      change Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
        Complex.exp (-(↑(z.1 0 * z.2.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i : Fin d, z.2.2 i * z.1 (Fin.succ i))) *
          h z.1)
      have h1base : Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
          -((z.1 0) * z.2.1)) := by
        exact
          ((((continuous_apply (0 : Fin (d + 1))).comp continuous_fst) : Continuous
              fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => z.1 0).mul
            (((continuous_fst.comp continuous_snd) : Continuous
              fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => z.2.1))).neg
      have h1 : Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
          Complex.exp (-(↑(z.1 0 * z.2.1) : ℂ))) := by
        have h1' : Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
            Complex.exp (↑(-((z.1 0) * z.2.1)) : ℂ)) := by
          exact Complex.continuous_exp.comp (Complex.continuous_ofReal.comp h1base)
        simpa using h1'
      have h2 : Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
          Complex.exp (Complex.I * ↑(∑ i : Fin d, z.2.2 i * z.1 (Fin.succ i)))) := by
        exact
          Complex.continuous_exp.comp
            (continuous_const.mul (Complex.continuous_ofReal.comp hcont_sum))
      have h3 : Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => h z.1) := by
        exact (SchwartzMap.continuous h).comp continuous_fst
      simpa [G, f, mul_assoc] using h1.mul (h2.mul h3)
    simpa [Function.uncurry, f, G] using hcont.aestronglyMeasurable
  have hbound :
      ∀ᵐ z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) ∂(volume.prod μ),
        ‖Function.uncurry f z‖ ≤ ‖h z.1‖ := by
    have h_nonneg_p : ∀ᵐ p : ℝ × (Fin d → ℝ) ∂μ, 0 ≤ p.1 := by
      rw [Filter.Eventually, MeasureTheory.mem_ae_iff]
      suffices
          {p : ℝ × (Fin d → ℝ) | ¬ 0 ≤ p.1} ⊆ Set.prod (Set.Iio 0) Set.univ by
        exact le_antisymm (le_trans (μ.mono this) (le_of_eq hsupp)) (zero_le _)
      intro p hp
      rcases p with ⟨E, q⟩
      simp only [Set.mem_setOf_eq, not_le] at hp
      exact Set.mk_mem_prod hp (Set.mem_univ q)
    have h_nonneg_prod :
        ∀ᵐ z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) ∂(volume.prod μ), 0 ≤ z.2.1 := by
      have hmeas :
          MeasurableSet {z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) | 0 ≤ z.2.1} := by
        let g : SpacetimeDim d × (ℝ × (Fin d → ℝ)) → ℝ := fun z => z.2.1
        have hg : Measurable g := by
          exact (((continuous_fst.comp continuous_snd) : Continuous g).measurable)
        exact hg measurableSet_Ici
      rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas]
      exact Filter.Eventually.of_forall fun _ => h_nonneg_p
    filter_upwards [h_nonneg_prod] with z hz
    rcases z with ⟨ξ, p⟩
    have hp_nonneg : 0 ≤ p.1 := hz
    by_cases hhξ : h ξ = 0
    · simp [f, hhξ]
    · have hξ_pos : 0 < ξ 0 := by
        exact hh_pos (subset_tsupport (h : SpacetimeDim d → ℂ)
          (by rwa [Function.mem_support]))
      have hphase :
          (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))).re = 0 := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      have hexp_le_one :
          Real.exp (-(ξ 0 * p.1)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith [hξ_pos, hp_nonneg]
      calc
        ‖Function.uncurry f (ξ, p)‖
            = ‖Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i)))‖ *
              ‖h ξ‖ := by
                simp [f, mul_assoc]
        _ = Real.exp (-(ξ 0 * p.1)) * ‖h ξ‖ := by
              rw [norm_mul, Complex.norm_exp, Complex.norm_exp, hphase, Real.exp_zero, mul_one]
              simp
        _ ≤ 1 * ‖h ξ‖ := by
              gcongr
        _ = ‖h ξ‖ := by ring
  have hh_int :
      Integrable (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => h z.1) (volume.prod μ) := by
    simpa using ((h.integrable (μ := volume)).comp_fst μ)
  have hf_int : Integrable (Function.uncurry f) (volume.prod μ) := by
    exact (hh_int.norm).mono' hf_meas hbound
  calc
    ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * h ξ
        = ∫ ξ : SpacetimeDim d,
            ∫ p : ℝ × (Fin d → ℝ),
              f ξ p ∂μ := by
            congr 1
            ext ξ
            rw [laplaceFourierKernel, ← MeasureTheory.integral_mul_const]
    _ = ∫ p : ℝ × (Fin d → ℝ),
          ∫ ξ : SpacetimeDim d, f ξ p ∂volume ∂μ := by
            exact MeasureTheory.integral_integral_swap (f := f) hf_int
    _ = ∫ p : ℝ × (Fin d → ℝ),
          ∫ ξ : SpacetimeDim d,
            Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
              h ξ ∂volume ∂μ := by
            simp [f]

private lemma mul_exp_neg_bound_local (c t : ℝ) (hc : 0 < c) :
    t * Real.exp (-c * t) ≤ Real.exp (-1) / c := by
  rw [le_div_iff₀ hc]
  calc
    t * Real.exp (-c * t) * c = c * t * Real.exp (-c * t) := by ring
    _ ≤ Real.exp (c * t - 1) * Real.exp (-c * t) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (c * t - 1)]
    _ = Real.exp (-1) := by
      rw [← Real.exp_add]
      ring_nf

/-- Dominated convergence for real weights converging pointwise to `1`. This is
the exact smearing-removal engine needed for the approximate-identity Bochner
route: once the weighted spectral factors stay in `[0,1]`, any integrable test
function can be pushed through the limit. -/
private theorem tendsto_integral_mul_of_realWeights_to_one
    {α : Type} [MeasurableSpace α]
    (ρ : Measure α) [IsFiniteMeasure ρ]
    (f : α → ℂ) (hf : Integrable f ρ)
    (w : ℕ → α → ℝ)
    (hw_meas : ∀ n, Measurable (w n))
    (hw_nonneg : ∀ n x, 0 ≤ w n x)
    (hw_le : ∀ n x, w n x ≤ 1)
    (hw_lim : ∀ x, Tendsto (fun n => w n x) atTop (nhds 1)) :
    Tendsto (fun n => ∫ x, f x * (w n x : ℂ) ∂ρ) atTop (nhds (∫ x, f x ∂ρ)) := by
  let F : ℕ → α → ℂ := fun n x => f x * (w n x : ℂ)
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) ρ := by
    intro n
    exact hf.aestronglyMeasurable.mul
      ((Complex.continuous_ofReal.measurable.comp (hw_meas n)).aestronglyMeasurable)
  have h_bound : ∀ n, ∀ᵐ x ∂ρ, ‖F n x‖ ≤ ‖f x‖ := by
    intro n
    exact Filter.Eventually.of_forall fun x => by
      dsimp [F]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw_nonneg n x)]
      have hle : ‖f x‖ * w n x ≤ ‖f x‖ * 1 := by
        exact mul_le_mul_of_nonneg_left (hw_le n x) (norm_nonneg _)
      simpa using hle
  have h_lim : ∀ᵐ x ∂ρ, Tendsto (fun n => F n x) atTop (nhds (f x)) := by
    exact Filter.Eventually.of_forall fun x => by
      have hwc : Tendsto (fun n => ((w n x : ℝ) : ℂ)) atTop (nhds (1 : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp (hw_lim x)
      have hmul :
          Tendsto (fun n => f x * ((w n x : ℝ) : ℂ)) atTop (nhds (f x * (1 : ℂ))) :=
        Filter.Tendsto.const_mul (f x) hwc
      simpa [F] using hmul
  simpa [F] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      hF_meas hf.norm h_bound h_lim)

/-- Spectral bridge, step A: once a finite Bochner measure represents the
semigroup-group matrix element, pairing its Laplace-Fourier kernel against a
positive-time compact Schwartz test is the same as pairing the OS matrix element
itself against that test. -/
private theorem bochner_kernel_integral_eq_semigroup_integral
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (v : OSHilbertSpace OS)
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμ_repr : ∀ t a, 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc v t a =
        ∫ p, Complex.exp (-(↑(t * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i, p.2 i * a i)) ∂μ)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * h ξ =
      ∫ ξ : SpacetimeDim d,
        osSemigroupGroupMatrixElement (d := d) OS lgc v (ξ 0) (fun i => ξ (Fin.succ i)) *
          h ξ := by
  congr 1
  ext ξ
  by_cases hξ : (h : SpacetimeDim d → ℂ) ξ = 0
  · simp [hξ]
  · have hξ_pos : 0 < ξ 0 :=
      hh_pos (subset_tsupport (h : SpacetimeDim d → ℂ) (by rwa [Function.mem_support]))
    congr 1
    rw [hμ_repr (ξ 0) (fun i => ξ (Fin.succ i)) hξ_pos]
    simp [laplaceFourierKernel]

/-- Spectral bridge, step B: the semigroup-group matrix-element integral
attached to the one-point vector generated by `φ` is exactly the two-point
Schwinger value of the corresponding product-shell test. -/
private theorem semigroup_integral_eq_schwinger_productShell
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_int : ∫ u : SpacetimeDim d, φ u = 1)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    ∫ ξ : SpacetimeDim d,
        osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d φ : SchwartzNPoint d 1))
              hφ_pos⟧) : OSHilbertSpace OS))
          (ξ 0) (fun i => ξ (Fin.succ i)) * h ξ =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointProductLift φ h)) := by
  sorry

/-- Spectral bridge, step C: once the center factor has unit integral, the
product-shell pairing differs from the canonical difference lift by a single
explicit error term. -/
private theorem productShell_eq_differenceLift_plus_error
    (OS : OsterwalderSchraderAxioms d)
    (φ χ₀ h : SchwartzSpacetime d)
    (hφ_int : ∫ u : SpacetimeDim d, φ u = 1)
    (hχ₀_int : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0}) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointProductLift φ h)) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) +
        (OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointProductLift φ h)) -
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift φ h))) := by
  have h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) := by
    intro hz
    have hz' := hh_pos hz
    simpa using hz'
  have hcenter :
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift φ h)) =
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) := by
    rw [OsterwalderSchraderAxioms.twoPointDifferenceLift_eq_centerValue
      (d := d) OS h h0 χ₀ hχ₀_int φ]
    simp [hφ_int]
  calc
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointProductLift φ h))
        =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift φ h)) +
        (OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointProductLift φ h)) -
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift φ h))) := by
            ring
    _ =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) +
        (OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointProductLift φ h)) -
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift φ h))) := by
            rw [hcenter]

/-- Spectral bridge, step D: after replacing the Bochner measures by the scalar
spectral measure and removing the `|φ̂_n|²` weight by dominated convergence, the
approximate-identity kernel pairings converge to the canonical Schwinger
difference functional. This is the key smearing-removal step from OS II. -/
private theorem schwinger_error_tendsto_zero
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_support : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_pos : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hφ_onePoint_pos : ∀ n,
      tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (χ₀ : SchwartzSpacetime d) (hχ₀_int : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ))
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (hμ_fin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hμ_supp : ∀ n, (μ_seq n) (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμ_repr : ∀ n t a, 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
            (hφ_onePoint_pos n)⟧) : OSHilbertSpace OS))
        t a =
          ∫ p, Complex.exp (-(↑(t * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i, p.2 i * a i)) ∂(μ_seq n)) :
    Tendsto (fun n => ∫ ξ : SpacetimeDim d,
        laplaceFourierKernel (d := d) (μ_seq n) ξ * h ξ)
      atTop
      (nhds
        (OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)))) := by
  sorry

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
  let phase : (Fin d → ℝ) → (ℝ × (Fin d → ℝ)) → ℂ := fun ξ_s p =>
    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ_s i))
  let F : (Fin d → ℝ) → ℂ → (ℝ × (Fin d → ℝ)) → ℂ := fun ξ_s z p =>
    Complex.exp (-(z * ↑p.1)) * phase ξ_s p
  let F' : (Fin d → ℝ) → ℂ → (ℝ × (Fin d → ℝ)) → ℂ := fun ξ_s z p =>
    F ξ_s z p * -(↑p.1 : ℂ)
  refine ⟨fun z ξ_s => ∫ p, F ξ_s z p ∂μ, ?_, ?_⟩
  · intro ξ_s z₀ hz₀
    simp only [Set.mem_setOf_eq] at hz₀
    apply DifferentiableAt.differentiableWithinAt
    set δ : ℝ := z₀.re / 2 with hδ_def
    have hδ : 0 < δ := by
      linarith
    set c : ℝ := z₀.re - δ with hc_def
    have hc : 0 < c := by
      linarith
    have hsum_cont : Continuous (fun p : ℝ × (Fin d → ℝ) => ∑ i : Fin d, p.2 i * ξ_s i) := by
      refine continuous_finset_sum _ fun i _hi => ?_
      exact (((continuous_apply i).comp continuous_snd) : Continuous fun p : ℝ × (Fin d → ℝ) => p.2 i).mul
        (continuous_const : Continuous fun _ : ℝ × (Fin d → ℝ) => ξ_s i)
    have hphase_cont : Continuous (phase ξ_s) := by
      show Continuous (fun p : ℝ × (Fin d → ℝ) =>
        Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ_s i)))
      exact Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp hsum_cont))
    have hF_cont : ∀ z : ℂ, Continuous (F ξ_s z) := by
      intro z
      show Continuous (fun p : ℝ × (Fin d → ℝ) =>
        Complex.exp (-(z * ↑p.1)) * phase ξ_s p)
      exact
        (Complex.continuous_exp.comp
          ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).neg)).mul
          hphase_cont
    have hF'_cont : ∀ z : ℂ, Continuous (F' ξ_s z) := by
      intro z
      show Continuous (fun p : ℝ × (Fin d → ℝ) => F ξ_s z p * -(↑p.1 : ℂ))
      exact (hF_cont z).mul ((Complex.continuous_ofReal.comp continuous_fst).neg)
    have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F ξ_s z) μ := by
      exact Filter.Eventually.of_forall fun z => (hF_cont z).aestronglyMeasurable
    have hF_int : Integrable (F ξ_s z₀) μ := by
      apply Integrable.mono' (integrable_const (1 : ℝ))
      · exact
          (hF_cont z₀).aestronglyMeasurable
      · rw [ae_iff]
        apply measure_mono_null _ hsupp
        intro p hp
        refine Set.mem_prod.mpr ?_
        constructor
        · by_contra hp_nonneg
          apply hp
          have hp_nonneg' : 0 ≤ p.1 := le_of_not_gt hp_nonneg
          have hphase : (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ_s i) : ℂ).re = 0 := by
            simp
          have hre : (-(z₀ * ↑p.1) : ℂ).re = -z₀.re * p.1 := by
            simp [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]
          rw [show ‖F ξ_s z₀ p‖ =
              ‖Complex.exp (-(z₀ * ↑p.1)) * phase ξ_s p‖ by rfl]
          rw [Complex.norm_mul, Complex.norm_exp, Complex.norm_exp, hphase,
            Real.exp_zero, mul_one, hre, Real.exp_le_one_iff]
          nlinarith [hz₀, hp_nonneg']
        · exact Set.mem_univ _
    have hF'_meas : AEStronglyMeasurable (F' ξ_s z₀) μ := by
      exact (hF'_cont z₀).aestronglyMeasurable
    have h_bound :
        ∀ᵐ p ∂μ, ∀ z ∈ Metric.ball z₀ δ, ‖F' ξ_s z p‖ ≤ Real.exp (-1) / c := by
      rw [ae_iff]
      apply measure_mono_null _ hsupp
      intro p hp
      refine Set.mem_prod.mpr ?_
      constructor
      · by_contra hp_nonneg
        apply hp
        intro z hzball
        have hp_nonneg' : 0 ≤ p.1 := by
          exact le_of_not_gt hp_nonneg
        have hzre : z₀.re - δ ≤ z.re := by
          rw [Metric.mem_ball, dist_eq_norm] at hzball
          have habs : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
            simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - z₀)
          linarith [neg_abs_le (z.re - z₀.re)]
        have hphase : (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ_s i) : ℂ).re = 0 := by
          simp
        have hre : (-(z * ↑p.1) : ℂ).re = -z.re * p.1 := by
          simp [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]
        rw [show ‖F' ξ_s z p‖ =
            ‖Complex.exp (-(z * ↑p.1)) * phase ξ_s p * -(↑p.1 : ℂ)‖ by rfl]
        rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_exp, Complex.norm_exp,
          hphase, Real.exp_zero, mul_one, hre]
        have hnormp : ‖-(↑p.1 : ℂ)‖ = p.1 := by
          have hcast : (-(↑p.1 : ℂ)) = (((-p.1 : ℝ)) : ℂ) := by simp
          rw [hcast, Complex.norm_real, Real.norm_of_nonpos]
          · ring
          · linarith
        rw [hnormp]
        have hmain : Real.exp (-z.re * p.1) * p.1 ≤ Real.exp (-1) / c := by
          have h1 : p.1 * Real.exp (-z.re * p.1) ≤ p.1 * Real.exp (-(z₀.re - δ) * p.1) := by
            apply mul_le_mul_of_nonneg_left ?_ hp_nonneg'
            apply Real.exp_le_exp.mpr
            nlinarith
          simpa [mul_comm] using h1.trans (mul_exp_neg_bound_local c p.1 hc)
        exact hmain
      · exact Set.mem_univ _
    have h_bound_int : Integrable (fun _ : ℝ × (Fin d → ℝ) => (Real.exp (-1) / c : ℝ)) μ := by
      simpa using (integrable_const (Real.exp (-1) / c : ℝ))
    have h_diff : ∀ᵐ p ∂μ, ∀ z ∈ Metric.ball z₀ δ, HasDerivAt (F ξ_s · p) (F' ξ_s z p) z := by
      exact Filter.Eventually.of_forall fun p => by
        intro z hz
        have hlin : HasDerivAt (fun z : ℂ => -(z * ↑p.1)) (-(↑p.1 : ℂ)) z := by
          simpa [neg_mul] using (((hasDerivAt_id z).mul_const (↑p.1 : ℂ)).neg)
        simpa [F, F', phase, mul_assoc, mul_left_comm, mul_comm] using
          (hlin.cexp.mul_const (phase ξ_s p))
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (s := Metric.ball z₀ δ) (bound := fun _ => (Real.exp (-1) / c : ℝ))
      (F := F ξ_s) (F' := F' ξ_s) (Metric.ball_mem_nhds z₀ hδ)
      hF_meas hF_int hF'_meas h_bound h_bound_int h_diff).2.differentiableAt
  · intro t ξ_s ht
    simp [laplaceFourierKernel, F, phase, Fin.cons_zero, Fin.cons_succ]

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
