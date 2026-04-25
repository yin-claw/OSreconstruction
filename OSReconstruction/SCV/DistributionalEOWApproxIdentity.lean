/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWRepresentative
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Compact Approximate-Identity Kernels for Distributional EOW

This file starts the pure-SCV approximate-identity layer needed after the
checked product-kernel `∂bar` and distributional-holomorphicity bridge.
-/

noncomputable section

open Complex MeasureTheory Metric Set Filter
open LineDeriv

namespace SCV

variable {m : ℕ}

/-- For every positive radius there is a normalized real nonnegative
complex-valued Schwartz bump whose topological support is contained in the
closed ball of that radius. -/
theorem exists_normalized_schwartz_bump_kernelSupportWithin
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ t : Fin m → ℝ, 0 ≤ (ψ t).re) ∧
      (∀ t : Fin m → ℝ, (ψ t).im = 0) ∧
      (∫ t : Fin m → ℝ, ψ t = 1) ∧
      KernelSupportWithin ψ ε := by
  let c : Fin m → ℝ := 0
  let b : ContDiffBump c := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  let f : (Fin m → ℝ) → ℂ := fun t => (b t : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let g₀ : SchwartzMap (Fin m → ℝ) ℂ :=
    hf_compact.toSchwartzMap hf_smooth
  have hg₀_apply : ∀ t, g₀ t = f t :=
    HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth
  have hg₀_int_ne : ∫ t : Fin m → ℝ, g₀ t ≠ 0 := by
    change ∫ t, (↑(b t) : ℂ) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt b.integral_pos)
  let ψ : SchwartzMap (Fin m → ℝ) ℂ := (∫ t : Fin m → ℝ, g₀ t)⁻¹ • g₀
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro t
    simp only [ψ, SchwartzMap.smul_apply, smul_eq_mul]
    rw [Complex.mul_re]
    have hg₀_im : (g₀ t).im = 0 := by
      rw [hg₀_apply t]
      exact Complex.ofReal_im (b t)
    have hg₀_re : 0 ≤ (g₀ t).re := by
      rw [hg₀_apply t]
      exact Complex.ofReal_re (b t) ▸ b.nonneg
    have hint_im : (∫ u : Fin m → ℝ, g₀ u).im = 0 := by
      change (∫ u : Fin m → ℝ, (↑(b u) : ℂ)).im = 0
      rw [integral_complex_ofReal]
      simp
    have hinv_im : ((∫ u : Fin m → ℝ, g₀ u)⁻¹).im = 0 := by
      rw [Complex.inv_im, hint_im]
      ring_nf
    rw [hg₀_im, hinv_im]
    ring_nf
    apply mul_nonneg _ hg₀_re
    rw [Complex.inv_re]
    apply div_nonneg
    · change 0 ≤ (∫ u : Fin m → ℝ, (↑(b u) : ℂ)).re
      rw [integral_complex_ofReal]
      simp only [Complex.ofReal_re]
      exact le_of_lt b.integral_pos
    · exact Complex.normSq_nonneg _
  · intro t
    simp only [ψ, SchwartzMap.smul_apply, smul_eq_mul]
    rw [Complex.mul_im]
    have hg₀_im : (g₀ t).im = 0 := by
      rw [hg₀_apply t]
      exact Complex.ofReal_im (b t)
    have hint_im : (∫ u : Fin m → ℝ, g₀ u).im = 0 := by
      change (∫ u : Fin m → ℝ, (↑(b u) : ℂ)).im = 0
      rw [integral_complex_ofReal]
      simp
    have hinv_im : ((∫ u : Fin m → ℝ, g₀ u)⁻¹).im = 0 := by
      rw [Complex.inv_im, hint_im]
      ring_nf
    rw [hg₀_im, hinv_im]
    ring_nf
  · simp only [ψ, SchwartzMap.smul_apply, smul_eq_mul]
    calc
      ∫ t : Fin m → ℝ, (∫ t : Fin m → ℝ, g₀ t)⁻¹ * g₀ t =
          (∫ t : Fin m → ℝ, g₀ t)⁻¹ * ∫ t : Fin m → ℝ, g₀ t := by
        exact MeasureTheory.integral_const_mul
          ((∫ t : Fin m → ℝ, g₀ t)⁻¹) (fun t : Fin m → ℝ => g₀ t)
      _ = 1 := inv_mul_cancel₀ hg₀_int_ne
  · intro t ht
    have hsubset :
        tsupport (ψ : (Fin m → ℝ) → ℂ) ⊆
          tsupport (g₀ : (Fin m → ℝ) → ℂ) := by
      exact tsupport_smul_subset_right
        (fun _ : Fin m → ℝ => (∫ u : Fin m → ℝ, g₀ u)⁻¹)
        (g₀ : (Fin m → ℝ) → ℂ)
    have ht_supp : t ∈ Metric.closedBall c (ε / 2 : ℝ) := by
      have h_tsup_f : tsupport f ⊆ Metric.closedBall c (ε / 2) := by
        intro y hy
        rw [← b.tsupport_eq]
        exact tsupport_comp_subset Complex.ofReal_zero _ hy
      exact h_tsup_f (hsubset ht)
    rw [Metric.mem_closedBall] at ht_supp ⊢
    have hc : c = (0 : Fin m → ℝ) := rfl
    rw [hc] at ht_supp
    linarith

/-- A normalized compact bump sequence whose support radius shrinks to zero
and is always contained in a prescribed positive ball. -/
theorem exists_shrinking_normalized_schwartz_bump_sequence
    {r : ℝ} (hr : 0 < r) :
    ∃ ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ,
      (∀ n t, 0 ≤ (ψn n t).re) ∧
      (∀ n t, (ψn n t).im = 0) ∧
      (∀ n, ∫ t : Fin m → ℝ, ψn n t = 1) ∧
      (∀ n,
        KernelSupportWithin (ψn n)
          (min (r / 2) (1 / (n + 1 : ℝ)))) ∧
      (∀ n, KernelSupportWithin (ψn n) r) := by
  classical
  let εn : ℕ → ℝ := fun n => min (r / 2) (1 / (n + 1 : ℝ))
  have hεn_pos : ∀ n, 0 < εn n := by
    intro n
    exact lt_min (by linarith) (by positivity)
  let ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ := fun n =>
    Classical.choose
      (exists_normalized_schwartz_bump_kernelSupportWithin
        (m := m) (εn n) (hεn_pos n))
  have hspec :
      ∀ n,
        (∀ t : Fin m → ℝ, 0 ≤ (ψn n t).re) ∧
        (∀ t : Fin m → ℝ, (ψn n t).im = 0) ∧
        (∫ t : Fin m → ℝ, ψn n t = 1) ∧
        KernelSupportWithin (ψn n) (εn n) := by
    intro n
    simpa [ψn] using
      (Classical.choose_spec
        (exists_normalized_schwartz_bump_kernelSupportWithin
          (m := m) (εn n) (hεn_pos n)))
  refine ⟨ψn, ?_, ?_, ?_, ?_, ?_⟩
  · intro n t
    exact (hspec n).1 t
  · intro n t
    exact (hspec n).2.1 t
  · intro n
    exact (hspec n).2.2.1
  · intro n
    simpa [εn] using (hspec n).2.2.2
  · intro n t ht
    have ht' := (hspec n).2.2.2 ht
    rw [Metric.mem_closedBall] at ht' ⊢
    have hle : εn n ≤ r := by
      calc
        εn n ≤ r / 2 := min_le_left _ _
        _ ≤ r := by linarith
    exact le_trans ht' hle

/-- The real embedding into the complex chart is norm nonincreasing for the
coordinate supremum norms used on finite products. -/
theorem norm_realEmbed_le (t : Fin m → ℝ) :
    ‖realEmbed t‖ ≤ ‖t‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg t)]
  intro i
  simp [realEmbed, Complex.norm_real]
  exact norm_le_pi_norm t i

/-- The real embedding into the complex chart is continuous. -/
theorem continuous_realEmbed :
    Continuous (realEmbed : (Fin m → ℝ) → ComplexChartSpace m) := by
  exact continuous_pi fun i =>
    Complex.continuous_ofReal.comp (continuous_apply i)

/-- Local continuous-linear form of `realEmbed`, used only to compute the
base derivative of the sheared real-convolution tensor. -/
private def realEmbedCLMApprox : (Fin m → ℝ) →L[ℝ] ComplexChartSpace m :=
  ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

@[simp]
private theorem realEmbedCLMApprox_apply (t : Fin m → ℝ) :
    realEmbedCLMApprox t = realEmbed t := by
  ext i
  simp [realEmbedCLMApprox, realEmbed]

/-- A kernel supported in a closed ball vanishes outside that ball. -/
theorem kernel_eq_zero_of_not_mem_closedBall
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) {r : ℝ} {t : Fin m → ℝ}
    (hψ : KernelSupportWithin ψ r)
    (ht : t ∉ Metric.closedBall (0 : Fin m → ℝ) r) :
    ψ t = 0 := by
  exact image_eq_zero_of_notMem_tsupport (fun htψ => ht (hψ htψ))

/-- A real-valued nonnegative normalized complex Schwartz kernel has `L¹`
mass one. -/
theorem integral_norm_eq_one_of_real_nonneg_normalized
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_nonneg : ∀ t : Fin m → ℝ, 0 ≤ (ψ t).re)
    (hψ_real : ∀ t : Fin m → ℝ, (ψ t).im = 0)
    (hψ_norm : ∫ t : Fin m → ℝ, ψ t = 1) :
    ∫ t : Fin m → ℝ, ‖ψ t‖ = 1 := by
  have hnorm_point : ∀ t : Fin m → ℝ, ‖ψ t‖ = (ψ t).re := by
    intro t
    have hz : ψ t = ((ψ t).re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hψ_real t]
    calc
      ‖ψ t‖ = ‖((ψ t).re : ℂ)‖ := congrArg norm hz
      _ = ‖(ψ t).re‖ := Complex.norm_real _
      _ = |(ψ t).re| := Real.norm_eq_abs _
      _ = (ψ t).re := abs_of_nonneg (hψ_nonneg t)
  calc
    ∫ t : Fin m → ℝ, ‖ψ t‖ = ∫ t : Fin m → ℝ, (ψ t).re := by
      exact integral_congr_ae (Filter.Eventually.of_forall hnorm_point)
    _ = (∫ t : Fin m → ℝ, ψ t).re := by
      exact integral_re ψ.integrable
    _ = 1 := by
      rw [hψ_norm]
      norm_num

/-- Iterated real derivatives commute with subtracting a fixed real embedded
translation in the complex-chart variable. -/
theorem iteratedFDeriv_sub_realEmbed_right
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (t : Fin m → ℝ) (l : ℕ) (z : ComplexChartSpace m) :
    iteratedFDeriv ℝ l
      (fun z : ComplexChartSpace m => θ (z - realEmbed t)) z =
      iteratedFDeriv ℝ l
        (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) := by
  simpa [sub_eq_add_neg] using
    (iteratedFDeriv_comp_add_right
      (f := (θ : ComplexChartSpace m → ℂ)) l (-(realEmbed t)) z)

/-- The translated `l`-th derivative field, multiplied by a Schwartz real
kernel, is Bochner integrable in the real kernel variable. -/
theorem integrable_smul_iteratedFDeriv_translate
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (l : ℕ) (z : ComplexChartSpace m) :
    Integrable (fun t : Fin m → ℝ =>
      (ψ t) • iteratedFDeriv ℝ l
        (θ : ComplexChartSpace m → ℂ) (z - realEmbed t)) := by
  let C : ℝ := SchwartzMap.seminorm ℂ 0 l θ
  have hmajor : Integrable (fun t : Fin m → ℝ => C * ‖ψ t‖) := by
    exact ψ.integrable.norm.const_mul C
  refine hmajor.mono' ?_ ?_
  · have hsub : Continuous fun t : Fin m → ℝ => z - realEmbed t := by
      exact continuous_const.sub (continuous_realEmbed (m := m))
    have hcontD : Continuous fun t : Fin m → ℝ =>
        iteratedFDeriv ℝ l
          (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) :=
      ((θ.smooth l).continuous_iteratedFDeriv le_rfl).comp hsub
    exact (ψ.continuous.smul hcontD).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_smul]
    have hD :
        ‖iteratedFDeriv ℝ l
          (θ : ComplexChartSpace m → ℂ) (z - realEmbed t)‖ ≤ C := by
      simpa [C] using
        SchwartzMap.norm_iteratedFDeriv_le_seminorm
          (𝕜 := ℂ) θ l (z - realEmbed t)
    nlinarith [norm_nonneg (ψ t)]

/-- Zeroth-order case of differentiating the real convolution test under the
real fiber integral. -/
theorem iteratedFDeriv_zero_realConvolutionTest_eq_integral
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (z : ComplexChartSpace m) :
    iteratedFDeriv ℝ 0
      (realConvolutionTest θ ψ : ComplexChartSpace m → ℂ) z =
      ∫ t : Fin m → ℝ,
        (ψ t) • iteratedFDeriv ℝ 0
          (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) := by
  ext v
  rw [iteratedFDeriv_zero_apply]
  rw [ContinuousMultilinearMap.integral_apply
    (integrable_smul_iteratedFDeriv_translate θ ψ 0 z) v]
  simp [realConvolutionTest_apply, iteratedFDeriv_zero_apply, mul_comm]

/-- Base-variable derivative of the pointwise sheared tensor product.  The
fiber derivative of `ψ` drops out because we evaluate only along the complex
chart direction. -/
theorem fderiv_shearedTensor_base_apply
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (z v : ComplexChartSpace m) (t : Fin m → ℝ) :
    fderiv ℝ (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
      θ (p.1 - realEmbed p.2) * ψ p.2) (z, t)
      ((ContinuousLinearMap.inl ℝ (ComplexChartSpace m) (Fin m → ℝ)) v) =
      (ψ t) • fderiv ℝ (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) v := by
  let fstCLM : (ComplexChartSpace m × (Fin m → ℝ)) →L[ℝ] ComplexChartSpace m :=
    ContinuousLinearMap.fst ℝ (ComplexChartSpace m) (Fin m → ℝ)
  let sndCLM : (ComplexChartSpace m × (Fin m → ℝ)) →L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearMap.snd ℝ (ComplexChartSpace m) (Fin m → ℝ)
  let L : (ComplexChartSpace m × (Fin m → ℝ)) →L[ℝ] ComplexChartSpace m :=
    fstCLM - realEmbedCLMApprox.comp sndCLM
  let A : ComplexChartSpace m × (Fin m → ℝ) → ℂ :=
    fun p => θ (p.1 - realEmbed p.2)
  let B : ComplexChartSpace m × (Fin m → ℝ) → ℂ :=
    fun p => ψ p.2
  have hL_apply :
      ∀ p : ComplexChartSpace m × (Fin m → ℝ), L p = p.1 - realEmbed p.2 := by
    intro p
    simp [L, fstCLM, sndCLM]
  have hA_eq : A = fun p => θ (L p) := by
    funext p
    simp [A, hL_apply p]
  have hA_deriv :
      HasFDerivAt A ((fderiv ℝ θ (z - realEmbed t)).comp L) (z, t) := by
    rw [hA_eq]
    have hθ :
        HasFDerivAt (θ : ComplexChartSpace m → ℂ)
          (fderiv ℝ (θ : ComplexChartSpace m → ℂ) (z - realEmbed t))
          (z - realEmbed t) :=
      θ.differentiableAt.hasFDerivAt
    simpa [hL_apply] using hθ.comp (z, t) L.hasFDerivAt
  have hB_deriv :
      HasFDerivAt B ((fderiv ℝ ψ t).comp sndCLM) (z, t) := by
    have hψ :
        HasFDerivAt (ψ : (Fin m → ℝ) → ℂ)
          (fderiv ℝ (ψ : (Fin m → ℝ) → ℂ) t) t :=
      ψ.differentiableAt.hasFDerivAt
    simpa [B, sndCLM] using hψ.comp (z, t) sndCLM.hasFDerivAt
  have hAB : HasFDerivAt (fun p => A p * B p)
      (A (z, t) • ((fderiv ℝ ψ t).comp sndCLM) +
        B (z, t) • ((fderiv ℝ θ (z - realEmbed t)).comp L)) (z, t) := by
    simpa [smul_eq_mul] using hA_deriv.mul hB_deriv
  have hfun : (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
      θ (p.1 - realEmbed p.2) * ψ p.2) = fun p => A p * B p := by
    funext p
    simp [A, B]
  rw [hfun]
  rw [hAB.fderiv]
  have hreal_zero : realEmbed (0 : Fin m → ℝ) = (0 : ComplexChartSpace m) := by
    ext i
    simp [realEmbed]
  simp [A, B, L, fstCLM, sndCLM, hreal_zero, smul_eq_mul, mul_comm]

/-- The checked fiber-integral base-derivative field for the sheared
convolution kernel is exactly the translated derivative of the complex-chart
test, multiplied by the real kernel. -/
theorem baseFDeriv_realConvolution_kernel_apply
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (z v : ComplexChartSpace m) (t : Fin m → ℝ) :
    baseFDerivSchwartz
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realConvolutionShearCLE m))
        (schwartzTensorProduct₂ θ ψ)) (z, t) v =
      (ψ t) • fderiv ℝ (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) v := by
  rw [baseFDerivSchwartz_apply]
  change fderiv ℝ (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
      θ (p.1 - realEmbed p.2) * ψ p.2) (z, t)
      ((ContinuousLinearMap.inl ℝ (ComplexChartSpace m) (Fin m → ℝ)) v) = _
  exact fderiv_shearedTensor_base_apply θ ψ z v t

/-- First derivative of `realConvolutionTest`, evaluated on a complex-chart
direction, is the real-fiber integral of the translated first derivative. -/
theorem fderiv_realConvolutionTest_apply_eq_integral
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (z v : ComplexChartSpace m) :
    fderiv ℝ (realConvolutionTest θ ψ : ComplexChartSpace m → ℂ) z v =
      ∫ t : Fin m → ℝ,
        (ψ t) • fderiv ℝ (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) v := by
  let F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ :=
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realConvolutionShearCLE m))
      (schwartzTensorProduct₂ θ ψ))
  have hraw : fderiv ℝ (complexRealFiberIntegralRaw F) z =
      complexRealFiberIntegralRaw (baseFDerivSchwartz F) z := by
    exact congrFun (fderiv_complexRealFiberIntegralRaw_eq F) z
  change fderiv ℝ (complexRealFiberIntegralRaw F) z v = _
  rw [hraw]
  change (∫ t : Fin m → ℝ, baseFDerivSchwartz F (z, t)) v = _
  rw [ContinuousLinearMap.integral_apply
    (integrable_complexRealFiber (baseFDerivSchwartz F) z) v]
  apply integral_congr_ae
  filter_upwards with t
  exact baseFDeriv_realConvolution_kernel_apply θ ψ z v t

/-- The translated first-derivative field appearing in the convolution-test
derivative formula is Bochner integrable as a continuous linear map. -/
theorem integrable_smul_fderiv_translate
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (z : ComplexChartSpace m) :
    Integrable (fun t : Fin m → ℝ =>
      (ψ t) • fderiv ℝ (θ : ComplexChartSpace m → ℂ) (z - realEmbed t)) := by
  let F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ :=
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realConvolutionShearCLE m))
      (schwartzTensorProduct₂ θ ψ))
  have hbase : Integrable (fun t : Fin m → ℝ => baseFDerivSchwartz F (z, t)) :=
    integrable_complexRealFiber (baseFDerivSchwartz F) z
  refine hbase.congr ?_
  filter_upwards with t
  ext v
  exact baseFDeriv_realConvolution_kernel_apply θ ψ z v t

/-- First derivative of `realConvolutionTest` as a continuous-linear-map
identity. -/
theorem fderiv_realConvolutionTest_eq_integral
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (z : ComplexChartSpace m) :
    fderiv ℝ (realConvolutionTest θ ψ : ComplexChartSpace m → ℂ) z =
      ∫ t : Fin m → ℝ,
        (ψ t) • fderiv ℝ (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) := by
  ext v
  rw [ContinuousLinearMap.integral_apply
    (integrable_smul_fderiv_translate θ ψ z) v]
  simpa using fderiv_realConvolutionTest_apply_eq_integral θ ψ z v

/-- Directional derivatives in the complex-chart variable commute through
`realConvolutionTest`. -/
theorem lineDerivOp_realConvolutionTest
    (v : ComplexChartSpace m)
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    ∂_{v} (realConvolutionTest θ ψ) = realConvolutionTest (∂_{v} θ) ψ := by
  ext z
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [fderiv_realConvolutionTest_apply_eq_integral]
  rw [realConvolutionTest_apply]
  apply integral_congr_ae
  filter_upwards with t
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp [mul_comm]

/-- Iterated directional derivatives commute through `realConvolutionTest`. -/
theorem iteratedLineDerivOp_realConvolutionTest
    {l : ℕ} (u : Fin l → ComplexChartSpace m)
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    ∂^{u} (realConvolutionTest θ ψ) = realConvolutionTest (∂^{u} θ) ψ := by
  induction l with
  | zero =>
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ l ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      rw [ih (Fin.tail u)]
      exact lineDerivOp_realConvolutionTest (u 0) (∂^{Fin.tail u} θ) ψ

/-- Applied all-orders derivative-through-convolution formula for
`realConvolutionTest`. -/
theorem iteratedFDeriv_realConvolutionTest_eq_integral_apply
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (l : ℕ) (z : ComplexChartSpace m) (u : Fin l → ComplexChartSpace m) :
    iteratedFDeriv ℝ l
      (realConvolutionTest θ ψ : ComplexChartSpace m → ℂ) z u =
      ∫ t : Fin m → ℝ,
        (ψ t) * iteratedFDeriv ℝ l
          (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) u := by
  calc
    iteratedFDeriv ℝ l
        (realConvolutionTest θ ψ : ComplexChartSpace m → ℂ) z u =
        (∂^{u} (realConvolutionTest θ ψ)) z := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := realConvolutionTest θ ψ) (m := u) (x := z)).symm
    _ = realConvolutionTest (∂^{u} θ) ψ z := by
      rw [iteratedLineDerivOp_realConvolutionTest]
    _ = ∫ t : Fin m → ℝ, (∂^{u} θ) (z - realEmbed t) * ψ t := by
      rw [realConvolutionTest_apply]
    _ = ∫ t : Fin m → ℝ,
          iteratedFDeriv ℝ l
            (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) u * ψ t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    _ = ∫ t : Fin m → ℝ,
          (ψ t) * iteratedFDeriv ℝ l
            (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) u := by
      apply integral_congr_ae
      filter_upwards with t
      ring

/-- All-orders derivative-through-convolution formula for
`realConvolutionTest`. -/
theorem iteratedFDeriv_realConvolutionTest_eq_integral
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (l : ℕ) (z : ComplexChartSpace m) :
    iteratedFDeriv ℝ l
      (realConvolutionTest θ ψ : ComplexChartSpace m → ℂ) z =
      ∫ t : Fin m → ℝ,
        (ψ t) • iteratedFDeriv ℝ l
          (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) := by
  ext u
  rw [ContinuousMultilinearMap.integral_apply
    (integrable_smul_iteratedFDeriv_translate θ ψ l z) u]
  simpa [smul_eq_mul] using
    iteratedFDeriv_realConvolutionTest_eq_integral_apply θ ψ l z u

/-- All-orders formula for the difference between a real convolution test and
the original complex-chart test. -/
theorem iteratedFDeriv_realConvolutionTest_sub_eq_integral
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_norm : ∫ t : Fin m → ℝ, ψ t = 1)
    (l : ℕ) (z : ComplexChartSpace m) :
    iteratedFDeriv ℝ l
      (realConvolutionTest θ ψ - θ : ComplexChartSpace m → ℂ) z =
      ∫ t : Fin m → ℝ,
        (ψ t) •
          (iteratedFDeriv ℝ l
            (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) -
           iteratedFDeriv ℝ l
             (θ : ComplexChartSpace m → ℂ) z) := by
  let D :
      ComplexChartSpace m →
        ContinuousMultilinearMap ℝ (fun _ : Fin l => ComplexChartSpace m) ℂ :=
    fun w => iteratedFDeriv ℝ l (θ : ComplexChartSpace m → ℂ) w
  have hsub_fun :
      (realConvolutionTest θ ψ : ComplexChartSpace m → ℂ) -
          (θ : ComplexChartSpace m → ℂ) =
        (realConvolutionTest θ ψ : ComplexChartSpace m → ℂ) +
          fun w => -θ w := by
    funext w
    simp [sub_eq_add_neg]
  have hleft :
      iteratedFDeriv ℝ l
        (realConvolutionTest θ ψ - θ : ComplexChartSpace m → ℂ) z =
      iteratedFDeriv ℝ l
        (realConvolutionTest θ ψ : ComplexChartSpace m → ℂ) z - D z := by
    change (iteratedFDeriv ℝ l
      ((realConvolutionTest θ ψ : ComplexChartSpace m → ℂ) -
        (θ : ComplexChartSpace m → ℂ)) z) =
      iteratedFDeriv ℝ l
        (realConvolutionTest θ ψ : ComplexChartSpace m → ℂ) z - D z
    rw [hsub_fun]
    rw [iteratedFDeriv_add_apply
      ((realConvolutionTest θ ψ).smooth l).contDiffAt ((θ.smooth l).neg).contDiffAt]
    rw [show (fun w : ComplexChartSpace m => -θ w) =
        -(θ : ComplexChartSpace m → ℂ) by rfl]
    rw [iteratedFDeriv_neg_apply]
    simp [D, sub_eq_add_neg]
  have hconv := iteratedFDeriv_realConvolutionTest_eq_integral θ ψ l z
  rw [hleft, hconv]
  have hconst :
      ∫ t : Fin m → ℝ, (ψ t) • D z = D z := by
    calc
      ∫ t : Fin m → ℝ, (ψ t) • D z =
          (∫ t : Fin m → ℝ, ψ t) • D z := by
        exact integral_smul_const (fun t : Fin m → ℝ => ψ t) (D z)
      _ = D z := by
        rw [hψ_norm]
        simp
  have h1 : Integrable (fun t : Fin m → ℝ => (ψ t) • D (z - realEmbed t)) :=
    integrable_smul_iteratedFDeriv_translate θ ψ l z
  have h2 : Integrable (fun t : Fin m → ℝ => (ψ t) • D z) := by
    simpa [D] using ψ.integrable.smul_const (D z)
  calc
    (∫ t : Fin m → ℝ, (ψ t) • D (z - realEmbed t)) - D z =
        (∫ t : Fin m → ℝ, (ψ t) • D (z - realEmbed t)) -
          ∫ t : Fin m → ℝ, (ψ t) • D z := by
      rw [hconst]
    _ = ∫ t : Fin m → ℝ, (ψ t) • D (z - realEmbed t) - (ψ t) • D z := by
      rw [← integral_sub h1 h2]
    _ = ∫ t : Fin m → ℝ, (ψ t) • (D (z - realEmbed t) - D z) := by
      apply integral_congr_ae
      filter_upwards with t
      simp [smul_sub]

/-- Applied all-orders formula for the difference between a real convolution
test and the original complex-chart test. -/
theorem iteratedFDeriv_realConvolutionTest_sub_eq_integral_apply
    (θ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_norm : ∫ t : Fin m → ℝ, ψ t = 1)
    (l : ℕ) (z : ComplexChartSpace m) (u : Fin l → ComplexChartSpace m) :
    iteratedFDeriv ℝ l
      (realConvolutionTest θ ψ - θ : ComplexChartSpace m → ℂ) z u =
      ∫ t : Fin m → ℝ,
        (ψ t) * (iteratedFDeriv ℝ l
          (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) u -
          iteratedFDeriv ℝ l
            (θ : ComplexChartSpace m → ℂ) z u) := by
  have hInt : Integrable (fun t : Fin m → ℝ =>
        (ψ t) •
          (iteratedFDeriv ℝ l
            (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) -
           iteratedFDeriv ℝ l
             (θ : ComplexChartSpace m → ℂ) z)) := by
    have h1 : Integrable (fun t : Fin m → ℝ =>
        (ψ t) • iteratedFDeriv ℝ l
          (θ : ComplexChartSpace m → ℂ) (z - realEmbed t)) :=
      integrable_smul_iteratedFDeriv_translate θ ψ l z
    have h2 : Integrable (fun t : Fin m → ℝ =>
        (ψ t) • iteratedFDeriv ℝ l
          (θ : ComplexChartSpace m → ℂ) z) := by
      simpa using ψ.integrable.smul_const
        (iteratedFDeriv ℝ l (θ : ComplexChartSpace m → ℂ) z)
    simpa [smul_sub] using h1.sub h2
  have h := congrArg (fun A =>
      A u) (iteratedFDeriv_realConvolutionTest_sub_eq_integral θ ψ hψ_norm l z)
  change (iteratedFDeriv ℝ l
      (realConvolutionTest θ ψ - θ : ComplexChartSpace m → ℂ) z) u =
    (∫ t : Fin m → ℝ,
      (ψ t) •
        (iteratedFDeriv ℝ l
          (θ : ComplexChartSpace m → ℂ) (z - realEmbed t) -
         iteratedFDeriv ℝ l
          (θ : ComplexChartSpace m → ℂ) z)) u at h
  rw [ContinuousMultilinearMap.integral_apply hInt u] at h
  simpa [smul_sub, smul_eq_mul, mul_sub] using h

end SCV
