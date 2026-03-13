import OSReconstruction.Wightman.SchwartzTensorProduct
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/

/-!
# Slice Integrals of Schwartz Functions

This file contains the compact-support slice-integral theorem used in the
multi-dimensional induction behind the zero-mean decomposition on Schwartz
space.
-/

noncomputable section

open scoped SchwartzMap
open MeasureTheory SchwartzMap

namespace OSReconstruction

/-- Insert a tail vector into `Fin (n+1) → ℝ` with zero head coordinate. This
is the linear part of the map `y ↦ Fin.cons x y`. -/
noncomputable def tailInsertCLM (n : ℕ) :
    (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    Fin.cases
      (0 : (Fin n → ℝ) →L[ℝ] ℝ)
      (fun i => ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i)
      j

@[simp] theorem tailInsertCLM_apply {n : ℕ} (y : Fin n → ℝ) :
    tailInsertCLM n y = Fin.cons 0 y := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [tailInsertCLM]
  · intro i
    simp [tailInsertCLM]

theorem tailInsertCLM_opNorm_le (n : ℕ) :
    ‖tailInsertCLM n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul, tailInsertCLM_apply]
    have htail :
        ‖(Fin.cons 0 y : Fin (n + 1) → ℝ)‖ ≤ ‖y‖ := by
      simp only [Pi.norm_def]
      exact_mod_cast Finset.sup_le fun b _ =>
        Fin.cases
          (by simp)
          (fun i => Finset.le_sup (f := fun j : Fin n => ‖y j‖₊) (Finset.mem_univ i))
          b
    exact htail

/-- Integrate out the head coordinate of a Schwartz function on `ℝ × ℝ^n`,
viewed as `Fin (n+1) → ℝ`. This is the raw pointwise slice integral needed for
the multi-dimensional Poincare induction. -/
def sliceIntegralRaw {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) : V :=
  ∫ x : ℝ, F (Fin.cons x y)

@[simp] theorem sliceIntegralRaw_prependField {n : ℕ}
    (φ : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n → ℝ) ℂ) (y : Fin n → ℝ) :
    sliceIntegralRaw (φ.prependField g) y =
      (∫ x : ℝ, φ x) * g y := by
  simp [sliceIntegralRaw, SchwartzMap.prependField_apply, MeasureTheory.integral_mul_const]

/-- Fubini for the raw slice integral. Integrating first in the head variable
and then in the tail variables recovers the full integral on `Fin (n+1) → ℝ`.
-/
theorem integral_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    ∫ y : Fin n → ℝ, sliceIntegralRaw F y =
      ∫ z : Fin (n + 1) → ℝ, F z := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp :
      MeasureTheory.MeasurePreserving e
        (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))) := by
    simpa [e] using
      (MeasureTheory.volume_preserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0)
  have hF_int :
      Integrable (fun z : Fin (n + 1) → ℝ => F z)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ)) := by
    simpa using
      (SchwartzMap.integrable
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ))) F)
  have hpair_int :
      Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))) := by
    have hiff :=
      (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding
        (g := fun z : Fin (n + 1) → ℝ => F z))
    simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using hiff.2 hF_int
  calc
    ∫ y : Fin n → ℝ, sliceIntegralRaw F y
        = ∫ y : Fin n → ℝ, ∫ x : ℝ, F (Fin.cons x y) := by
            simp [sliceIntegralRaw]
    _ = ∫ p : ℝ × (Fin n → ℝ), F (Fin.cons p.1 p.2) := by
          symm
          exact MeasureTheory.integral_prod_symm
            (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2)) hpair_int
    _ = ∫ z : Fin (n + 1) → ℝ, F z := by
          simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using
            (hmp.symm.integral_comp'
              (f := e.symm) (g := fun z : Fin (n + 1) → ℝ => F z))

/-- Zeroth-order Schwartz decay for the raw slice integral: integrating out the
head coordinate loses two powers of decay in that coordinate, but preserves
arbitrary polynomial decay in the tail variables. This is the first genuine
estimate needed for the multi-dimensional induction. -/
theorem exists_one_add_norm_pow_mul_sliceIntegralRaw_le {n k : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ),
        (1 + ‖y‖) ^ k * ‖sliceIntegralRaw F y‖ ≤
          C * ((Finset.Iic (k + 2, 0)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F := by
  let C0 : ℝ := ∫ x : ℝ, (1 + x ^ 2)⁻¹
  let C : ℝ := (2 : ℝ) ^ (k + 2) * C0
  refine ⟨C, by positivity, ?_⟩
  intro F y
  let S : ℝ := ((Finset.Iic (k + 2, 0)).sup
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F
  let zfun : ℝ → Fin (n + 1) → ℝ := fun x j => Fin.cases x y j
  have hS_nonneg : 0 ≤ S := by positivity
  have hC0_int :
      Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    simpa using integrable_inv_one_add_sq
  have hbound_point :
      ∀ x : ℝ,
        (1 + ‖y‖) ^ k * ‖F (fun j : Fin (n + 1) => Fin.cases x y j)‖ ≤
          ((2 : ℝ) ^ (k + 2) * S) * (1 + x ^ 2)⁻¹ := by
    intro x
    let z : Fin (n + 1) → ℝ := zfun x
    have hhead : ‖x‖ ≤ ‖z‖ := by
      simpa [z] using (norm_le_pi_norm z 0)
    have htail : ‖y‖ ≤ ‖z‖ := by
      calc
        ‖y‖ = ‖tailCLM n z‖ := by
          simp [tailCLM_apply, zfun, z]
        _ ≤ ‖tailCLM n (E := ℝ)‖ * ‖z‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖z‖ := by
          gcongr
          exact tailCLM_opNorm_le (E := ℝ) n
        _ = ‖z‖ := by ring
    have hprod :
        (1 + ‖y‖) ^ k * (1 + ‖x‖) ^ 2 ≤ (1 + ‖z‖) ^ (k + 2) := by
      calc
        (1 + ‖y‖) ^ k * (1 + ‖x‖) ^ 2
            ≤ (1 + ‖z‖) ^ k * (1 + ‖z‖) ^ 2 := by
              gcongr
        _ = (1 + ‖z‖) ^ (k + 2) := by
              rw [← pow_add]
    have hseminorm :
        (1 + ‖z‖) ^ (k + 2) * ‖F z‖ ≤
          (2 : ℝ) ^ (k + 2) * S := by
      simpa [S] using
        (SchwartzMap.one_add_le_sup_seminorm_apply
          (𝕜 := ℝ) (m := (k + 2, 0)) (k := k + 2) (n := 0)
          le_rfl le_rfl F z)
    have hx_pos : 0 < (1 + ‖x‖) ^ (2 : ℕ) := by positivity
    have hx_nonneg : 0 ≤ (1 + ‖x‖) ^ (2 : ℕ) := by positivity
    have hmain :
        (1 + ‖y‖) ^ k * ‖F z‖ ≤
          ((2 : ℝ) ^ (k + 2) * S) / (1 + ‖x‖) ^ (2 : ℕ) := by
      refine (le_div_iff₀ hx_pos).2 ?_
      calc
        ((1 + ‖y‖) ^ k * ‖F z‖) * (1 + ‖x‖) ^ (2 : ℕ)
            = ((1 + ‖y‖) ^ k * (1 + ‖x‖) ^ (2 : ℕ)) * ‖F z‖ := by ring
        _ ≤ (1 + ‖z‖) ^ (k + 2) * ‖F z‖ := by
              gcongr
        _ ≤ (2 : ℝ) ^ (k + 2) * S := hseminorm
    have hsq : 1 + x ^ 2 ≤ (1 + ‖x‖) ^ (2 : ℕ) := by
      calc
        1 + x ^ 2 ≤ 1 + 2 * |x| + x ^ 2 := by
          nlinarith [abs_nonneg x]
        _ = 1 + 2 * |x| + |x| ^ 2 := by rw [sq_abs]
        _ = (1 + |x|) ^ (2 : ℕ) := by ring
        _ = (1 + ‖x‖) ^ (2 : ℕ) := by rw [Real.norm_eq_abs]
    have hsq_inv : ((1 + ‖x‖) ^ (2 : ℕ))⁻¹ ≤ (1 + x ^ 2)⁻¹ := by
      have hpos1 : 0 < 1 + x ^ 2 := by positivity
      simpa [one_div] using (one_div_le_one_div_of_le hpos1 hsq)
    calc
      (1 + ‖y‖) ^ k * ‖F z‖
          ≤ ((2 : ℝ) ^ (k + 2) * S) * (((1 + ‖x‖) ^ (2 : ℕ))⁻¹) := by
            simpa [one_div, div_eq_mul_inv] using hmain
      _ ≤ ((2 : ℝ) ^ (k + 2) * S) * (1 + x ^ 2)⁻¹ := by
            gcongr
  have hnorm :
      ‖sliceIntegralRaw F y‖ ≤ ∫ x : ℝ, ‖F (zfun x)‖ := by
    simpa [sliceIntegralRaw] using
      (norm_integral_le_integral_norm (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (f := fun x : ℝ => F (zfun x)))
  have hmajor_integrable :
      Integrable
        (fun x : ℝ => ((2 : ℝ) ^ (k + 2) * S) * (1 + x ^ 2)⁻¹)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hC0_int.const_mul ((2 : ℝ) ^ (k + 2) * S)
  have hzfun_cont : Continuous zfun := by
    classical
    refine continuous_pi ?_
    intro j
    induction j using Fin.cases with
    | zero =>
        simpa [zfun] using (continuous_id : Continuous fun a : ℝ => a)
    | succ i =>
        simpa [zfun] using (continuous_const : Continuous fun _ : ℝ => y i)
  have hlower_integrable :
      Integrable (fun x : ℝ => (1 + ‖y‖) ^ k * ‖F (zfun x)‖)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    refine hmajor_integrable.mono' ?_ ?_
    · exact (continuous_const.mul ((F.continuous.comp hzfun_cont).norm)).aestronglyMeasurable
    · filter_upwards [Filter.Eventually.of_forall hbound_point] with x hx
      have hnonneg : 0 ≤ (1 + ‖y‖) ^ k * ‖F (zfun x)‖ := by positivity
      have hy1_nonneg : 0 ≤ 1 + ‖y‖ := by positivity
      simpa [zfun, Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hy1_nonneg] using hx
  calc
    (1 + ‖y‖) ^ k * ‖sliceIntegralRaw F y‖
        ≤ (1 + ‖y‖) ^ k * ∫ x : ℝ, ‖F (zfun x)‖ := by
            gcongr
    _ = ∫ x : ℝ, (1 + ‖y‖) ^ k * ‖F (zfun x)‖ := by
          rw [← integral_const_mul]
    _ ≤ ∫ x : ℝ, ((2 : ℝ) ^ (k + 2) * S) * (1 + x ^ 2)⁻¹ := by
          refine MeasureTheory.integral_mono_ae hlower_integrable hmajor_integrable ?_
          exact Filter.Eventually.of_forall hbound_point
    _ = C * S := by
          rw [MeasureTheory.integral_const_mul]
          rw [show (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ k * 4 by
            rw [pow_add]
            norm_num]
          simp [C, C0, S]
          ring

/-- Pointwise `x`-decay for a fixed tail slice. This is the basic majorant used
for integrability of the slice map. -/
theorem norm_sliceSection_le_inv_one_add_sq {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) (x : ℝ) :
    ‖F (Fin.cons x y)‖ ≤
      ((4 : ℝ) * ((Finset.Iic (2, 0)).sup
        (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹ := by
  let S : ℝ := ((Finset.Iic (2, 0)).sup
    (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F
  have hhead : ‖x‖ ≤ ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ := by
    simpa using (norm_le_pi_norm (Fin.cons x y : Fin (n + 1) → ℝ) 0)
  have hseminorm :
      (1 + ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖) ^ (2 : ℕ) * ‖F (Fin.cons x y)‖
        ≤ (2 : ℝ) ^ (2 : ℕ) * S := by
    simpa [S] using
      (SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℝ) (m := (2, 0)) (k := 2) (n := 0)
        le_rfl le_rfl F (Fin.cons x y))
  have hx_pos : 0 < (1 + ‖x‖) ^ (2 : ℕ) := by positivity
  have hmain :
      ‖F (Fin.cons x y)‖ ≤ ((2 : ℝ) ^ (2 : ℕ) * S) / (1 + ‖x‖) ^ (2 : ℕ) := by
    refine (le_div_iff₀ hx_pos).2 ?_
    calc
      ‖F (Fin.cons x y)‖ * (1 + ‖x‖) ^ (2 : ℕ)
          ≤ ‖F (Fin.cons x y)‖ * (1 + ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖) ^ (2 : ℕ) := by
            gcongr
      _ = (1 + ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖) ^ (2 : ℕ) * ‖F (Fin.cons x y)‖ := by ring
      _ ≤ (2 : ℝ) ^ (2 : ℕ) * S := hseminorm
  have hsq : 1 + x ^ 2 ≤ (1 + ‖x‖) ^ (2 : ℕ) := by
    calc
      1 + x ^ 2 ≤ 1 + 2 * |x| + x ^ 2 := by nlinarith [abs_nonneg x]
      _ = 1 + 2 * |x| + |x| ^ 2 := by rw [sq_abs]
      _ = (1 + |x|) ^ (2 : ℕ) := by ring
      _ = (1 + ‖x‖) ^ (2 : ℕ) := by rw [Real.norm_eq_abs]
  have hsq_inv : ((1 + ‖x‖) ^ (2 : ℕ))⁻¹ ≤ (1 + x ^ 2)⁻¹ := by
    have hpos1 : 0 < 1 + x ^ 2 := by positivity
    simpa [one_div] using (one_div_le_one_div_of_le hpos1 hsq)
  calc
    ‖F (Fin.cons x y)‖
        ≤ ((2 : ℝ) ^ (2 : ℕ) * S) * (((1 + ‖x‖) ^ (2 : ℕ))⁻¹) := by
          simpa [one_div, div_eq_mul_inv] using hmain
    _ ≤ ((2 : ℝ) ^ (2 : ℕ) * S) * (1 + x ^ 2)⁻¹ := by
          gcongr
    _ = ((4 : ℝ) * S) * (1 + x ^ 2)⁻¹ := by norm_num
    _ = ((4 : ℝ) * ((Finset.Iic (2, 0)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹ := by
          simp [S]

/-- The slice map `y ↦ F (x,y)` is differentiable in the tail variable, with
derivative obtained by composing the ambient Fréchet derivative with the tail
inclusion. -/
theorem hasFDerivAt_sliceSection {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (x : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt
      (fun y' : Fin n → ℝ => F (Fin.cons x y'))
      (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
        (tailInsertCLM n))
      y := by
  let c : Fin (n + 1) → ℝ := Fin.cons x 0
  have hinner :
      HasFDerivAt
        (fun y' : Fin n → ℝ => tailInsertCLM n y' + c)
        (tailInsertCLM n) y := by
    simpa [c, tailInsertCLM_apply, add_comm, add_left_comm, add_assoc]
      using (tailInsertCLM n).hasFDerivAt.add_const c
  have hfun :
      (fun y' : Fin n → ℝ => tailInsertCLM n y' + c) =
        (fun y' : Fin n → ℝ => (Fin.cons x y' : Fin (n + 1) → ℝ)) := by
    funext y'
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [c, tailInsertCLM_apply]
    · intro i
      simp [c, tailInsertCLM_apply]
  have hpt : (Fin.cons 0 y : Fin (n + 1) → ℝ) + c = Fin.cons x y := by
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [c]
    · intro i
      simp [c]
  have hcons : ∀ y' : Fin n → ℝ, (Fin.cons 0 y' : Fin (n + 1) → ℝ) + c = Fin.cons x y' := by
    intro y'
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [c]
    · intro i
      simp [c]
  simpa [Function.comp, tailInsertCLM_apply, c, hcons, hpt] using
    (F.differentiableAt.hasFDerivAt.comp y hinner)

/-- Pointwise `x`-decay for the first tail derivative of a slice. This is the
majorant needed for the first differentiation-under-integral step. -/
theorem norm_fderiv_fullSlice_le_inv_one_add_sq {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) (x : ℝ) :
    ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ ≤
      ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
        (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹ := by
  let S : ℝ := ((Finset.Iic (2, 1)).sup
    (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F
  have hhead : ‖x‖ ≤ ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ := by
    simpa using (norm_le_pi_norm (Fin.cons x y : Fin (n + 1) → ℝ) 0)
  have hseminorm :
      (1 + ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖) ^ (2 : ℕ) *
        ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖
          ≤ (2 : ℝ) ^ (2 : ℕ) * S := by
    simpa [S] using
      (SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℝ) (m := (2, 1)) (k := 2) (n := 1)
        le_rfl le_rfl F (Fin.cons x y))
  have hx_pos : 0 < (1 + ‖x‖) ^ (2 : ℕ) := by positivity
  have hmain :
      ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖
        ≤ ((2 : ℝ) ^ (2 : ℕ) * S) / (1 + ‖x‖) ^ (2 : ℕ) := by
    refine (le_div_iff₀ hx_pos).2 ?_
    calc
      ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ * (1 + ‖x‖) ^ (2 : ℕ)
          ≤ ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ *
            (1 + ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖) ^ (2 : ℕ) := by
              gcongr
      _ = (1 + ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖) ^ (2 : ℕ) *
            ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ := by ring
      _ ≤ (2 : ℝ) ^ (2 : ℕ) * S := hseminorm
  have hsq : 1 + x ^ 2 ≤ (1 + ‖x‖) ^ (2 : ℕ) := by
    calc
      1 + x ^ 2 ≤ 1 + 2 * |x| + x ^ 2 := by nlinarith [abs_nonneg x]
      _ = 1 + 2 * |x| + |x| ^ 2 := by rw [sq_abs]
      _ = (1 + |x|) ^ (2 : ℕ) := by ring
      _ = (1 + ‖x‖) ^ (2 : ℕ) := by rw [Real.norm_eq_abs]
  have hsq_inv : ((1 + ‖x‖) ^ (2 : ℕ))⁻¹ ≤ (1 + x ^ 2)⁻¹ := by
    have hpos1 : 0 < 1 + x ^ 2 := by positivity
    simpa [one_div] using (one_div_le_one_div_of_le hpos1 hsq)
  calc
    ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖
        ≤ ((2 : ℝ) ^ (2 : ℕ) * S) * (((1 + ‖x‖) ^ (2 : ℕ))⁻¹) := by
          simpa [one_div, div_eq_mul_inv] using hmain
    _ ≤ ((2 : ℝ) ^ (2 : ℕ) * S) * (1 + x ^ 2)⁻¹ := by
          gcongr
    _ = ((4 : ℝ) * S) * (1 + x ^ 2)⁻¹ := by norm_num
    _ = ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹ := by
          simp [S]

/-- Pointwise `x`-decay for the first tail derivative of a slice. This is the
majorant needed for the first differentiation-under-integral step. -/
theorem norm_fderiv_sliceSection_le_inv_one_add_sq {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) (x : ℝ) :
    ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
        (tailInsertCLM n))‖ ≤
      ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹ := by
  have hcomp :
      ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
          (tailInsertCLM n))‖
        ≤ ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ *
          ‖tailInsertCLM n‖ := by
    exact ContinuousLinearMap.opNorm_comp_le _ _
  calc
    ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
        (tailInsertCLM n))‖
        ≤ ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ * ‖tailInsertCLM n‖ := hcomp
    _ ≤ ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ * 1 := by
          gcongr
          exact tailInsertCLM_opNorm_le n
    _ = ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ := by ring
    _ ≤ ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹ := by
          exact norm_fderiv_fullSlice_le_inv_one_add_sq F y x

/-- First differentiation-under-integral step for the raw slice map. -/
theorem hasFDerivAt_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) :
    HasFDerivAt
      (sliceIntegralRaw F)
      (∫ x : ℝ,
        (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
          (tailInsertCLM n)))
      y := by
  let bound0 : ℝ → ℝ := fun x =>
    ((4 : ℝ) * ((Finset.Iic (2, 0)).sup
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹
  let bound1 : ℝ → ℝ := fun x =>
    ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹
  have hs : (Set.univ : Set (Fin n → ℝ)) ∈ nhds y := Filter.univ_mem
  have hF_meas :
      ∀ᶠ y' in nhds y,
        AEStronglyMeasurable
          (fun x : ℝ => F (Fin.cons x y'))
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro y'
    have hcont : Continuous fun x : ℝ => F (Fin.cons x y') := by
      have hpath : Continuous fun x : ℝ => (Fin.cons x y' : Fin (n + 1) → ℝ) := by
        classical
        refine continuous_pi ?_
        intro j
        refine Fin.cases ?_ ?_ j
        · simpa using (continuous_id : Continuous fun x : ℝ => x)
        · intro i
          simpa using (continuous_const : Continuous fun _ : ℝ => y' i)
      exact F.continuous.comp hpath
    exact hcont.aestronglyMeasurable
  have hF_int :
      Integrable (fun x : ℝ => F (Fin.cons x y))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    have hbound_int :
        Integrable (fun x : ℝ => bound0 x)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      simpa [bound0, mul_comm, mul_left_comm, mul_assoc] using
        integrable_inv_one_add_sq.const_mul
          ((4 : ℝ) * ((Finset.Iic (2, 0)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F)
    refine hbound_int.mono' ?_ ?_
    · exact (F.continuous.comp <| by
          classical
          refine continuous_pi ?_
          intro j
          refine Fin.cases ?_ ?_ j
          · simpa using (continuous_id : Continuous fun x : ℝ => x)
          · intro i
            simpa using (continuous_const : Continuous fun _ : ℝ => y i)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (norm_sliceSection_le_inv_one_add_sq F y)
  have hF'_meas :
      AEStronglyMeasurable
        (fun x : ℝ =>
          (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
            (tailInsertCLM n)))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    have hpath : Continuous fun x : ℝ => (Fin.cons x y : Fin (n + 1) → ℝ) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun x : ℝ => x)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => y i)
    have hcont :
        Continuous
          (fun x : ℝ =>
            (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
              (tailInsertCLM n))) := by
      exact (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath).clm_comp continuous_const
    exact hcont.aestronglyMeasurable
  have h_bound :
      ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ y' ∈ (Set.univ : Set (Fin n → ℝ)),
          ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y'))).comp
              (tailInsertCLM n))‖ ≤ bound1 x := by
    exact Filter.Eventually.of_forall (fun x y' _ => by
      simpa [bound1] using norm_fderiv_sliceSection_le_inv_one_add_sq F y' x)
  have h_bound_all :
      ∀ x : ℝ, ∀ y' : Fin n → ℝ,
        ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y'))).comp
            (tailInsertCLM n))‖ ≤ bound1 x := by
    intro x y'
    simpa [bound1] using norm_fderiv_sliceSection_le_inv_one_add_sq F y' x
  have h_bound' :
      ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ y' ∈ (Set.univ : Set (Fin n → ℝ)),
          ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y'))).comp
              (tailInsertCLM n))‖ ≤ bound1 x := by
    exact Filter.Eventually.of_forall (fun x y' _ => h_bound_all x y')
  have h_bound_int :
      Integrable bound1 (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    simpa [bound1, mul_comm, mul_left_comm, mul_assoc] using
      integrable_inv_one_add_sq.const_mul
        ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F)
  have h_diff :
      ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ y' ∈ (Set.univ : Set (Fin n → ℝ)),
          HasFDerivAt
            (fun y'' : Fin n → ℝ => F (Fin.cons x y''))
            ((((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y'))).comp
              (tailInsertCLM n)))
            y' := by
    exact Filter.Eventually.of_forall
      (fun x y' _ => hasFDerivAt_sliceSection F x y')
  simpa [sliceIntegralRaw] using
    (hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (s := (Set.univ : Set (Fin n → ℝ)))
      (x₀ := y)
      (F := fun y' x => F (Fin.cons x y'))
      (F' := fun y' x =>
        (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y'))).comp
          (tailInsertCLM n)))
      hs hF_meas hF_int hF'_meas h_bound' h_bound_int h_diff)

theorem fderiv_sliceIntegralRaw_eq {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) :
    fderiv ℝ (sliceIntegralRaw F) y =
      (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y).comp
        (tailInsertCLM n) := by
  let φ : ℝ → (Fin (n + 1) → ℝ) →L[ℝ] V := fun x =>
    fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)
  have hφ_cont : Continuous φ := by
    have hpath : Continuous fun x : ℝ => (Fin.cons x y : Fin (n + 1) → ℝ) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun x : ℝ => x)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => y i)
    simpa [φ] using (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath)
  have hφ_int : Integrable φ (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    have hbound_int :
        Integrable
          (fun x : ℝ =>
            ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        integrable_inv_one_add_sq.const_mul
          ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F)
    refine hbound_int.mono' hφ_cont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (norm_fderiv_fullSlice_le_inv_one_add_sq F y)
  calc
    fderiv ℝ (sliceIntegralRaw F) y
        = ∫ x : ℝ,
            (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
              (tailInsertCLM n)) := by
              exact (hasFDerivAt_sliceIntegralRaw F y).fderiv
    _ = (∫ x : ℝ, φ x).comp (tailInsertCLM n) := by
          let L :
              ((Fin (n + 1) → ℝ) →L[ℝ] V) →L[ℝ] ((Fin n → ℝ) →L[ℝ] V) :=
            (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin (n + 1) → ℝ) V).flip
              (tailInsertCLM n)
          have hL : ∀ A : ((Fin (n + 1) → ℝ) →L[ℝ] V), L A = A.comp (tailInsertCLM n) := by
            intro A
            simp [L, ContinuousLinearMap.compL_apply]
          have hcomp :
              (fun x : ℝ =>
                (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
                  (tailInsertCLM n))) =
              fun x : ℝ => L (φ x) := by
            funext x
            simp [φ, hL]
          rw [hcomp, ContinuousLinearMap.integral_comp_comm L hφ_int]
          simp [hL]
    _ = (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y).comp
          (tailInsertCLM n) := by
          simp [sliceIntegralRaw, φ, SchwartzMap.fderivCLM_apply]

theorem continuous_fderiv_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    Continuous (fderiv ℝ (sliceIntegralRaw F)) := by
  let L :
      ((Fin (n + 1) → ℝ) →L[ℝ] V) →L[ℝ] ((Fin n → ℝ) →L[ℝ] V) :=
    (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin (n + 1) → ℝ) V).flip (tailInsertCLM n)
  have hslice :
      Continuous (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F)) := by
    refine continuous_iff_continuousAt.2 ?_
    intro y
    exact (hasFDerivAt_sliceIntegralRaw
      (V := (Fin (n + 1) → ℝ) →L[ℝ] V)
      (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y).continuousAt
  have hEq :
      fderiv ℝ (sliceIntegralRaw F) =
        fun y =>
          L (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y) := by
    funext y
    simp [L, fderiv_sliceIntegralRaw_eq, ContinuousLinearMap.compL_apply]
  rw [hEq]
  exact L.continuous.comp hslice

theorem contDiff_one_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    ContDiff ℝ 1 (sliceIntegralRaw F) := by
  rw [contDiff_one_iff_fderiv]
  constructor
  · intro y
    exact (hasFDerivAt_sliceIntegralRaw F y).differentiableAt
  · exact continuous_fderiv_sliceIntegralRaw F

theorem hasCompactSupport_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (hF : HasCompactSupport F) :
    HasCompactSupport (sliceIntegralRaw F) := by
  rcases hF.isCompact.isBounded.subset_closedBall (0 : Fin (n + 1) → ℝ) with ⟨R, hR⟩
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin n → ℝ) R) ?_
  intro y hy
  by_contra hyR
  have hy_gt : R < ‖y‖ := by
    simpa [Metric.mem_closedBall, dist_eq_norm, not_le] using hyR
  have hzero : sliceIntegralRaw F y = 0 := by
    rw [sliceIntegralRaw]
    refine integral_eq_zero_of_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    have hnorm_le : ‖y‖ ≤ ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ := by
      calc
        ‖y‖ = ‖tailCLM n (E := ℝ) (Fin.cons x y)‖ := by
          simp [tailCLM_apply]
        _ ≤ ‖tailCLM n (E := ℝ)‖ * ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ := by
          gcongr
          exact tailCLM_opNorm_le (E := ℝ) n
        _ = ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ := by ring
    have hz_not_mem : (Fin.cons x y : Fin (n + 1) → ℝ) ∉ tsupport F := by
      intro hz
      have hball := hR hz
      have hnorm_ball : ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hball
      exact not_lt_of_ge (le_trans hnorm_le hnorm_ball) hy_gt
    simpa using image_eq_zero_of_notMem_tsupport hz_not_mem
  exact hy hzero

theorem contDiff_nat_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (m : ℕ) (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    ContDiff ℝ m (sliceIntegralRaw F) := by
  induction m generalizing n V F with
  | zero =>
      exact contDiff_zero.2 <|
        continuous_iff_continuousAt.2 fun y => (hasFDerivAt_sliceIntegralRaw F y).continuousAt
  | succ m ihm =>
      exact (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := m) (f := sliceIntegralRaw F)).2 <|
      let L :
          ((Fin (n + 1) → ℝ) →L[ℝ] V) →L[ℝ] ((Fin n → ℝ) →L[ℝ] V) :=
        (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin (n + 1) → ℝ) V).flip
          (tailInsertCLM n)
      by
        refine ⟨fun y => ∫ x : ℝ, (fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)).comp
            (tailInsertCLM n), ?_, ?_⟩
        · have hslice :
              ContDiff ℝ m
                (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F)) :=
            ihm (F := SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F)
          have hEq :
              (fun y => ∫ x : ℝ, (fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)).comp
                  (tailInsertCLM n)) =
                fun y => L (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y) := by
            funext y
            calc
              (∫ x : ℝ, (fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)).comp
                  (tailInsertCLM n))
                  = fderiv ℝ (sliceIntegralRaw F) y := by
                      symm
                      exact (hasFDerivAt_sliceIntegralRaw F y).fderiv
              _ = L (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y) := by
                    simpa [L] using fderiv_sliceIntegralRaw_eq (F := F) y
          rw [hEq]
          exact L.contDiff.comp hslice
        · intro y
          exact hasFDerivAt_sliceIntegralRaw F y

theorem contDiff_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    ContDiff ℝ (⊤ : ℕ∞) (sliceIntegralRaw F) := by
  rw [contDiff_infty]
  intro m
  exact contDiff_nat_sliceIntegralRaw m F

/-- The raw slice map is itself Schwartz. This is the genuine induction
ingredient used in the multi-dimensional zero-mean decomposition. -/
theorem decay_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (k m : ℕ) :
    ∃ C : ℝ, ∀ y : Fin n → ℝ,
      ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (sliceIntegralRaw F) y‖ ≤ C := by
  induction m generalizing V n F with
  | zero =>
      obtain ⟨C0, hC0_nonneg, hC0⟩ :=
        exists_one_add_norm_pow_mul_sliceIntegralRaw_le (n := n) (k := k) (V := V)
      let C : ℝ :=
        C0 * ((Finset.Iic (k + 2, 0)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F
      refine ⟨C, ?_⟩
      intro y
      calc
        ‖y‖ ^ k * ‖iteratedFDeriv ℝ 0 (sliceIntegralRaw F) y‖
            = ‖y‖ ^ k * ‖sliceIntegralRaw F y‖ := by
                rw [norm_iteratedFDeriv_zero]
        _ ≤ (1 + ‖y‖) ^ k * ‖sliceIntegralRaw F y‖ := by
              have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg _
              have hy_le : ‖y‖ ≤ 1 + ‖y‖ := by linarith
              exact mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ hy_nonneg hy_le k) (norm_nonneg _)
        _ ≤ C0 * ((Finset.Iic (k + 2, 0)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F := hC0 F y
        _ = C := by rfl
  | succ m ihm =>
      let F' : SchwartzMap (Fin (n + 1) → ℝ) ((Fin (n + 1) → ℝ) →L[ℝ] V) :=
        SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F
      have hIH := ihm (V := (Fin (n + 1) → ℝ) →L[ℝ] V) (n := n) (F := F')
      obtain ⟨C, hC⟩ := hIH
      let L :
          ((Fin (n + 1) → ℝ) →L[ℝ] V) →L[ℝ] ((Fin n → ℝ) →L[ℝ] V) :=
        (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin (n + 1) → ℝ) V).flip
          (tailInsertCLM n)
      let C' : ℝ := ‖L‖ * C
      refine ⟨C', ?_⟩
      intro y
      have hEq :
          fderiv ℝ (sliceIntegralRaw F) =
            fun y =>
              L (sliceIntegralRaw
                (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y) := by
        funext y'
        simp [L, fderiv_sliceIntegralRaw_eq, ContinuousLinearMap.compL_apply]
      calc
        ‖y‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) (sliceIntegralRaw F) y‖
            = ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fderiv ℝ (sliceIntegralRaw F)) y‖ := by
                rw [norm_iteratedFDeriv_fderiv]
        _ = ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (L ∘ sliceIntegralRaw F') y‖ := by
              have hcompEq : (fun y => L (sliceIntegralRaw F' y)) = L ∘ sliceIntegralRaw F' := rfl
              rw [hEq, hcompEq]
        _ ≤ ‖y‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ m (sliceIntegralRaw F') y‖) := by
              gcongr
              exact L.norm_iteratedFDeriv_comp_left
                ((contDiff_sliceIntegralRaw F').contDiffAt) (by exact_mod_cast le_top)
        _ = ‖L‖ * (‖y‖ ^ k * ‖iteratedFDeriv ℝ m (sliceIntegralRaw F') y‖) := by
              ring
        _ ≤ ‖L‖ * C := by
              gcongr
              exact hC y
        _ = C' := by rfl

/-- Integrating out the head coordinate preserves the Schwartz class. -/
noncomputable def sliceIntegral {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    SchwartzMap (Fin n → ℝ) V where
  toFun := sliceIntegralRaw F
  smooth' := contDiff_sliceIntegralRaw F
  decay' := decay_sliceIntegralRaw F

@[simp] theorem sliceIntegral_apply {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) :
    sliceIntegral F y = sliceIntegralRaw F y := rfl

theorem integral_sliceIntegral {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))
        (sliceIntegral F)
      =
    (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ))) F := by
  simp [SchwartzMap.integralCLM_apply, integral_sliceIntegralRaw]

end OSReconstruction
