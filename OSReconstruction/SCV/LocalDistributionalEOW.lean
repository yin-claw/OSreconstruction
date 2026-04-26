/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernelRecovery

/-!
# Local Distributional Edge-of-the-Wedge Support Lemmas

This file starts the upstream Streater-Wightman local EOW package: regularized
local wedge-side functions, common continuous boundary values, and the
product-kernel family that feeds the checked chart-envelope recovery theorem.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter

namespace SCV

variable {m : ℕ}

/-- Local real-direction mollification of a holomorphic function is
holomorphic on the shrunken local domain when all real translates used by the
kernel support stay inside the original holomorphy domain. -/
theorem localRealMollifySide_holomorphicOn_of_translate_margin
    (F : ComplexChartSpace m → ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (Ω D : Set (ComplexChartSpace m))
    (hΩ_open : IsOpen Ω)
    (hD_open : IsOpen D)
    (hF_holo : DifferentiableOn ℂ F Ω)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (hmargin :
      ∀ z ∈ D, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ Ω) :
    DifferentiableOn ℂ (realMollifyLocal F ψ) D := by
  intro z hz
  obtain ⟨R, hRpos, hRsub⟩ := Metric.isOpen_iff.mp hD_open z hz
  let r : ℝ := R / 2
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  let s : Set (ComplexChartSpace m) := Metric.ball z r
  have hs : s ∈ 𝓝 z := Metric.ball_mem_nhds z hrpos
  have hs_sub : s ⊆ D := by
    intro w hw
    exact hRsub <| by
      have hwR : dist w z < R := by
        calc
          dist w z < r := hw
          _ < R := by
            dsimp [r]
            linarith
      simpa [Metric.mem_ball] using hwR
  have hclosed_sub : Metric.closedBall z r ⊆ D := by
    intro w hw
    exact hRsub <| by
      have hwR : dist w z < R := by
        calc
          dist w z ≤ r := by simpa [Metric.mem_closedBall] using hw
          _ < R := by
            dsimp [r]
            linarith
      simpa [Metric.mem_ball] using hwR
  let I : ComplexChartSpace m → (Fin m → ℝ) → ℂ :=
    fun w t => F (w + realEmbed t) * ψ t
  let I' : ComplexChartSpace m → (Fin m → ℝ) → (ComplexChartSpace m →L[ℂ] ℂ) :=
    fun w t => (ψ t) • fderiv ℂ F (w + realEmbed t)
  have hψ_tsupport_compact :
      IsCompact (tsupport (ψ : (Fin m → ℝ) → ℂ)) := by
    simpa [HasCompactSupport] using hψ_compact
  have hrealEmbed_cont : Continuous (fun t : Fin m → ℝ => realEmbed t) :=
    continuous_realEmbed (m := m)
  have hI_cont_at :
      ∀ w ∈ D, Continuous fun t : Fin m → ℝ => I w t := by
    intro w hw
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ)
    · have hshift : w + realEmbed t ∈ Ω := hmargin w hw t ht
      have hF_at : ContinuousAt F (w + realEmbed t) :=
        ((hF_holo (w + realEmbed t) hshift).differentiableAt
          (hΩ_open.mem_nhds hshift)).continuousAt
      have hshift_at :
          ContinuousAt (fun u : Fin m → ℝ => w + realEmbed u) t :=
        (continuous_const.add hrealEmbed_cont).continuousAt
      have hleft : ContinuousAt (fun u : Fin m → ℝ => F (w + realEmbed u)) t :=
        ContinuousAt.comp_of_eq hF_at hshift_at rfl
      simpa [I] using hleft.mul ψ.continuous.continuousAt
    · have hψ_zero :
        (ψ : (Fin m → ℝ) → ℂ) =ᶠ[nhds t] fun _ => 0 := by
          rwa [notMem_tsupport_iff_eventuallyEq] at ht
      have hI_zero : (fun u : Fin m → ℝ => I w u) =ᶠ[nhds t] fun _ => 0 := by
        filter_upwards [hψ_zero] with u hu
        simp [I, hu]
      exact hI_zero.continuousAt
  have hF_meas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (I w) volume := by
    filter_upwards [hs] with w hw
    exact (hI_cont_at w (hs_sub hw)).aestronglyMeasurable
  have hI_support_subset :
      ∀ w, Function.support (I w) ⊆
        Function.support (ψ : (Fin m → ℝ) → ℂ) := by
    intro w t ht
    by_contra hnot
    have hψt : ψ t = 0 := by
      simpa [Function.mem_support] using hnot
    have hIt : I w t = 0 := by
      simp [I, hψt]
    exact ht (by simp [hIt])
  have hI_compact : ∀ w, HasCompactSupport (I w) := by
    intro w
    rw [HasCompactSupport]
    refine hψ_compact.of_isClosed_subset isClosed_closure ?_
    exact
      closure_minimal
        (fun t ht => subset_tsupport _ (hI_support_subset w ht))
        (isClosed_tsupport _)
  have hF_int : Integrable (I z) volume :=
    (hI_cont_at z hz).integrable_of_hasCompactSupport (hI_compact z)
  have hF_contDiff : ContDiffOn ℂ 1 F Ω := by
    exact
      (hF_holo.analyticOnNhd_of_finiteDimensional hΩ_open).contDiffOn_of_completeSpace
  have hF_fderiv_cont : ContinuousOn (fderiv ℂ F) Ω :=
    hF_contDiff.continuousOn_fderiv_of_isOpen hΩ_open le_rfl
  let K : Set (ComplexChartSpace m) :=
    (Metric.closedBall z r ×ˢ tsupport (ψ : (Fin m → ℝ) → ℂ)).image
      (fun p : ComplexChartSpace m × (Fin m → ℝ) => p.1 + realEmbed p.2)
  have hK_compact : IsCompact K := by
    exact
      ((isCompact_closedBall z r).prod hψ_tsupport_compact).image <|
        (continuous_fst.add (hrealEmbed_cont.comp continuous_snd))
  have hK_sub : K ⊆ Ω := by
    intro w hw
    rcases hw with ⟨⟨x, t⟩, hx, rfl⟩
    exact hmargin x (hclosed_sub hx.1) t hx.2
  obtain ⟨Cbound, hCbound⟩ :=
    hK_compact.exists_bound_of_continuousOn (hF_fderiv_cont.mono hK_sub)
  let bound : (Fin m → ℝ) → ℝ := fun t => Cbound * ‖ψ t‖
  have hF'_meas : AEStronglyMeasurable (I' z) volume := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine Continuous.aemeasurable ?_
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ)
    · have hz_shift : z + realEmbed t ∈ Ω := hmargin z hz t ht
      have hderiv_at : ContinuousAt (fderiv ℂ F) (z + realEmbed t) :=
        (hF_fderiv_cont (z + realEmbed t) hz_shift).continuousAt
          (hΩ_open.mem_nhds hz_shift)
      have hshift_at :
          ContinuousAt (fun u : Fin m → ℝ => z + realEmbed u) t :=
        (continuous_const.add hrealEmbed_cont).continuousAt
      have hfderiv_shift :
          ContinuousAt (fun u : Fin m → ℝ => fderiv ℂ F (z + realEmbed u)) t :=
        ContinuousAt.comp_of_eq hderiv_at hshift_at rfl
      simpa [I'] using ψ.continuous.continuousAt.smul hfderiv_shift
    · have hψ_zero :
        (ψ : (Fin m → ℝ) → ℂ) =ᶠ[nhds t] fun _ => 0 := by
          rwa [notMem_tsupport_iff_eventuallyEq] at ht
      have hI'_zero : (fun u : Fin m → ℝ => I' z u) =ᶠ[nhds t] fun _ => 0 := by
        filter_upwards [hψ_zero] with u hu
        ext v
        simp [I', hu]
      exact hI'_zero.continuousAt
  have h_bound : ∀ᵐ t ∂volume, ∀ w ∈ s, ‖I' w t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall ?_
    intro t w hw
    by_cases hψt : ψ t = 0
    · have hzeroI' : I' w t = 0 := by
        ext v
        simp [I', hψt]
      have hzeroBound : bound t = 0 := by simp [bound, hψt]
      rw [hzeroI', norm_zero, hzeroBound]
    · have ht_support :
          t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ) :=
        subset_tsupport _ (by simpa [Function.mem_support] using hψt)
      have hwK : w + realEmbed t ∈ K := by
        refine ⟨⟨w, t⟩, ?_, rfl⟩
        refine ⟨?_, ht_support⟩
        simpa [s, Metric.mem_ball, Metric.mem_closedBall] using le_of_lt hw
      have hfderiv_bound : ‖fderiv ℂ F (w + realEmbed t)‖ ≤ Cbound :=
        hCbound _ hwK
      calc
        ‖I' w t‖ = ‖ψ t‖ * ‖fderiv ℂ F (w + realEmbed t)‖ := by
          simpa [I'] using norm_smul (ψ t) (fderiv ℂ F (w + realEmbed t))
        _ ≤ ‖ψ t‖ * Cbound := by
          exact mul_le_mul_of_nonneg_left hfderiv_bound (norm_nonneg _)
        _ = bound t := by ring
  have hbound_cont : Continuous bound := continuous_const.mul ψ.continuous.norm
  have hbound_support_subset :
      Function.support bound ⊆ Function.support (ψ : (Fin m → ℝ) → ℂ) := by
    intro t ht
    by_contra hnot
    have hψt : ψ t = 0 := by
      simpa [Function.mem_support] using hnot
    have hbt : bound t = 0 := by simp [bound, hψt]
    exact ht (by simp [hbt])
  have hbound_compact : HasCompactSupport bound := by
    rw [HasCompactSupport]
    refine hψ_compact.of_isClosed_subset isClosed_closure ?_
    exact
      closure_minimal
        (fun t ht => subset_tsupport _ (hbound_support_subset ht))
        (isClosed_tsupport _)
  have hbound_int : Integrable bound volume :=
    hbound_cont.integrable_of_hasCompactSupport hbound_compact
  have h_diff : ∀ᵐ t ∂volume, ∀ w ∈ s, HasFDerivAt (I · t) (I' w t) w := by
    refine Filter.Eventually.of_forall ?_
    intro t w hw
    by_cases hψt : ψ t = 0
    · have hI_zero : (fun u : ComplexChartSpace m => I u t) = fun _ => 0 := by
        funext u
        simp [I, hψt]
      have hI'_zero : I' w t = 0 := by
        ext v
        simp [I', hψt]
      rw [hI_zero, hI'_zero]
      exact hasFDerivAt_const (0 : ℂ) w
    · have ht_support :
          t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ) :=
        subset_tsupport _ (by simpa [Function.mem_support] using hψt)
      have hwD : w ∈ D := hs_sub hw
      have hshift : w + realEmbed t ∈ Ω := hmargin w hwD t ht_support
      have hderiv_F :
          HasFDerivAt F (fderiv ℂ F (w + realEmbed t)) (w + realEmbed t) :=
        ((hF_holo (w + realEmbed t) hshift).differentiableAt
          (hΩ_open.mem_nhds hshift)).hasFDerivAt
      have htrans :
          HasFDerivAt (fun u : ComplexChartSpace m => u + realEmbed t)
            (ContinuousLinearMap.id ℂ (ComplexChartSpace m)) w := by
        simpa using
          ((ContinuousLinearMap.id ℂ (ComplexChartSpace m)).hasFDerivAt).add_const
            (realEmbed t)
      have hcomp :
          HasFDerivAt (fun u : ComplexChartSpace m => F (u + realEmbed t))
            (fderiv ℂ F (w + realEmbed t)) w := by
        simpa using hderiv_F.comp w htrans
      simpa [I, I'] using hcomp.mul_const (ψ t)
  have hderiv :
      HasFDerivAt
        (fun w : ComplexChartSpace m => ∫ t : Fin m → ℝ, I w t)
        (∫ t : Fin m → ℝ, I' z t)
        z := by
    exact
      hasFDerivAt_integral_of_dominated_of_fderiv_le
        hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa [realMollifyLocal, I] using hderiv.differentiableAt.differentiableWithinAt

end SCV
