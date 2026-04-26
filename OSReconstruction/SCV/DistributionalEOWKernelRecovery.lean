/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWHolomorphic
import OSReconstruction.SCV.DistributionalEOWApproxIdentity
import OSReconstruction.SCV.ProductDensity

/-!
# Kernel Recovery Midpoint for Distributional EOW

This downstream file assembles the checked product-kernel descent,
approximate-identity, product-kernel `∂bar`, and distributional-holomorphic
regularity layers.  It does not yet prove agreement with the plus/minus wedge
functions; that is the subsequent delta-limit step.
-/

noncomputable section

open Complex MeasureTheory Metric Set Filter
open scoped BigOperators LineDeriv

namespace SCV

variable {m : ℕ}

/-- If compact real kernels shrink like `1/(n+1)`, then for each fixed chart
point in an open domain, all real translates in the kernel support eventually
stay inside the domain and have arbitrarily small embedded real displacement. -/
theorem eventually_translate_mem_open_of_shrinking_support
    (Ucore U0 : Set (ComplexChartSpace m))
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ Ucore, ∀ ρ > 0,
      ∀ᶠ n in atTop,
        ∀ t ∈ tsupport (ψn n : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ U0 ∧ ‖realEmbed t‖ < ρ := by
  intro z hz ρ hρ
  have hzU : z ∈ U0 := hcore_U0 hz
  obtain ⟨η, hη_pos, hη_sub⟩ := Metric.isOpen_iff.mp hU0_open z hzU
  have hmin_pos : 0 < min η ρ := lt_min hη_pos hρ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hmin_pos
  refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn t ht
  have hmono : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
    have hNle : (N + 1 : ℝ) ≤ n + 1 := by
      exact_mod_cast Nat.succ_le_succ hn
    exact one_div_le_one_div_of_le (by positivity) hNle
  have hsmall : 1 / (n + 1 : ℝ) < min η ρ :=
    lt_of_le_of_lt hmono hN
  have ht_closed := hψ_support n ht
  have ht_norm : ‖t‖ ≤ 1 / (n + 1 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using ht_closed
  have hreal_small_min : ‖realEmbed t‖ < min η ρ :=
    lt_of_le_of_lt (norm_realEmbed_le t) (lt_of_le_of_lt ht_norm hsmall)
  have hreal_eta : ‖realEmbed t‖ < η :=
    lt_of_lt_of_le hreal_small_min (min_le_left η ρ)
  have hreal_rho : ‖realEmbed t‖ < ρ :=
    lt_of_lt_of_le hreal_small_min (min_le_right η ρ)
  have hdist : dist (z + realEmbed t) z = ‖realEmbed t‖ := by
    rw [dist_eq_norm]
    congr 1
    ext i
    simp
  refine ⟨?_, hreal_rho⟩
  exact hη_sub (by simpa [Metric.mem_ball, hdist] using hreal_eta)

/-- A local continuous chart representative is integrable against a compactly
supported real kernel, provided the real-translated topological support stays
inside the chart domain. -/
theorem integrable_continuousOn_realTranslate_mul_kernel
    (H : ComplexChartSpace m → ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (U0 : Set (ComplexChartSpace m))
    (z : ComplexChartSpace m)
    (hU0_open : IsOpen U0)
    (hH_cont : ContinuousOn H U0)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (htranslate :
      ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ), z + realEmbed t ∈ U0) :
    Integrable fun t : Fin m → ℝ => H (z + realEmbed t) * ψ t := by
  have hcont :
      Continuous fun t : Fin m → ℝ => H (z + realEmbed t) * ψ t := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ)
    · have hzU : z + realEmbed t ∈ U0 := htranslate t ht
      have hH_at : ContinuousAt H (z + realEmbed t) :=
        (hH_cont (z + realEmbed t) hzU).continuousAt
          (hU0_open.mem_nhds hzU)
      have hshift_at :
          ContinuousAt (fun s : Fin m → ℝ => z + realEmbed s) t :=
        (continuous_const.add (continuous_realEmbed (m := m))).continuousAt
      have hH_shift : ContinuousAt (fun s : Fin m → ℝ =>
          H (z + realEmbed s)) t :=
        ContinuousAt.comp_of_eq hH_at hshift_at rfl
      exact hH_shift.mul ψ.continuous.continuousAt
    · have hψ_zero :
          (ψ : (Fin m → ℝ) → ℂ) =ᶠ[nhds t] fun _ => 0 := by
        rwa [notMem_tsupport_iff_eventuallyEq] at ht
      have hprod_zero :
          (fun y : Fin m → ℝ => H (z + realEmbed y) * ψ y)
            =ᶠ[nhds t] fun _ => 0 := by
        filter_upwards [hψ_zero] with y hy
        simp [hy]
      exact hprod_zero.continuousAt
  have hcompact :
      HasCompactSupport fun t : Fin m → ℝ => H (z + realEmbed t) * ψ t :=
    hψ_compact.mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- Kernel-recovery representation algebra: once the translated kernel support
is eventually contained in the chart domain, the representation integral can be
rewritten as the difference integral used by the approximate-identity estimate. -/
theorem regularizedEnvelope_difference_integral_identity_eventually
    (Ucore U0 : Set (ComplexChartSpace m))
    (H : ComplexChartSpace m → ℂ)
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hH_cont : ContinuousOn H U0)
    (hH_rep :
      ∀ n, ∀ z ∈ Ucore,
        G (ψn n) z =
          ∫ t : Fin m → ℝ, H (z + realEmbed t) * ψn n t)
    (hψ_norm : ∀ n, ∫ t : Fin m → ℝ, ψn n t = 1)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ Ucore,
      ∀ᶠ n in atTop,
        G (ψn n) z - H z =
          ∫ t : Fin m → ℝ,
            (H (z + realEmbed t) - H z) * ψn n t := by
  intro z hz
  have htranslate_eventually :
      ∀ᶠ n in atTop,
        ∀ t ∈ tsupport (ψn n : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ U0 ∧ ‖realEmbed t‖ < 1 :=
    eventually_translate_mem_open_of_shrinking_support
      Ucore U0 ψn hU0_open hcore_U0 hψ_support z hz 1 (by norm_num)
  filter_upwards [htranslate_eventually] with n htranslate_n
  have hHψ_int : Integrable fun t : Fin m → ℝ =>
      H (z + realEmbed t) * ψn n t :=
    integrable_continuousOn_realTranslate_mul_kernel
      H (ψn n) U0 z hU0_open hH_cont
      (KernelSupportWithin_hasCompactSupport (hψ_support n))
      (fun t ht => (htranslate_n t ht).1)
  have hconst_int : Integrable fun t : Fin m → ℝ => H z * ψn n t :=
    (SchwartzMap.integrable (ψn n)).const_mul (H z)
  have hconst_integral :
      (∫ t : Fin m → ℝ, H z * ψn n t) = H z := by
    calc
      (∫ t : Fin m → ℝ, H z * ψn n t) =
          H z * ∫ t : Fin m → ℝ, ψn n t := by
            exact MeasureTheory.integral_const_mul
              (H z) (fun t : Fin m → ℝ => ψn n t)
      _ = H z := by
            simp [hψ_norm n]
  calc
    G (ψn n) z - H z =
        (∫ t : Fin m → ℝ, H (z + realEmbed t) * ψn n t) - H z := by
          rw [hH_rep n z hz]
    _ =
        (∫ t : Fin m → ℝ, H (z + realEmbed t) * ψn n t) -
          (∫ t : Fin m → ℝ, H z * ψn n t) := by
          rw [hconst_integral]
    _ =
        ∫ t : Fin m → ℝ,
          H (z + realEmbed t) * ψn n t - H z * ψn n t := by
          rw [(MeasureTheory.integral_sub hHψ_int hconst_int).symm]
    _ =
        ∫ t : Fin m → ℝ,
          (H (z + realEmbed t) - H z) * ψn n t := by
          apply integral_congr_ae
          filter_upwards with t
          ring

/-- Approximate-identity recovery for the holomorphic representative, once the
kernel-recovery expression has already been rewritten as the difference
integral against the local representative.  The separate representation-to-
difference-integral identity carries the remaining compact-support
integrability bookkeeping. -/
theorem regularizedEnvelope_kernelLimit_from_difference_integral
    (Ucore U0 : Set (ComplexChartSpace m))
    (H : ComplexChartSpace m → ℂ)
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hH_cont : ContinuousOn H U0)
    (hdiff :
      ∀ z ∈ Ucore,
        ∀ᶠ n in atTop,
          G (ψn n) z - H z =
            ∫ t : Fin m → ℝ,
              (H (z + realEmbed t) - H z) * ψn n t)
    (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
    (hψ_real : ∀ n t, (ψn n t).im = 0)
    (hψ_norm : ∀ n, ∫ t : Fin m → ℝ, ψn n t = 1)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ Ucore,
      Tendsto (fun n => G (ψn n) z) atTop (nhds (H z)) := by
  intro z hz
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hzU : z ∈ U0 := hcore_U0 hz
  have hcont_at_z :=
    (Metric.continuousOn_iff.mp hH_cont) z hzU (ε / 2) hε2
  obtain ⟨δ, hδ_pos, hδ⟩ := hcont_at_z
  have htranslate_eventually :
      ∀ᶠ n in atTop,
        ∀ t ∈ tsupport (ψn n : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ U0 ∧ ‖realEmbed t‖ < δ :=
    eventually_translate_mem_open_of_shrinking_support
      Ucore U0 ψn hU0_open hcore_U0 hψ_support z hz δ hδ_pos
  have hdiff_eventually := hdiff z hz
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (htranslate_eventually.and hdiff_eventually)
  refine ⟨N, ?_⟩
  intro n hn
  have htranslate_n := (hN n hn).1
  have hdiff_n := (hN n hn).2
  have hnorm_int : ∫ t : Fin m → ℝ, ‖ψn n t‖ = 1 :=
    integral_norm_eq_one_of_real_nonneg_normalized
      (ψn n) (hψ_nonneg n) (hψ_real n) (hψ_norm n)
  have hbound : ∀ t : Fin m → ℝ,
      ‖(H (z + realEmbed t) - H z) * ψn n t‖ ≤
        (ε / 2) * ‖ψn n t‖ := by
    intro t
    by_cases ht : t ∈ tsupport (ψn n : (Fin m → ℝ) → ℂ)
    · have htrans := htranslate_n t ht
      have hdist : dist (z + realEmbed t) z = ‖realEmbed t‖ := by
        rw [dist_eq_norm]
        congr 1
        ext i
        simp
      have hH_small_dist :
          dist (H (z + realEmbed t)) (H z) < ε / 2 :=
        hδ (z + realEmbed t) htrans.1 (by simpa [hdist] using htrans.2)
      have hH_small : ‖H (z + realEmbed t) - H z‖ < ε / 2 := by
        simpa [dist_eq_norm] using hH_small_dist
      calc
        ‖(H (z + realEmbed t) - H z) * ψn n t‖ =
            ‖H (z + realEmbed t) - H z‖ * ‖ψn n t‖ := by
              exact norm_mul _ _
        _ ≤ (ε / 2) * ‖ψn n t‖ := by
              exact mul_le_mul_of_nonneg_right
                (le_of_lt hH_small) (norm_nonneg _)
    · have hzero : ψn n t = 0 := image_eq_zero_of_notMem_tsupport ht
      simp [hzero]
  calc
    dist (G (ψn n) z) (H z) = ‖G (ψn n) z - H z‖ := by
      rw [dist_eq_norm]
    _ = ‖∫ t : Fin m → ℝ,
          (H (z + realEmbed t) - H z) * ψn n t‖ := by
      rw [hdiff_n]
    _ ≤ ∫ t : Fin m → ℝ,
          ‖(H (z + realEmbed t) - H z) * ψn n t‖ := by
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ t : Fin m → ℝ, (ε / 2) * ‖ψn n t‖ := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
      · exact (((SchwartzMap.integrable (ψn n)).norm).const_mul (ε / 2))
      · exact Filter.Eventually.of_forall hbound
    _ = (ε / 2) * ∫ t : Fin m → ℝ, ‖ψn n t‖ := by
      rw [MeasureTheory.integral_const_mul]
    _ = ε / 2 := by
      simp [hnorm_int]
    _ < ε := by
      linarith

/-- Approximate-identity recovery for the holomorphic representative directly
from the regularized kernel representation.  The proof is the composition of
the compact-support difference-integral identity with the kernel-limit
estimate. -/
theorem regularizedEnvelope_kernelLimit_from_representation
    (Ucore U0 : Set (ComplexChartSpace m))
    (H : ComplexChartSpace m → ℂ)
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hH_cont : ContinuousOn H U0)
    (hH_rep :
      ∀ n, ∀ z ∈ Ucore,
        G (ψn n) z =
          ∫ t : Fin m → ℝ, H (z + realEmbed t) * ψn n t)
    (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
    (hψ_real : ∀ n t, (ψn n t).im = 0)
    (hψ_norm : ∀ n, ∫ t : Fin m → ℝ, ψn n t = 1)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ Ucore,
      Tendsto (fun n => G (ψn n) z) atTop (nhds (H z)) :=
  regularizedEnvelope_kernelLimit_from_difference_integral
    Ucore U0 H G ψn hU0_open hcore_U0 hH_cont
    (regularizedEnvelope_difference_integral_identity_eventually
      Ucore U0 H G ψn hU0_open hcore_U0 hH_cont
      hH_rep hψ_norm hψ_support)
    hψ_nonneg hψ_real hψ_norm hψ_support

/-- Real-direction mollification of a local holomorphic side function by a
compact real kernel. -/
noncomputable def realMollifyLocal
    (F : ComplexChartSpace m → ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    ComplexChartSpace m → ℂ :=
  fun z => ∫ t : Fin m → ℝ, F (z + realEmbed t) * ψ t

/-- Once the recovered holomorphic representative has the same kernel limit as
the regularized plus/minus side mollifications, uniqueness of limits identifies
it with the original side functions on the shrunken wedge pieces. -/
theorem regularizedEnvelope_deltaLimit_agreesOnWedges
    (Ucore : Set (ComplexChartSpace m))
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (Fplus Fminus H : ComplexChartSpace m → ℂ)
    (DplusSmall DminusSmall : Set (ComplexChartSpace m))
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hG_plus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DplusSmall,
        G (ψn n) z = realMollifyLocal Fplus (ψn n) z)
    (hG_minus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DminusSmall,
        G (ψn n) z = realMollifyLocal Fminus (ψn n) z)
    (happrox_plus :
      ∀ z ∈ Ucore ∩ DplusSmall,
        Tendsto (fun n => realMollifyLocal Fplus (ψn n) z)
          atTop (nhds (Fplus z)))
    (happrox_minus :
      ∀ z ∈ Ucore ∩ DminusSmall,
        Tendsto (fun n => realMollifyLocal Fminus (ψn n) z)
          atTop (nhds (Fminus z)))
    (hkernel_limit :
      ∀ z ∈ Ucore, Tendsto (fun n => G (ψn n) z) atTop (nhds (H z))) :
    (∀ z ∈ Ucore ∩ DplusSmall, H z = Fplus z) ∧
    (∀ z ∈ Ucore ∩ DminusSmall, H z = Fminus z) := by
  constructor
  · intro z hz
    have hG_to_plus : Tendsto (fun n => G (ψn n) z) atTop (nhds (Fplus z)) :=
      Tendsto.congr'
        (by
          filter_upwards [hG_plus] with n hn
          exact (hn z hz).symm)
        (happrox_plus z hz)
    exact tendsto_nhds_unique (hkernel_limit z hz.1) hG_to_plus
  · intro z hz
    have hG_to_minus : Tendsto (fun n => G (ψn n) z) atTop (nhds (Fminus z)) :=
      Tendsto.congr'
        (by
          filter_upwards [hG_minus] with n hn
          exact (hn z hz).symm)
        (happrox_minus z hz)
    exact tendsto_nhds_unique (hkernel_limit z hz.1) hG_to_minus

/-- A translation-covariant product kernel whose regularized scalar kernels are
holomorphic on a chart domain descends to a distributional-holomorphic chart
distribution, hence to a holomorphic representative on that chart.

This is the Streater-Wightman kernel-recovery midpoint.  The remaining
envelope step is to show, by compactly supported approximate identities, that
the produced holomorphic function agrees with the original plus/minus wedge
functions on the shrunken wedge pieces. -/
theorem regularizedEnvelope_holomorphicDistribution_from_productKernel
    {r : ℝ}
    (hm : 0 < m)
    (hr : 0 < r)
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (U0 : Set (ComplexChartSpace m))
    (hU0_open : IsOpen U0)
    (hcov : ProductKernelRealTranslationCovariantGlobal K)
    (hG_holo : ∀ ψ, KernelSupportWithin ψ r → DifferentiableOn ℂ (G ψ) U0)
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0 →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m, G ψ z * φ z) :
    ∃ H : ComplexChartSpace m → ℂ,
      DifferentiableOn ℂ H U0 ∧
      ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ,
        RepresentsDistributionOnComplexDomain Hdist H U0 ∧
        ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m → ℝ) ℂ),
          K (schwartzTensorProduct₂ φ ψ) =
            Hdist (realConvolutionTest φ ψ) := by
  obtain ⟨ψn, hψ_norm, _hψ_small, hψ_support, hψ_approx⟩ :=
    exists_realConvolutionTest_approxIdentity (m := m) hr
  obtain ⟨Hdist, hdesc⟩ :=
    translationCovariantProductKernel_descends K hcov (ψn 0) (hψ_norm 0)
  have hK_dbar_zero :
      ∀ (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0 →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0 := by
    intro j φ ψ hφ hψ
    exact
      regularizedEnvelope_productKernel_dbar_eq_zero
        K G U0 hU0_open hG_holo hK_rep j φ hφ ψ hψ
  have hCR : IsDistributionalHolomorphicOn Hdist U0 :=
    translationCovariantKernel_distributionalHolomorphic
      (Hdist := Hdist) (K := K) (ψι := ψn)
      (hψ_support := Filter.Eventually.of_forall hψ_support)
      (hψ_approx := hψ_approx)
      (hdesc := hdesc)
      (hK_dbar_zero := hK_dbar_zero)
  obtain ⟨H, hH_holo, hRep⟩ :=
    distributionalHolomorphic_regular Hdist hm hU0_open hCR
  exact ⟨H, hH_holo, Hdist, hRep, hdesc⟩

end SCV
