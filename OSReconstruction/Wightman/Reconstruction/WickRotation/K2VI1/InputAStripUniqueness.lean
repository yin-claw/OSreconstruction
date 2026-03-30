import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputADiffBlock
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAOneVariableUniqueness

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The common witness section along the zero-center shifted real slice. -/
def commonZeroCenterShiftSection_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (s : ℝ) : SpacetimeDim d → ℂ := fun ξ =>
  k2TimeParametricKernel (d := d) G
    ![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)]

/-- The translated real section used to compare against a fixed probe witness. -/
def translatedProbeArg_local
    (a : SpacetimeDim d)
    (s : ℝ) : SpacetimeDim d → NPointDomain d 2 := fun ξ =>
  ![(a : SpacetimeDim d), a + ξ + timeShiftVec d (s + s)]

/-- The one-variable kernel extracted from a translated probe section. -/
def translatedProbeSection_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (a : SpacetimeDim d)
    (s : ℝ) : SpacetimeDim d → ℂ := fun ξ =>
  k2TimeParametricKernel (d := d)
    (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg)
    (translatedProbeArg_local (d := d) a s ξ)

/-- The common zero-center section is continuous on the fixed strip as soon as
the common witness is tube-continuous and diff-block-dependent. -/
theorem continuousOn_commonZeroCenterShiftSection_on_fixedStrip_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (s : ℝ) :
    ContinuousOn
      (commonZeroCenterShiftSection_local (d := d) G s)
      {ξ : SpacetimeDim d | -(s + s) < ξ 0} := by
  refine
    (commonLiftedDifferenceSliceKernel_continuousOn_local
      (d := d) G hG_holo s).congr ?_
  intro ξ hξ
  symm
  exact
    commonLiftedDifferenceSliceKernel_eq_k2TimeParametricKernel_on_zeroCenterShift_of_diffBlockDependence_local
      (d := d) G hG_diff s ξ

/-- The translated probe section is continuous on the same fixed strip. -/
theorem continuousOn_translatedProbeSection_on_fixedStrip_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (a : SpacetimeDim d)
    (s : ℝ) :
    ContinuousOn
      (translatedProbeSection_local (d := d) OS lgc φ hφ_compact hφ_neg a s)
      {ξ : SpacetimeDim d | -(s + s) < ξ 0} := by
  have hprobe_arg_cont :
      Continuous (translatedProbeArg_local (d := d) a s) := by
    refine continuous_pi ?_
    intro i
    fin_cases i
    · simpa [translatedProbeArg_local] using
        (continuous_const : Continuous fun _ : SpacetimeDim d => a)
    · simpa [translatedProbeArg_local] using
        ((continuous_const : Continuous fun _ : SpacetimeDim d => a).add continuous_id).add
          (continuous_const : Continuous fun _ : SpacetimeDim d => timeShiftVec d (s + s))
  have hprobe_arg_maps :
      Set.MapsTo (translatedProbeArg_local (d := d) a s)
        {ξ : SpacetimeDim d | -(s + s) < ξ 0}
        {x : NPointDomain d 2 | x 0 0 < x 1 0} := by
    intro ξ hξ
    change (translatedProbeArg_local (d := d) a s ξ) 0 0 <
      (translatedProbeArg_local (d := d) a s ξ) 1 0
    have hstrip : -(s + s) < ξ 0 := hξ
    simp [translatedProbeArg_local, timeShiftVec]
    linarith
  exact
    (continuousOn_k2TimeParametricKernel_of_pos_local
      (d := d) OS lgc φ hφ_compact hφ_neg).comp
        hprobe_arg_cont.continuousOn hprobe_arg_maps

/-- Compact-support strip pairing equality upgrades to pointwise equality
between the common zero-center section and any comparison kernel that is
continuous on the same fixed strip. -/
theorem zeroCenterShift_eq_comparison_of_compactSupport_pairing_eq_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (K_cmp : SpacetimeDim d → ℂ)
    (s : ℝ)
    (hK_cont : ContinuousOn K_cmp {ξ : SpacetimeDim d | -(s + s) < ξ 0})
    (hpair_eq : ∀ h : SchwartzSpacetime d,
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -(s + s) < ξ 0} →
      ∫ ξ : SpacetimeDim d,
        commonZeroCenterShiftSection_local (d := d) G s ξ * h ξ =
        ∫ ξ : SpacetimeDim d, K_cmp ξ * h ξ) :
    Set.EqOn
      (commonZeroCenterShiftSection_local (d := d) G s)
      K_cmp
      {ξ : SpacetimeDim d | -(s + s) < ξ 0} := by
  exact
    eqOn_fixedStrip_of_compactSupport_schwartz_integral_eq_continuousOn_local
      (d := d) (s + s)
      (continuousOn_commonZeroCenterShiftSection_on_fixedStrip_local
        (d := d) G hG_holo hG_diff s)
      hK_cont
      hpair_eq

/-- To compare the common zero-center section with a one-variable comparison
kernel on the whole fixed strip, it is already enough to compare the common
fixed-time kernel with that comparison kernel on one normalized fixed-center
shell family `χc(z₀) * h(z₁)`. Under diff-block dependence, both sides
factorize through the same one-variable kernels, so this shell-level equality
is exactly the compact-support strip pairing equality needed downstream. -/
theorem compactSupport_pairing_eq_comparison_of_fixedCenter_pairing_eq_of_diffBlockDependence_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (K_cmp : SpacetimeDim d → ℂ)
    (s : ℝ)
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (hcenter_eq : ∀ h : SchwartzSpacetime d,
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -(s + s) < ξ 0} →
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
          (χc (z 0) * h (z 1)) =
        ∫ z : NPointDomain d 2,
          K_cmp (z 1) * (χc (z 0) * h (z 1))) :
    ∀ h : SchwartzSpacetime d,
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -(s + s) < ξ 0} →
      ∫ ξ : SpacetimeDim d,
        commonZeroCenterShiftSection_local (d := d) G s ξ * h ξ =
        ∫ ξ : SpacetimeDim d, K_cmp ξ * h ξ := by
  intro h hh_compact hh_strip
  have hcmp_factor :
      ∫ z : NPointDomain d 2, K_cmp (z 1) * (χc (z 0) * h (z 1)) =
        ∫ ξ : SpacetimeDim d, K_cmp ξ * h ξ := by
    calc
      ∫ z : NPointDomain d 2, K_cmp (z 1) * (χc (z 0) * h (z 1)) =
          (∫ u : SpacetimeDim d, χc u) * ∫ ξ : SpacetimeDim d, K_cmp ξ * h ξ := by
            exact integral_centerDiff_differenceOnly_kernel_factorizes
              (d := d) K_cmp χc h
      _ = ∫ ξ : SpacetimeDim d, K_cmp ξ * h ξ := by
            rw [hχc, one_mul]
  have hslice_factor :
      ∫ z : NPointDomain d 2,
          commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
            (χc (z 0) * h (z 1)) =
        ∫ ξ : SpacetimeDim d,
          commonLiftedDifferenceSliceKernel_local (d := d) G s ξ * h ξ := by
    calc
      ∫ z : NPointDomain d 2,
          commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
            (χc (z 0) * h (z 1)) =
          (∫ u : SpacetimeDim d, χc u) *
            ∫ ξ : SpacetimeDim d,
              commonLiftedDifferenceSliceKernel_local (d := d) G s ξ * h ξ := by
            exact integral_centerDiff_differenceOnly_kernel_factorizes
              (d := d) (commonLiftedDifferenceSliceKernel_local (d := d) G s) χc h
      _ = ∫ ξ : SpacetimeDim d,
            commonLiftedDifferenceSliceKernel_local (d := d) G s ξ * h ξ := by
            rw [hχc, one_mul]
  have hfixed_eq_slice :
      ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            (χc (z 0) * h (z 1)) =
        ∫ z : NPointDomain d 2,
          commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
            (χc (z 0) * h (z 1)) := by
    refine integral_congr_ae ?_
    filter_upwards with z
    rw [twoPointFixedTimeCenterDiffKernel_eq_commonLiftedDifferenceSlice_of_diffBlockDependence_local
      (d := d) G hG_diff s z]
  calc
    ∫ ξ : SpacetimeDim d,
        commonZeroCenterShiftSection_local (d := d) G s ξ * h ξ =
      ∫ ξ : SpacetimeDim d,
        commonLiftedDifferenceSliceKernel_local (d := d) G s ξ * h ξ := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          rw [commonLiftedDifferenceSliceKernel_eq_k2TimeParametricKernel_on_zeroCenterShift_of_diffBlockDependence_local
            (d := d) G hG_diff s ξ]
          rfl
    _ =
      ∫ z : NPointDomain d 2,
        commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
          (χc (z 0) * h (z 1)) := by
            symm
            exact hslice_factor
    _ =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
          (χc (z 0) * h (z 1)) := by
            symm
            exact hfixed_eq_slice
    _ =
      ∫ z : NPointDomain d 2,
        K_cmp (z 1) * (χc (z 0) * h (z 1)) := hcenter_eq h hh_compact hh_strip
    _ = ∫ ξ : SpacetimeDim d, K_cmp ξ * h ξ := hcmp_factor

/-- Bundled fixed-center-shell version of the strip-bound transfer.

Under diff-block dependence, it is enough to compare the common fixed-time
kernel with a bounded comparison kernel on one normalized fixed-center shell
family `χc(z₀) * h(z₁)`. The compact-support strip pairing equality then follows
formally, and the comparison-kernel strip bound transfers to the common lifted
slice. -/
theorem exists_common_lifted_difference_slice_strip_bound_of_fixedCenter_pairing_eq_comparison_of_diffBlockDependence_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (K_cmp : SpacetimeDim d → ℂ)
    (s : ℝ)
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (hK_cont : ContinuousOn K_cmp {ξ : SpacetimeDim d | -(s + s) < ξ 0})
    (C_bd : ℝ)
    (N : ℕ)
    (hC : 0 < C_bd)
    (hK_bound : ∀ ξ : SpacetimeDim d, -(s + s) < ξ 0 →
      ‖K_cmp ξ‖ ≤ C_bd * (1 + ‖ξ‖) ^ N)
    (hcenter_eq : ∀ h : SchwartzSpacetime d,
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -(s + s) < ξ 0} →
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
          (χc (z 0) * h (z 1)) =
        ∫ z : NPointDomain d 2,
          K_cmp (z 1) * (χc (z 0) * h (z 1))) :
    ∃ (C_bd' : ℝ) (N' : ℕ),
      0 < C_bd' ∧
      ∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)‖ ≤
          C_bd' * (1 + ‖z‖) ^ N' := by
  have hpair_eq :
      ∀ h : SchwartzSpacetime d,
        HasCompactSupport (h : SpacetimeDim d → ℂ) →
        tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -(s + s) < ξ 0} →
        ∫ ξ : SpacetimeDim d,
          commonZeroCenterShiftSection_local (d := d) G s ξ * h ξ =
          ∫ ξ : SpacetimeDim d, K_cmp ξ * h ξ :=
    compactSupport_pairing_eq_comparison_of_fixedCenter_pairing_eq_of_diffBlockDependence_local
      (d := d) G hG_diff K_cmp s χc hχc hcenter_eq
  have hEq :
      Set.EqOn
        (commonZeroCenterShiftSection_local (d := d) G s)
        K_cmp
        {ξ : SpacetimeDim d | -(s + s) < ξ 0} :=
    zeroCenterShift_eq_comparison_of_compactSupport_pairing_eq_local
      (d := d) G hG_holo hG_diff K_cmp s hK_cont hpair_eq
  have hzero_bound :
      ∀ ξ : SpacetimeDim d, -(s + s) < ξ 0 →
        ‖commonZeroCenterShiftSection_local (d := d) G s ξ‖ ≤
          C_bd * (1 + ‖ξ‖) ^ N := by
    intro ξ hz
    rw [hEq hz]
    exact hK_bound ξ hz
  exact
    exists_common_lifted_difference_slice_strip_bound_of_k2TimeParametricKernel_zeroCenterShift_bound_of_diffBlockDependence_local
      (d := d) G hG_diff s C_bd N hC hzero_bound

/-- Compact-support strip pairing equality transfers the comparison-kernel
bound directly to the common zero-center shifted section. This is the honest
one-variable form of the current root Input-A seam. -/
theorem exists_commonZeroCenterShiftSection_bound_of_compactSupport_pairing_eq_comparison_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (K_cmp : SpacetimeDim d → ℂ)
    (s : ℝ)
    (hK_cont : ContinuousOn K_cmp {ξ : SpacetimeDim d | -(s + s) < ξ 0})
    (C_bd : ℝ)
    (N : ℕ)
    (hC : 0 < C_bd)
    (hK_bound : ∀ ξ : SpacetimeDim d, -(s + s) < ξ 0 →
      ‖K_cmp ξ‖ ≤ C_bd * (1 + ‖ξ‖) ^ N)
    (hpair_eq : ∀ h : SchwartzSpacetime d,
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -(s + s) < ξ 0} →
      ∫ ξ : SpacetimeDim d,
        commonZeroCenterShiftSection_local (d := d) G s ξ * h ξ =
        ∫ ξ : SpacetimeDim d, K_cmp ξ * h ξ) :
    ∃ (C_bd' : ℝ) (N' : ℕ),
      0 < C_bd' ∧
      ∀ ξ : SpacetimeDim d, -(s + s) < ξ 0 →
        ‖commonZeroCenterShiftSection_local (d := d) G s ξ‖ ≤
          C_bd' * (1 + ‖ξ‖) ^ N' := by
  refine ⟨C_bd, N, hC, ?_⟩
  have hEq :=
    zeroCenterShift_eq_comparison_of_compactSupport_pairing_eq_local
      (d := d) G hG_holo hG_diff K_cmp s hK_cont hpair_eq
  intro ξ hξ
  rw [hEq hξ]
  exact hK_bound ξ hξ

/-- Once the compact-support strip pairings of the common zero-center section
and a comparison kernel agree, the pointwise strip bound transfers from the
comparison kernel to the common lifted slice. -/
theorem exists_common_lifted_difference_slice_strip_bound_of_compactSupport_pairing_eq_comparison_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (K_cmp : SpacetimeDim d → ℂ)
    (s : ℝ)
    (hK_cont : ContinuousOn K_cmp {ξ : SpacetimeDim d | -(s + s) < ξ 0})
    (C_bd : ℝ)
    (N : ℕ)
    (hC : 0 < C_bd)
    (hK_bound : ∀ ξ : SpacetimeDim d, -(s + s) < ξ 0 →
      ‖K_cmp ξ‖ ≤ C_bd * (1 + ‖ξ‖) ^ N)
    (hpair_eq : ∀ h : SchwartzSpacetime d,
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -(s + s) < ξ 0} →
      ∫ ξ : SpacetimeDim d,
        commonZeroCenterShiftSection_local (d := d) G s ξ * h ξ =
        ∫ ξ : SpacetimeDim d, K_cmp ξ * h ξ) :
    ∃ (C_bd : ℝ) (N : ℕ),
      0 < C_bd ∧
      ∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)‖ ≤
          C_bd * (1 + ‖z‖) ^ N := by
  refine ⟨C_bd, N, hC, ?_⟩
  have hEq :=
    zeroCenterShift_eq_comparison_of_compactSupport_pairing_eq_local
      (d := d) G hG_holo hG_diff K_cmp s hK_cont hpair_eq
  intro z hz
  have hsec :
      commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) = K_cmp (z 1) := by
    rw [commonLiftedDifferenceSliceKernel_eq_k2TimeParametricKernel_on_zeroCenterShift_of_diffBlockDependence_local
      (d := d) G hG_diff s (z 1)]
    simpa [commonZeroCenterShiftSection_local] using hEq hz
  have hz1_le : ‖z 1‖ ≤ ‖z‖ := norm_le_pi_norm z 1
  rw [hsec]
  calc
    ‖K_cmp (z 1)‖ ≤ C_bd * (1 + ‖z 1‖) ^ N := hK_bound (z 1) hz
    _ ≤ C_bd * (1 + ‖z‖) ^ N := by
      gcongr

/-- Probe-specialized corollary of the generic strip-uniqueness transfer. -/
theorem zeroCenterShift_eq_translated_probe_section_of_compactSupport_pairing_eq_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (a : SpacetimeDim d)
    (s : ℝ)
    (hpair_eq : ∀ h : SchwartzSpacetime d,
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -(s + s) < ξ 0} →
      ∫ ξ : SpacetimeDim d,
        commonZeroCenterShiftSection_local (d := d) G s ξ * h ξ =
        ∫ ξ : SpacetimeDim d,
          translatedProbeSection_local (d := d) OS lgc φ hφ_compact hφ_neg a s ξ * h ξ) :
    Set.EqOn
      (commonZeroCenterShiftSection_local (d := d) G s)
      (translatedProbeSection_local (d := d) OS lgc φ hφ_compact hφ_neg a s)
      {ξ : SpacetimeDim d | -(s + s) < ξ 0} := by
  exact
    zeroCenterShift_eq_comparison_of_compactSupport_pairing_eq_local
      (d := d) G hG_holo hG_diff
      (translatedProbeSection_local (d := d) OS lgc φ hφ_compact hφ_neg a s)
      s
      (continuousOn_translatedProbeSection_on_fixedStrip_local
        (d := d) OS lgc φ hφ_compact hφ_neg a s)
      hpair_eq

/-- Bundled transfer from compact-support strip pairing equality with a bounded
comparison kernel to the common lifted-slice strip bound, using diff-block
dependence to identify the lifted slice with the common zero-center section. -/
theorem exists_common_lifted_difference_slice_strip_bound_of_compactSupport_pairing_eq_comparison_of_diffBlockDependence_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (K_cmp : SpacetimeDim d → ℂ)
    (s : ℝ)
    (hK_cont : ContinuousOn K_cmp {ξ : SpacetimeDim d | -(s + s) < ξ 0})
    (C_bd : ℝ)
    (N : ℕ)
    (hC : 0 < C_bd)
    (hK_bound : ∀ ξ : SpacetimeDim d, -(s + s) < ξ 0 →
      ‖K_cmp ξ‖ ≤ C_bd * (1 + ‖ξ‖) ^ N)
    (hpair_eq : ∀ h : SchwartzSpacetime d,
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -(s + s) < ξ 0} →
      ∫ ξ : SpacetimeDim d,
        commonZeroCenterShiftSection_local (d := d) G s ξ * h ξ =
        ∫ ξ : SpacetimeDim d, K_cmp ξ * h ξ) :
    ∃ (C_bd' : ℝ) (N' : ℕ),
      0 < C_bd' ∧
      ∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)‖ ≤
          C_bd' * (1 + ‖z‖) ^ N' := by
  obtain ⟨C_bd', N', hC', hzero_bound⟩ :=
    exists_commonZeroCenterShiftSection_bound_of_compactSupport_pairing_eq_comparison_local
      (d := d) G hG_holo hG_diff K_cmp s hK_cont C_bd N hC hK_bound hpair_eq
  exact
    exists_common_lifted_difference_slice_strip_bound_of_k2TimeParametricKernel_zeroCenterShift_bound_of_diffBlockDependence_local
      (d := d) G hG_diff s C_bd' N' hC' hzero_bound

end OSReconstruction
