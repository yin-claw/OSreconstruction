import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputADiffBlock
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

open Complex MeasureTheory Filter Topology

namespace OSReconstruction

variable {d : ℕ}

/-- One-variable identity theorem used in the common-`G` center-independence
lane.

If a holomorphic function on the upper half-plane agrees almost everywhere with
a constant along the positive imaginary axis, then it is that constant
everywhere on the upper half-plane. The almost-everywhere hypothesis is first
upgraded to pointwise equality on `(0, ∞)` using continuity on the open ray,
and then the analytic identity theorem propagates that equality to the whole
connected domain. -/
theorem analytic_constant_of_ae_constant_on_imaginary_axis
    (f : ℂ → ℂ) (c : ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hae : ∀ᵐ t : ℝ ∂volume, 0 < t → f (Complex.I * (t : ℂ)) = c) :
    ∀ z : ℂ, 0 < z.im → f z = c := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hanalytic : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im} :=
    hf.analyticOnNhd hopen
  have hcont_axis : ContinuousOn (fun t : ℝ => f (Complex.I * (t : ℂ))) (Set.Ioi 0) := by
    refine hf.continuousOn.comp ?_ ?_
    · exact (continuous_const.mul Complex.continuous_ofReal).continuousOn
    · intro t ht
      simpa using ht
  have hae_axis :
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi 0)), f (Complex.I * (t : ℂ)) = c := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with t ht
    exact ht
  have haxis : ∀ t : ℝ, 0 < t → f (Complex.I * (t : ℂ)) = c := by
    have hEqOn :
        Set.EqOn (fun t : ℝ => f (Complex.I * (t : ℂ))) (fun _ : ℝ => c) (Set.Ioi 0) := by
      exact MeasureTheory.Measure.eqOn_open_of_ae_eq
        hae_axis isOpen_Ioi hcont_axis continuousOn_const
    intro t ht
    exact hEqOn ht
  have hI_mem : Complex.I ∈ {z : ℂ | 0 < z.im} := by simp [Complex.I_im]
  have hclosure : Complex.I ∈ closure ({z : ℂ | f z = c} \ {Complex.I}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨Complex.I * (((1 + ε / 2 : ℝ) : ℂ)), ?_, ?_⟩
    · constructor
      · have ht : 0 < 1 + ε / 2 := by linarith
        simpa using haxis (1 + ε / 2) ht
      · intro hEq
        have hEq0 : Complex.I * (((1 + ε / 2 : ℝ) : ℂ)) = Complex.I := by
          simpa using hEq
        have hEq1 : Complex.I * (((1 + ε / 2 : ℝ) : ℂ)) = Complex.I * (1 : ℂ) := by
          simpa using hEq0
        have hEq' : (((1 + ε / 2 : ℝ) : ℂ)) = 1 := by
          exact mul_left_cancel₀ Complex.I_ne_zero hEq1
        have hEq'' : (1 + ε / 2 : ℝ) = 1 := by
          exact Complex.ofReal_injective hEq'
        linarith
    · rw [Complex.dist_eq]
      have hhalf_lt : ε / 2 < ε := by linarith
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, Complex.norm_mul,
        Complex.norm_I, one_mul, abs_of_pos hε] using hhalf_lt
  have hconn : IsPreconnected {z : ℂ | 0 < z.im} :=
    (Complex.isConnected_of_upperHalfPlane (r := 0) (fun _ h => h)
      (fun z (h : 0 < z.im) => le_of_lt h)).isPreconnected
  have hf_eq_const : Set.EqOn f (fun _ : ℂ => c) {z : ℂ | 0 < z.im} := by
    exact hanalytic.eqOn_of_preconnected_of_mem_closure analyticOnNhd_const
      hconn hI_mem hclosure
  intro z hz
  exact hf_eq_const hz

/-- Fiberwise analytic propagation for flat positive-time-difference witnesses.

Fix a point `z` in the flattened tube and one block-time slot `i`. If the
corresponding one-variable fiber
`w ↦ G(update z (i,0) w)` agrees almost everywhere with a constant along the
positive imaginary axis, then that fiber is identically constant on the upper
half-plane. This is the reusable midpoint between the raw one-variable identity
theorem and the eventual center/diff-block independence statements for the
common witness. -/
theorem flatPositiveTimeDiffWitness_blockTime_constant_of_ae_imaginary_axis
    {k : ℕ}
    (G : (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (z : Fin (k * (d + 1)) → ℂ)
    (hz : z ∈ SCV.TubeDomain (FlatPositiveTimeDiffReal k d))
    (i : Fin k)
    (c : ℂ)
    (hae : ∀ᵐ t : ℝ ∂volume,
      0 < t →
        G (Function.update z (finProdFinEquiv (i, (0 : Fin (d + 1)))) (Complex.I * (t : ℂ))) = c) :
    ∀ w : ℂ, 0 < w.im →
      G (Function.update z (finProdFinEquiv (i, (0 : Fin (d + 1)))) w) = c := by
  rcases hG_holo with ⟨_hG_cont, hG_diff⟩
  exact
    analytic_constant_of_ae_constant_on_imaginary_axis
      (fun w =>
        G (Function.update z (finProdFinEquiv (i, (0 : Fin (d + 1)))) w))
      c
      (hG_diff z hz i)
      hae

section CLMBound

variable [NeZero d]

omit [NeZero d] in
private theorem twoPointDifferenceLift_fixedTranslate_seminorm_bound_exists_local
    (χ : SchwartzSpacetime d)
    (a : SpacetimeDim d)
    (p l : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : NNReal, C ≠ 0 ∧
      ∀ h : SchwartzSpacetime d,
        SchwartzMap.seminorm ℝ p l
          (twoPointDifferenceLift χ (SCV.translateSchwartz a h)) ≤
            (C • s.sup (schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ)) h := by
  let L : SchwartzSpacetime d →L[ℂ] SchwartzNPoint d 2 :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (twoPointCenterDiffCLE d).symm).comp
      ((SchwartzMap.prependFieldCLMRight (E := SpacetimeDim d) (n := 1) χ).comp
        ((onePointToFin1CLM d).comp (SCV.translateSchwartzCLM a)))
  let q : Seminorm ℝ (SchwartzSpacetime d) :=
    (schwartzSeminormFamily ℝ (NPointDomain d 2) ℂ (p, l)).comp
      (L.restrictScalars ℝ).toLinearMap
  have hq_cont : Continuous q := by
    change Continuous (fun h : SchwartzSpacetime d =>
      schwartzSeminormFamily ℝ (NPointDomain d 2) ℂ (p, l) (L h))
    exact ((schwartz_withSeminorms ℝ (NPointDomain d 2) ℂ).continuous_seminorm (p, l)).comp
      L.continuous
  obtain ⟨s, C, hC_ne, hq_bound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ (SpacetimeDim d) ℂ) q hq_cont
  refine ⟨s, C, hC_ne, ?_⟩
  intro h
  change (schwartzSeminormFamily ℝ (NPointDomain d 2) ℂ (p, l)) (L h) ≤
    (C • s.sup (schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ)) h
  simpa [q, L, twoPointDifferenceLift] using hq_bound h

/-- CLM estimate for the common lifted slice on positive-time compact-support
tests.

This packages the exact part of the direct analytic fallback route: once the
common witness has Euclidean reproduction and diff-block dependence, pairing the
common lifted slice against a positive-time compact-support test is bounded by a
finite supremum of Schwartz seminorms of that test. The remaining unproved step
for the direct route is only the upgrade from this bounded CLM estimate plus
continuity to a pointwise polynomial-growth bound. -/
theorem commonLiftedSlice_clm_bound_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (s : ℝ) (hs : 0 < s)
    (χ₀ : SchwartzSpacetime d) (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1) :
    ∃ (C : ℝ) (semIdx : Finset (ℕ × ℕ)), 0 < C ∧
      ∀ (h : SchwartzSpacetime d),
        HasCompactSupport (h : SpacetimeDim d → ℂ) →
        tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} →
        ‖∫ ξ : SpacetimeDim d,
          commonLiftedDifferenceSliceKernel_local (d := d) G s ξ * h ξ‖ ≤
          C * (semIdx.sup (schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ)) h := by
  let m := lgc.sobolev_index
  let A : ℝ := lgc.alpha * lgc.beta ^ 2 * ((2).factorial : ℝ) ^ lgc.gamma
  obtain ⟨semIdx, C0, hC0_ne, hsemi⟩ :=
    twoPointDifferenceLift_fixedTranslate_seminorm_bound_exists_local
      (d := d) χ₀ (- timeShiftVec d (s + s)) m m
  have hC0_pos : 0 < (C0 : ℝ) := by
    have hC0_nonneg : 0 ≤ (C0 : ℝ) := by exact_mod_cast C0.2
    have hC0_ne' : (C0 : ℝ) ≠ 0 := by exact_mod_cast hC0_ne
    exact lt_of_le_of_ne hC0_nonneg hC0_ne'.symm
  have hA_pos : 0 < A := by
    dsimp [A]
    have hbeta_pow_pos : 0 < lgc.beta ^ 2 := by
      nlinarith [sq_pos_of_pos lgc.beta_pos]
    have hfac_pos : 0 < ((2).factorial : ℝ) := by norm_num
    have hpow_pos : 0 < ((2).factorial : ℝ) ^ lgc.gamma := by
      exact Real.rpow_pos_of_pos hfac_pos lgc.gamma
    exact mul_pos (mul_pos lgc.alpha_pos hbeta_pow_pos) hpow_pos
  refine ⟨A * C0, semIdx, mul_pos hA_pos hC0_pos, ?_⟩
  intro h hh_compact hh_pos
  have hslice_factor :
      ∫ z : NPointDomain d 2,
          commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
            (χ₀ (z 0) * h (z 1)) =
        ∫ ξ : SpacetimeDim d,
          commonLiftedDifferenceSliceKernel_local (d := d) G s ξ * h ξ := by
    calc
      ∫ z : NPointDomain d 2,
          commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
            (χ₀ (z 0) * h (z 1)) =
          (∫ u : SpacetimeDim d, χ₀ u) *
            ∫ ξ : SpacetimeDim d,
              commonLiftedDifferenceSliceKernel_local (d := d) G s ξ * h ξ := by
            exact integral_centerDiff_differenceOnly_kernel_factorizes
              (d := d) (commonLiftedDifferenceSliceKernel_local (d := d) G s) χ₀ h
      _ = ∫ ξ : SpacetimeDim d,
            commonLiftedDifferenceSliceKernel_local (d := d) G s ξ * h ξ := by
            rw [hχ₀, one_mul]
  have hfixed_eq_slice :
      ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            (χ₀ (z 0) * h (z 1)) =
        ∫ z : NPointDomain d 2,
          commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
            (χ₀ (z 0) * h (z 1)) := by
    refine integral_congr_ae ?_
    filter_upwards with z
    rw [twoPointFixedTimeCenterDiffKernel_eq_commonLiftedDifferenceSlice_of_diffBlockDependence_local
      (d := d) G hG_diff s z]
  have hpair_eq :
      ∫ ξ : SpacetimeDim d,
          commonLiftedDifferenceSliceKernel_local (d := d) G s ξ * h ξ =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ₀
              (SCV.translateSchwartz (- timeShiftVec d (s + s)) h))) := by
    calc
      ∫ ξ : SpacetimeDim d,
          commonLiftedDifferenceSliceKernel_local (d := d) G s ξ * h ξ =
        ∫ z : NPointDomain d 2,
          commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
            (χ₀ (z 0) * h (z 1)) := by
            symm
            exact hslice_factor
      _ =
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            (χ₀ (z 0) * h (z 1)) := by
            symm
            exact hfixed_eq_slice
      _ =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ₀
              (SCV.translateSchwartz (- timeShiftVec d (s + s)) h))) := by
            simpa [Complex.ofReal_add] using
              (fixedTimeCenterDiffKernel_fixed_center_pairing_eq_schwinger_timeShift_local
                (d := d) OS G hG_euclid χ₀ h hh_pos (s + s) (by linarith))
  have hzero_not_mem :
      (0 : SpacetimeDim d) ∉
        tsupport ((((SCV.translateSchwartz (- timeShiftVec d (s + s)) h) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ)) := by
    refine zero_not_mem_tsupport_translate_of_notMem (d := d) h (- timeShiftVec d (s + s)) ?_
    exact neg_timeShiftVec_not_mem_positive_tsupport (d := d) h hh_pos (s + s) (by linarith)
  have hvanish :
      VanishesToInfiniteOrderOnCoincidence
        (twoPointDifferenceLift χ₀
          (SCV.translateSchwartz (- timeShiftVec d (s + s)) h)) := by
    exact twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ₀
      (SCV.translateSchwartz (- timeShiftVec d (s + s)) h) hzero_not_mem
  have hgrowth :
      ‖OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ₀
              (SCV.translateSchwartz (- timeShiftVec d (s + s)) h)))‖ ≤
        A * SchwartzMap.seminorm ℝ m m
          ((ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ₀
              (SCV.translateSchwartz (- timeShiftVec d (s + s)) h)) : ZeroDiagonalSchwartz d 2).1) := by
    simpa [A, m] using
      (lgc.growth_estimate 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ₀
            (SCV.translateSchwartz (- timeShiftVec d (s + s)) h))))
  calc
    ‖∫ ξ : SpacetimeDim d,
        commonLiftedDifferenceSliceKernel_local (d := d) G s ξ * h ξ‖
        = ‖OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ₀
                (SCV.translateSchwartz (- timeShiftVec d (s + s)) h)))‖ := by
            rw [hpair_eq]
    _ ≤ A * SchwartzMap.seminorm ℝ m m
          ((ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ₀
              (SCV.translateSchwartz (- timeShiftVec d (s + s)) h)) : ZeroDiagonalSchwartz d 2).1) := hgrowth
    _ = A * SchwartzMap.seminorm ℝ m m
          (twoPointDifferenceLift χ₀
            (SCV.translateSchwartz (- timeShiftVec d (s + s)) h)) := by
          rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
            (f := twoPointDifferenceLift χ₀
              (SCV.translateSchwartz (- timeShiftVec d (s + s)) h)) hvanish]
    _ ≤ A * ((C0 • semIdx.sup (schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ)) h) := by
          gcongr
          exact hsemi h
    _ = (A * C0) * (semIdx.sup (schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ)) h := by
          rw [Seminorm.smul_apply]
          simp [NNReal.smul_def, mul_assoc, mul_left_comm, mul_comm]

/-- The same positive-time CLM seminorm control, stated directly for the common
zero-center shifted section used in the live frontier.

Under diff-block dependence, the zero-center section and the common lifted slice
agree pointwise, so the existing CLM estimate transfers without additional
analytic input. -/
theorem commonZeroCenterShiftSection_clm_bound_of_diffBlockDependence_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (s : ℝ) (hs : 0 < s)
    (χ₀ : SchwartzSpacetime d) (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1) :
    ∃ (C : ℝ) (semIdx : Finset (ℕ × ℕ)), 0 < C ∧
      ∀ (h : SchwartzSpacetime d),
        HasCompactSupport (h : SpacetimeDim d → ℂ) →
        tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} →
        ‖∫ ξ : SpacetimeDim d,
            k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)] : NPointDomain d 2) *
              h ξ‖ ≤
          C * (semIdx.sup (schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ)) h := by
  obtain ⟨C, semIdx, hC, hclm⟩ :=
    commonLiftedSlice_clm_bound_local
      OS lgc G hG_euclid hG_diff s hs χ₀ hχ₀
  refine ⟨C, semIdx, hC, ?_⟩
  intro h hh_compact hh_pos
  have hEq :
      ∫ ξ : SpacetimeDim d,
          k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)] : NPointDomain d 2) *
            h ξ =
        ∫ ξ : SpacetimeDim d,
          commonLiftedDifferenceSliceKernel_local (d := d) G s ξ * h ξ := by
    refine integral_congr_ae ?_
    filter_upwards with ξ
    rw [← commonLiftedDifferenceSliceKernel_eq_k2TimeParametricKernel_on_zeroCenterShift_of_diffBlockDependence_local
      (d := d) G hG_diff s ξ]
  rw [hEq]
  exact hclm h hh_compact hh_pos

/-- The strengthened upstream translation-invariant `ACR(1)` witness already
comes with the direct positive-time CLM seminorm package on the zero-center
section.

This keeps the direct analytic fallback honest at the actual common-witness
surface used by the corrected Input A route. -/
theorem exists_commonZeroCenterShiftSection_clm_bound_of_translationInvariant_acrOne_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s : ℝ) (hs : 0 < s)
    (χ₀ : SchwartzSpacetime d) (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      (∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
        G u = G v) ∧
      ∃ (C : ℝ) (semIdx : Finset (ℕ × ℕ)), 0 < C ∧
        ∀ (h : SchwartzSpacetime d),
          HasCompactSupport (h : SpacetimeDim d → ℂ) →
          tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} →
          ‖∫ ξ : SpacetimeDim d,
              k2TimeParametricKernel (d := d) G
                (![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)] : NPointDomain d 2) *
                h ξ‖ ≤
            C * (semIdx.sup (schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ)) h := by
  obtain ⟨G, hG_holo, hG_euclid, hG_diff⟩ :=
    schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_local
      OS lgc
  obtain ⟨C, semIdx, hC, hclm⟩ :=
    commonZeroCenterShiftSection_clm_bound_of_diffBlockDependence_local
      OS lgc G hG_euclid hG_diff s hs χ₀ hχ₀
  exact ⟨G, hG_holo, hG_euclid, hG_diff, C, semIdx, hC, hclm⟩

end CLMBound

end OSReconstruction
