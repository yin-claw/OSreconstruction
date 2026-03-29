/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Support
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputA
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAInvariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAKernelReduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAFixedTime
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAFixedTimeInvariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAHdescReduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAHeadBlockTransport
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAOneVariableUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAShiftedRepresentative
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAWitness
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.DCT

/-!
# OS to Wightman `k = 2` VI.1 Frontier

This file now contains only the surviving OS II Section VI.1 `k = 2` frontier:
the direct descended-shell convergence seam behind the probe limit and the
final distributional assembly theorem.

All proved support infrastructure has been moved to `K2VI1/Support.lean` so that the hard `sorry`s stay on a small, readable theorem surface.
-/

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal
open BigOperators Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

variable {d : ℕ} [NeZero d]

private theorem exists_probeSeq_euclid_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∀ n (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f =
        ∫ x : NPointDomain d 2,
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
            (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x) := by
  /-
  Honest root Input A seam on the probe side:

  prove Euclidean reproduction for each probe witness on all zero-diagonal
  tests. Once this is available, the product-shell identity, fixed-center shell
  identity, and fixed-strip common-functional route are all formal from the
  current production support.
  -/
  sorry

private theorem exists_shifted_realDifference_productShell_to_same_center_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (t : ℝ)
    (_ht : 0 < t)
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (hKpkg : ∀ n,
      ∃ (C_bd : ℝ) (N : ℕ), 0 < C_bd ∧
        AEStronglyMeasurable
          (fun z : NPointDomain d 2 =>
            k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t))
          volume ∧
        (∀ᵐ z : NPointDomain d 2 ∂volume,
          ‖k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t)‖ ≤
            C_bd * (1 + ‖z‖) ^ N)) :
    ∀ n,
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          ((φ_seq n) (z 0) *
            (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (φ_seq n))) (z 1)) := by
  /-
  Honest shifted-representative shell seam:

  because the explicit shifted real-difference representative depends only on
  the difference variable, it should pair equally with the reflected product
  shell and with its descended same-center representative.
  -/
  intro n
  rcases hKpkg n with ⟨C_bd, N, hC, hK_meas, hK_bound⟩
  exact
    OSReconstruction.shifted_realDifferenceKernel_productShell_to_same_center_of_package_local
      (d := d) (μ := μ_seq n) (t := t) hK_meas C_bd N hC hK_bound
      (φ_seq n) (hφ_int n) (reflectedSchwartzSpacetime (d := d) (φ_seq n))

private theorem exists_fixed_strip_common_difference_kernel_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (s : ℝ)
    (hs : 0 < s) :
    ∃ K_s : SpacetimeDim d → ℂ,
      ContinuousOn K_s {ξ : SpacetimeDim d | -(s + s) < ξ 0} ∧
      (∀ n,
        let xφ : OSHilbertSpace OS :=
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                  (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                    (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
              OSHilbertSpace OS))
      osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ) =
          ∫ x : NPointDomain d 2,
            OSReconstruction.twoPointDifferenceKernel K_s x *
              (twoPointDifferenceLift χ₀
                (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                  (reflectedSchwartzSpacetime (φ_seq n))) x)) := by
  have hprobe_euclid :=
    exists_probeSeq_euclid_local
      (d := d) OS lgc φ_seq hφ_real hφ_int hφ_compact hφ_neg
  obtain ⟨μ_seq_pkg, _hμfin_pkg, hrepr_pkg, hKpkg⟩ :=
    OSReconstruction.exists_probeSeq_fixedTimeCenterDiffKernel_eq_and_shifted_realDifference_package_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  obtain ⟨μ_seq_cont, _hμfin_cont, hrepr_cont, hcont_cont⟩ :=
    OSReconstruction.exists_probeSeq_fixedTimeCenterDiff_with_shifted_realDifference_continuous_package_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  obtain ⟨χc_seq, _hχc_nonneg, _hχc_real, hχc_int, _hχc_compact, _hχc_neg, _hχc_ball⟩ :=
    exists_negative_approx_identity_sequence (d := d)
  let χc : SchwartzSpacetime d := χc_seq 0
  let I : ℕ → ℂ := fun n =>
    let xφ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
          OSHilbertSpace OS))
    osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ)
  have htime : (((s + s) : ℂ) * Complex.I) = ((↑s + ↑s) * Complex.I) := by
    ring
  have hprobe_fixed_center_eq_of_repr :
      ∀ m (μ : Measure (ℝ × (Fin d → ℝ)))
        (hreprm : ∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq m) (hφ_compact m) (hφ_neg m))
            ((((s + s) : ℂ) * Complex.I)) z =
          k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d (s + s))),
      ∀ h : SchwartzSpacetime d,
        tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} →
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) μ (ξ + timeShiftVec d (s + s)) * h ξ =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χc
              (SCV.translateSchwartz (- timeShiftVec d (s + s)) h))) := by
    intro m μ hreprm h hh_pos
    let Kt : SpacetimeDim d → ℂ :=
      fun ξ => k2DifferenceKernel_real_local (d := d) μ (ξ + timeShiftVec d (s + s))
    calc
      ∫ ξ : SpacetimeDim d, Kt ξ * h ξ
        = (∫ u : SpacetimeDim d, χc u) * ∫ ξ : SpacetimeDim d, Kt ξ * h ξ := by
            rw [hχc_int 0]
            ring
      _ =
        ∫ z : NPointDomain d 2,
          Kt (z 1) * (χc (z 0) * h (z 1)) := by
            symm
            exact OSReconstruction.integral_centerDiff_differenceOnly_kernel_factorizes
              (d := d) Kt χc h
      _ =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq m) (hφ_compact m) (hφ_neg m))
            ((((s + s) : ℂ) * Complex.I)) z *
            (χc (z 0) * h (z 1)) := by
              refine integral_congr_ae ?_
              filter_upwards with z
              by_cases hz : h (z 1) = 0
              · simp [Kt, hz]
              · have hz_mem : z 1 ∈ tsupport (h : SpacetimeDim d → ℂ) :=
                  subset_tsupport _ (Function.mem_support.mpr hz)
                have hz_pos : 0 < z 1 0 := hh_pos hz_mem
                have hz_strip : -(s + s) < z 1 0 := by
                  have hneg : -(s + s) < 0 := by linarith
                  exact lt_trans hneg hz_pos
                rw [show Kt (z 1) =
                    OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
                      (d := d)
                      (k2ProbeWitness_local (d := d) OS lgc
                        (φ_seq m) (hφ_compact m) (hφ_neg m))
                      ((((s + s) : ℂ) * Complex.I)) z by
                      symm
                      exact hreprm z hz_strip]
      _ =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χc
              (SCV.translateSchwartz (- timeShiftVec d (s + s)) h))) := by
              simpa [htime] using
                OSReconstruction.fixedTimeCenterDiffKernel_fixed_center_pairing_eq_schwinger_timeShift_local
                  (d := d) OS
                  (k2ProbeWitness_local (d := d) OS lgc
                    (φ_seq m) (hφ_compact m) (hφ_neg m))
                  (hprobe_euclid m) χc h hh_pos (s + s) (add_pos hs hs)
  have hpair_eq_pkg_cont :
      ∀ n (h : SchwartzSpacetime d),
        tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} →
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) * h ξ =
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) (μ_seq_cont 0) (ξ + timeShiftVec d (s + s)) * h ξ := by
    intro n h hh_pos
    exact
      (hprobe_fixed_center_eq_of_repr n (μ_seq_pkg n)
        (fun z hz => by simpa [htime] using hrepr_pkg n (s + s) z (add_pos hs hs) hz)
        h hh_pos).trans <|
      (hprobe_fixed_center_eq_of_repr 0 (μ_seq_cont 0)
        (fun z hz => by simpa [htime] using hrepr_cont 0 (s + s) z (add_pos hs hs) hz)
        h hh_pos).symm
  have hpair_prod_probe : ∀ n,
      I n =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
    intro n
    simpa [I] using
      OSReconstruction.fixedTimeCenterDiff_productShell_pairing_eq_matrixElement_of_euclid_local
        (d := d) OS lgc
        (k2ProbeWitness_local (d := d) OS lgc
          (φ_seq n) (hφ_compact n) (hφ_neg n))
        (hprobe_euclid n) (φ_seq n) (hφ_real n) (hφ_compact n) (hφ_neg n)
        (s + s) (add_pos hs hs)
  have hfactor :
      ∀ n,
        I n =
          ∫ ξ : SpacetimeDim d,
            k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) *
              (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) ξ := by
    intro n
    let hdesc_n : SchwartzSpacetime d :=
      OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
        (reflectedSchwartzSpacetime (d := d) (φ_seq n))
    have hprobe_shifted_prod :
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (z 1 + timeShiftVec d (s + s)) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
      refine integral_congr_ae ?_
      filter_upwards with z
      by_cases hz :
          (φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1) = 0
      · rw [hz]
        simp
      · have hz0_neg : z 0 0 < 0 := by
          exact hφ_neg n <|
            subset_tsupport _ (Function.mem_support.mpr (left_ne_zero_of_mul hz))
        have hzsum_pos : 0 < (z 0 + z 1) 0 := by
          exact reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n) <|
            subset_tsupport _ (Function.mem_support.mpr (right_ne_zero_of_mul hz))
        have hzsum : (z 0 + z 1) 0 = z 0 0 + z 1 0 := by simp
        rw [hzsum] at hzsum_pos
        have hz1_pos : 0 < z 1 0 := by
          linarith
        have hz_strip : -(s + s) < z 1 0 := by
          have hneg : -(s + s) < 0 := by linarith
          exact lt_trans hneg hz1_pos
        rw [show OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
              (d := d)
              (k2ProbeWitness_local (d := d) OS lgc
                (φ_seq n) (hφ_compact n) (hφ_neg n))
              ((((s + s) : ℂ) * Complex.I)) z =
              k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n)
                (z 1 + timeShiftVec d (s + s)) by
              simpa [htime] using hrepr_pkg n (s + s) z (add_pos hs hs) hz_strip]
    have hshifted_prod_to_same_center :
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (z 1 + timeShiftVec d (s + s)) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (z 1 + timeShiftVec d (s + s)) *
            ((φ_seq n) (z 0) * hdesc_n (z 1)) := by
      simpa [hdesc_n] using
        exists_shifted_realDifference_productShell_to_same_center_local
          (d := d) φ_seq hφ_int (s + s) (add_pos hs hs) μ_seq_pkg
          (fun m => by
            rcases hKpkg m (s + s) with ⟨C', N', hC', hK_meas', hK_bound'⟩
            exact ⟨C', N', hC', hK_meas', hK_bound'⟩) n
    calc
      I n =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := hpair_prod_probe n
      _ =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (z 1 + timeShiftVec d (s + s)) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := hprobe_shifted_prod
      _ =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (z 1 + timeShiftVec d (s + s)) *
            ((φ_seq n) (z 0) * hdesc_n (z 1)) := hshifted_prod_to_same_center
      _ = (∫ u : SpacetimeDim d, φ_seq n u) *
            ∫ ξ : SpacetimeDim d,
              k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) *
                hdesc_n ξ := by
              exact OSReconstruction.integral_centerDiff_differenceOnly_kernel_factorizes
                (d := d)
                (fun ξ : SpacetimeDim d =>
                  k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n)
                    (ξ + timeShiftVec d (s + s)))
                (φ_seq n) hdesc_n
      _ =
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) *
            hdesc_n ξ := by
              rw [hφ_int n]
              ring
  have hK0_strip :
      ContinuousOn
        (fun ξ : SpacetimeDim d =>
          k2DifferenceKernel_real_local (d := d) (μ_seq_cont 0) (ξ + timeShiftVec d (s + s)))
        {ξ : SpacetimeDim d | -(s + s) < ξ 0} := by
    let emb : SpacetimeDim d → NPointDomain d 2 := fun ξ => ![(0 : SpacetimeDim d), ξ]
    have hemb : Continuous emb := by
      refine continuous_pi ?_
      intro i
      fin_cases i
      · simpa [emb] using
          (continuous_const : Continuous fun _ : SpacetimeDim d => (0 : SpacetimeDim d))
      · simpa [emb] using (continuous_id : Continuous fun ξ : SpacetimeDim d => ξ)
    have hmaps :
        Set.MapsTo emb
          {ξ : SpacetimeDim d | -(s + s) < ξ 0}
          {z : NPointDomain d 2 | -(s + s) < z 1 0} := by
      intro ξ hξ
      simpa [emb] using hξ
    refine ((hcont_cont 0 (s + s) (add_pos hs hs)).comp hemb.continuousOn hmaps).congr ?_
    intro ξ hξ
    simp [emb]
  let K_s : SpacetimeDim d → ℂ := fun ξ =>
    k2DifferenceKernel_real_local (d := d) (μ_seq_cont 0) (ξ + timeShiftVec d (s + s))
  refine ⟨K_s, hK0_strip, ?_⟩
  intro n
  let hdesc_n : SchwartzSpacetime d :=
    OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
      (reflectedSchwartzSpacetime (d := d) (φ_seq n))
  have hdesc_pos :
      tsupport (hdesc_n : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
    dsimp [hdesc_n]
    exact OSReconstruction.twoPointCenterShearDescent_reflected_tsupport_pos_local
      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)
  have hsame :
      ∫ ξ : SpacetimeDim d,
        k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) *
          hdesc_n ξ =
      ∫ ξ : SpacetimeDim d,
        K_s ξ * hdesc_n ξ := by
    exact hpair_eq_pkg_cont n hdesc_n hdesc_pos
  calc
    I n =
      ∫ ξ : SpacetimeDim d,
        k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) *
          hdesc_n ξ := hfactor n
    _ = ∫ ξ : SpacetimeDim d, K_s ξ * hdesc_n ξ := hsame
    _ = (∫ u : SpacetimeDim d, χ₀ u) *
          ∫ ξ : SpacetimeDim d, K_s ξ * hdesc_n ξ := by
            rw [hχ₀]
            ring
    _ =
      ∫ x : NPointDomain d 2,
        OSReconstruction.twoPointDifferenceKernel K_s x *
          (twoPointDifferenceLift χ₀ hdesc_n x) := by
            symm
            exact OSReconstruction.integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
              (d := d) K_s χ₀ hdesc_n

private theorem exists_fixed_strip_diagonal_limit_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (s : ℝ)
    (hs : 0 < s) :
    ∃ z : ℂ,
      Filter.Tendsto
        (fun n =>
          let xφ : OSHilbertSpace OS :=
            (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single 1
                    (SchwartzNPoint.osConj (d := d) (n := 1)
                      (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                    (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
                OSHilbertSpace OS))
          osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ))
        Filter.atTop
        (nhds z) := by
  obtain ⟨K_s, hK_strip, hpair⟩ :=
    exists_fixed_strip_common_difference_kernel_local
      OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg s hs
  simpa using
    OSReconstruction.exists_fixed_strip_diagonal_limit_of_difference_kernel_pairing_on_fixedStrip_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int
      hφ_compact hφ_neg hφ_ball s hs K_s hK_strip hpair

private theorem exists_shell_pointwise_limit_function_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ g : SpacetimeDim d → ℂ,
      (∀ᵐ ξ : SpacetimeDim d ∂volume,
        Filter.Tendsto
          (fun n =>
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ))
          Filter.atTop
          (nhds (g ξ * ((h : SchwartzSpacetime d) ξ)))) ∧
      ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h =
        ∫ ξ : SpacetimeDim d, g ξ * ((h : SchwartzSpacetime d) ξ)) := by
  /-
  Genuine remaining Input B:

  identify the pointwise almost-everywhere shell limit and the corresponding
  target integral. The intended direct OS route is again a descended-center
  approximate-identity argument on the positive-time shell, using the orbit
  continuity layer from `K2VI1/OrbitBridge.lean`.
  -/
  sorry

private theorem k2Probe_pairing_fixed_normalized_center_tendsto_schwingerDifferencePositive_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hpair : ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
      ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
          twoPointDifferenceLift χ (h : SchwartzSpacetime d) x =
        (∫ u : SpacetimeDim d, χ u) *
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ)) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      Filter.Tendsto
        (fun n =>
          ∫ x : NPointDomain d 2,
            k2TimeParametricKernel (d := d)
                (k2ProbeWitness_local (d := d) OS lgc
                  (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
              twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x)
        Filter.atTop
        (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h)) := by
  intro h
  obtain ⟨ε, hε_pos, hmargin0⟩ :=
    exists_positive_time_margin_of_mem_positiveTimeCompactSupport_local (d := d) h
  have hs : 0 < ε / 4 := by linarith
  have hmargin :
      tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | ε / 4 + ε / 4 < ξ 0} := by
    refine Set.Subset.trans hmargin0 ?_
    intro ξ hξ
    simp only [Set.mem_setOf] at hξ ⊢
    linarith
  obtain ⟨z, hdiag⟩ :=
    exists_fixed_strip_diagonal_limit_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int
      hφ_compact hφ_neg hφ_ball (ε / 4) hs
  obtain ⟨g, hpointwise, htarget⟩ :=
    exists_shell_pointwise_limit_function_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
      hφ_ball h
  have hshell :
      Filter.Tendsto
        (fun n =>
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ))
        Filter.atTop
        (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h)) :=
    OSReconstruction.translatedProductShell_boundary_tendsto_of_tendsto_damped_diagonal_and_ae_pointwise_vi1DCT_local
      (d := d) OS lgc χ₀ φ_seq hφ_real hφ_compact hφ_neg h (ε / 4) hs
      hmargin g hdiag hpointwise htarget
  refine Filter.Tendsto.congr' ?_ hshell
  filter_upwards with n
  simpa [hχ₀, one_mul] using (hpair n χ₀ h).symm

private theorem k2DifferenceKernel_real_pairing_tendsto_schwingerDifferencePositive_of_negativeApproxIdentity_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (_hμfin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hsupp : ∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμrepr : ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n))
    (hpair : ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
      ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
          twoPointDifferenceLift χ (h : SchwartzSpacetime d) x =
        (∫ u : SpacetimeDim d, χ u) *
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ)) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      Filter.Tendsto
        (fun n =>
          ∫ ξ : SpacetimeDim d,
            k2DifferenceKernel_real_local (μ_seq n) ξ *
              (h : SchwartzSpacetime d) ξ)
        Filter.atTop
        (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h)) := by
  intro h
  have hpair_fixed :
      ∀ n,
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (μ_seq n) ξ *
            (h : SchwartzSpacetime d) ξ =
          ∫ x : NPointDomain d 2,
            k2TimeParametricKernel (d := d)
                (k2ProbeWitness_local (d := d) OS lgc
                  (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
              twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x := by
    intro n
    exact integral_k2DifferenceKernel_real_eq_probe_pairing_fixed_normalized_center_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_int hφ_ball hφ_real hφ_compact
      hφ_neg μ_seq _hμfin hsupp hμrepr hpair n h
  simpa [hpair_fixed] using
    k2Probe_pairing_fixed_normalized_center_tendsto_schwingerDifferencePositive_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
      hφ_ball hpair h

private theorem translatedProductShell_boundary_tendsto_schwingerDifferencePositive_of_negativeApproxIdentity_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (_hμfin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hsupp : ∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμrepr : ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n))
    (hpair : ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
      ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
          twoPointDifferenceLift χ (h : SchwartzSpacetime d) x =
        (∫ u : SpacetimeDim d, χ u) *
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ)) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      Filter.Tendsto
        (fun n =>
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ))
        Filter.atTop
        (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h)) := by
  intro h
  have hred :=
    k2DifferenceKernel_real_pairing_tendsto_schwingerDifferencePositive_of_negativeApproxIdentity_local
      OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
      hφ_ball μ_seq _hμfin hsupp hμrepr hpair h
  refine Filter.Tendsto.congr' ?_ hred
  filter_upwards with n
  exact
    integral_translatedProductShell_boundary_eq_reduced_differenceKernel_pairing_of_negativeApproxIdentity_local
      OS lgc φ_seq hφ_real hφ_compact hφ_neg μ_seq _hμfin hsupp hμrepr n h |>.symm

/-- Route-independent final payoff: once an honest Euclidean two-point kernel
has the correct sector formulas, measurable polynomial bounds, and agreement
with `OS.S 2` on the flat-origin difference-shell generators, reproduction on
all of `ZeroDiagonalSchwartz d 2` is purely formal. This packages the last
non-VI.1 bookkeeping step so the remaining assembly theorem only has to produce
the limiting witness/kernel data. -/
private theorem k2_distributional_reproduction_of_flatOrigin_shell_agreement_local
    (OS : OsterwalderSchraderAxioms d)
    (K : NPointDomain d 2 → ℂ)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hShell :
      ∀ (χ h : SchwartzSpacetime d)
        (hzero : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0),
        OSReconstruction.twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
            (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)))
    (f : ZeroDiagonalSchwartz d 2) :
    OS.S 2 f = ∫ x : NPointDomain d 2, K x * (f.1 x) := by
  have hCLM :
      OSReconstruction.twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound =
        OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2 :=
    zeroDiagKernelCLM_eq_schwinger_of_flatOrigin_differenceShell_agreement
      (d := d) OS K hK_meas C_bd N hC hK_bound hShell
  have happly :=
    congrArg (fun L : ZeroDiagonalSchwartz d 2 →L[ℂ] ℂ => L f) hCLM
  simpa [OSReconstruction.twoPointZeroDiagonalKernelCLM_apply] using happly.symm

private theorem exists_k2_timeParametric_distributional_assembly
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ) (K : NPointDomain d 2 → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ x : NPointDomain d 2, x 0 0 < x 1 0 →
        K x = k2TimeParametricKernel (d := d) G x) ∧
      (∀ x : NPointDomain d 2, x 1 0 < x 0 0 →
        K x = k2TimeParametricKernel (d := d) G
          (fun i => x ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) i))) ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2, K x * (f.1 x)) := by
  /-
  Honest remaining assembly step after the VI.1 refactor:

  * obtain the shrinking negative approximate-identity sequence and its
    per-probe shell package from `exists_k2_VI1_regularization_input_local`;
  * use
    `translatedProductShell_boundary_tendsto_schwingerDifferencePositive_of_negativeApproxIdentity_local`
    to identify the reduced boundary functional on the positive-time edge;
  * choose the resulting honest Euclidean kernel/witness pair `(G, K)` coming
    from the OS II VI.1 limit construction, not from a single fixed probe;
  * discharge the final reproduction clause through
    `k2_distributional_reproduction_of_flatOrigin_shell_agreement_local`.
  -/
  sorry

/-- The `k = 2` time-parametric base step on the honest OS route.

The previous kernel / difference-lift transport chain has been removed from the
critical path. The remaining gap is now exactly the OS-faithful semigroup /
distributional assembly theorem. -/
theorem schwinger_continuation_base_step_timeParametric_k2
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ) (K : NPointDomain d 2 → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ x : NPointDomain d 2, x 0 0 < x 1 0 →
        K x = k2TimeParametricKernel (d := d) G x) ∧
      (∀ x : NPointDomain d 2, x 1 0 < x 0 0 →
        K x = k2TimeParametricKernel (d := d) G
          (fun i => x ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) i))) ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2, K x * (f.1 x)) := by
  exact exists_k2_timeParametric_distributional_assembly OS lgc

end
