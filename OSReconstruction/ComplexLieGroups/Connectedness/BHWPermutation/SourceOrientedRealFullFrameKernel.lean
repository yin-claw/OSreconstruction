import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRealFullFrameChart

/-!
# Real-compatible full-frame kernel map

This file keeps the real-compatible full-frame implicit-kernel derivative
support separate from the chart packaging file.  The key point is that the
kernel coordinate used for the real route is based on the explicit
determinant-direction projection, not on the arbitrary closed-complement
projection used by the generic complex local-image chart.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 500000 in
/-- The explicit real-compatible kernel-coordinate map has the same strict
derivative as the generic implicit-kernel map. -/
theorem sourceFullFrameRealCompatibleExplicitKernelMap_hasStrictFDerivAt
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    HasStrictFDerivAt
      (sourceFullFrameRealCompatibleExplicitKernelMap d hM0R)
      (sourceFullFrameGaugeSliceKernelDerivCLM d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R))) 0 := by
  let hM0C := sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
  let S := sourceFullFrameExplicitGaugeSliceData d hM0C
  let M0 := M0R.map Complex.ofReal
  let Fsym := sourceFullFrameGaugeSliceMapSymmetric d M0 S
  let H0S := sourceFullFrameSymmetricBase d M0
  let P := sourceFullFrameRealCompatibleKernelProjection d hM0R
  have hF : HasStrictFDerivAt Fsym
      (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S) 0 := by
    simpa [Fsym, M0, S, hM0C] using
      sourceFullFrameGaugeSliceMapSymmetric_hasStrictFDerivAt d hM0C S
  have hsub : HasStrictFDerivAt (fun X : S.slice => Fsym X - H0S)
      (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S) 0 := by
    exact hF.sub_const H0S
  have hP : HasStrictFDerivAt
      (P : sourceFullFrameSymmetricCoordSubmodule d →
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker)
      P (Fsym 0 - H0S) :=
    @ContinuousLinearMap.hasStrictFDerivAt ℂ _
      (sourceFullFrameSymmetricCoordSubmodule d) _ _ _
      ((sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker)
      _ _ _
      P (x := Fsym 0 - H0S)
  have hcomp : HasStrictFDerivAt
      (fun X : S.slice => P (Fsym X - H0S))
      (P.comp (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S)) 0 := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := (0 : S.slice))
        (g := (P : sourceFullFrameSymmetricCoordSubmodule d →
          (sourceFullFrameSymmetricEquationDerivCLM d
            (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker))
        (f := fun X : S.slice => Fsym X - H0S) hP hsub)
  have hclm : P.comp (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S) =
      sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S := by
    apply ContinuousLinearMap.ext
    intro X
    have hp := sourceFullFrameRealCompatibleKernelProjection_apply_ker d hM0R
      (sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S X)
    simpa [P, sourceFullFrameGaugeSliceKernelDerivCLM] using hp
  have hcomp' : HasStrictFDerivAt
      (fun X : S.slice => P (Fsym X - H0S))
      (sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S) 0 :=
    hcomp.congr_fderiv hclm
  refine hcomp'.congr_of_eventuallyEq ?_
  filter_upwards with X
  simp [sourceFullFrameRealCompatibleExplicitKernelMap, P, Fsym, H0S, S, M0]

/-- The explicit real-compatible kernel map written in the finite coordinates
of the checked real-form slice. -/
noncomputable def sourceFullFrameRealCompatibleNormalizedKernelMap
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (Fin F.realModelDim → ℂ) → (Fin F.realModelDim → ℂ) :=
  fun q =>
    (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm
      (sourceFullFrameRealCompatibleExplicitKernelMap d hM0R
        (F.complexCoordEquiv q))

set_option synthInstance.maxHeartbeats 100000 in
@[simp]
theorem sourceFullFrameRealCompatibleNormalizedKernelMap_zero
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F 0 = 0 := by
  simp [sourceFullFrameRealCompatibleNormalizedKernelMap,
    sourceFullFrameRealSliceKernelCoordEquiv]

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 500000 in
/-- The explicit real-compatible normalized kernel map has identity strict
derivative at the origin. -/
theorem sourceFullFrameRealCompatibleNormalizedKernelMap_hasStrictFDerivAt
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    HasStrictFDerivAt
      (sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F)
      (1 : (Fin F.realModelDim → ℂ) →L[ℂ] (Fin F.realModelDim → ℂ)) 0 := by
  let hM0C := sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
  let S := sourceFullFrameExplicitGaugeSliceData d hM0C
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker
  let E := sourceFullFrameRealSliceKernelCoordEquiv d hM0R F
  let Es : K →L[ℂ] (Fin F.realModelDim → ℂ) := E.symm
  let f := sourceFullFrameRealCompatibleExplicitKernelMap d hM0R
  let c : (Fin F.realModelDim → ℂ) →L[ℂ] S.slice := F.complexCoordEquiv
  let e : S.slice ≃L[ℂ] K :=
    sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv d hM0C S
  have hf : HasStrictFDerivAt f (e : S.slice →L[ℂ] K) 0 := by
    rw [sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv_coe]
    exact sourceFullFrameRealCompatibleExplicitKernelMap_hasStrictFDerivAt
      d hM0R
  have hc : HasStrictFDerivAt (fun q : Fin F.realModelDim → ℂ => c q) c
      (0 : Fin F.realModelDim → ℂ) :=
    c.hasStrictFDerivAt
  have hc0 : c (0 : Fin F.realModelDim → ℂ) = 0 := by
    simp [c]
  have hf0 : HasStrictFDerivAt f (e : S.slice →L[ℂ] K)
      (c (0 : Fin F.realModelDim → ℂ)) := by
    simpa [hc0] using hf
  have hfc : HasStrictFDerivAt (fun q : Fin F.realModelDim → ℂ => f (c q))
      ((e : S.slice →L[ℂ] K).comp c) (0 : Fin F.realModelDim → ℂ) := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := (0 : Fin F.realModelDim → ℂ))
        (g := f) (f := fun q : Fin F.realModelDim → ℂ => c q) hf0 hc)
  have hsymm : HasStrictFDerivAt
      (Es : K → (Fin F.realModelDim → ℂ)) Es (0 : K) :=
    ContinuousLinearMap.hasStrictFDerivAt Es (x := (0 : K))
  have hf_zero : f 0 = 0 := by
    simp [f]
  have hf_c0 : f (c (0 : Fin F.realModelDim → ℂ)) = 0 := by
    rw [hc0]
    exact hf_zero
  have hsymm0 : HasStrictFDerivAt
      (Es : K → (Fin F.realModelDim → ℂ)) Es
      (f (c (0 : Fin F.realModelDim → ℂ))) := by
    rw [hf_c0]
    exact hsymm
  have hcomp : HasStrictFDerivAt
      (fun q : Fin F.realModelDim → ℂ => E.symm (f (c q)))
      (Es.comp ((e : S.slice →L[ℂ] K).comp c)) (0 : Fin F.realModelDim → ℂ) := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := (0 : Fin F.realModelDim → ℂ))
        (g := (Es : K → (Fin F.realModelDim → ℂ)))
        (f := fun q : Fin F.realModelDim → ℂ => f (c q)) hsymm0 hfc)
  have hfun :
      (fun q : Fin F.realModelDim → ℂ => E.symm (f (c q))) =
        sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F := by
    funext q
    rfl
  have hderiv :
      Es.comp ((e : S.slice →L[ℂ] K).comp c) =
        (1 : (Fin F.realModelDim → ℂ) →L[ℂ] (Fin F.realModelDim → ℂ)) := by
    apply ContinuousLinearMap.ext
    intro q
    change Es (e (c q)) = q
    rw [show Es (e (c q)) =
        F.complexCoordEquiv.symm (e.symm (e (F.complexCoordEquiv q))) by
      rfl]
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ContinuousLinearEquiv.symm_apply_apply F.complexCoordEquiv q
  simpa [hfun, hderiv] using hcomp

set_option synthInstance.maxHeartbeats 100000 in
/-- The restricted symmetric equation derivative has real value on
componentwise complexified real symmetric coordinates at a complexified real
full-frame base. -/
theorem sourceFullFrameSymmetricEquationDerivCLM_realComplexify_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (Y : SourceFullFrameRealOrientedCoord d)
    (hYsym : ∀ a b : Fin (d + 1), Y.1 a b = Y.1 b a) :
    Complex.im (sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))
      ⟨sourceFullFrameRealOrientedCoordComplexify d Y, by
        intro a b
        change (Y.1 a b : ℂ) = (Y.1 b a : ℂ)
        exact_mod_cast hYsym a b⟩) = 0 := by
  have hGramUnit :
      IsUnit
        (Matrix.of
          (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal)).gram).det := by
    simpa [sourceFullFrameOrientedGram] using
      sourceFullFrameGram_det_isUnit_of_frame_det_isUnit
        (d := d) (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
  have hf0 :=
    (sourceFullFrameOrientedEquation_hasFDerivAt_trace (d := d)
      (H0 := sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))
      hGramUnit).fderiv
  have hf :
      fderiv ℂ (sourceFullFrameOrientedEquation d)
        (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal)) =
      sourceFullFrameOrientedEquationDerivCLM d
        (sourceFullFrameOrientedGram d (M0R.map Complex.ofReal)) := by
    simpa [sourceFullFrameOrientedGramCoord] using hf0
  change Complex.im
      (((fderiv ℂ (sourceFullFrameOrientedEquation d)
        (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).comp
          (sourceFullFrameSymmetricCoordSubmodule d).subtypeL)
        ⟨sourceFullFrameRealOrientedCoordComplexify d Y, by
          intro a b
          change (Y.1 a b : ℂ) = (Y.1 b a : ℂ)
          exact_mod_cast hYsym a b⟩) = 0
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [hf]
  exact sourceFullFrameOrientedEquationDerivLinear_realComplexify_im d hM0R Y

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- The explicit determinant-direction projection preserves zero imaginary
parts in all symmetric full-frame coordinates. -/
theorem sourceFullFrameRealCompatibleKernelProjection_im_zero
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (H : sourceFullFrameSymmetricCoordSubmodule d)
    (hHgram : ∀ a b : Fin (d + 1),
      Complex.im ((H : SourceFullFrameOrientedCoord d).1 a b) = 0)
    (hHdet : Complex.im ((H : SourceFullFrameOrientedCoord d).2) = 0) :
    (∀ a b : Fin (d + 1),
      Complex.im ((((sourceFullFrameRealCompatibleKernelProjection d hM0R H :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 a b) = 0) ∧
      Complex.im ((((sourceFullFrameRealCompatibleKernelProjection d hM0R H :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2) = 0 := by
  let L := sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))
  let u := sourceFullFrameSymmetricDetDirection d
  have ha_im0 :
      ((sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal)))
        ⟨(0, 1), sourceFullFrameDetDirection_mem_symmetric d⟩).im = 0 := by
    simpa [sourceFullFrameSymmetricDetDirection, sourceFullFrameDetDirection] using
      sourceFullFrameRealCompatibleSymmetricDetDirection_scalar_im d M0R
  have hYsym :
      ∀ a b : Fin (d + 1),
        ((H : SourceFullFrameOrientedCoord d).1 a b).re =
          ((H : SourceFullFrameOrientedCoord d).1 b a).re := by
    intro a b
    exact congrArg Complex.re (H.property a b)
  let Y : SourceFullFrameRealOrientedCoord d :=
    (fun a b => ((H : SourceFullFrameOrientedCoord d).1 a b).re,
      ((H : SourceFullFrameOrientedCoord d).2).re)
  have hH_eq : H =
      ⟨sourceFullFrameRealOrientedCoordComplexify d Y, by
        intro a b
        change (((H : SourceFullFrameOrientedCoord d).1 a b).re : ℂ) =
          (((H : SourceFullFrameOrientedCoord d).1 b a).re : ℂ)
        exact_mod_cast hYsym a b⟩ := by
    apply Subtype.ext
    apply Prod.ext
    · funext a b
      apply Complex.ext
      · simp [Y, sourceFullFrameRealOrientedCoordComplexify]
      · simpa [Y, sourceFullFrameRealOrientedCoordComplexify] using hHgram a b
    · apply Complex.ext
      · simp [Y, sourceFullFrameRealOrientedCoordComplexify]
      · simpa [Y, sourceFullFrameRealOrientedCoordComplexify] using hHdet
  have hb_im0 : (L H).im = 0 := by
    rw [hH_eq]
    simpa [L, Y] using
      sourceFullFrameSymmetricEquationDerivCLM_realComplexify_im
        d hM0R Y hYsym
  constructor
  · intro i j
    change Complex.im (((H -
        (1 / (L u)) • (ContinuousLinearMap.smulRight L u) H :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 i j) = 0
    simp [u, sourceFullFrameSymmetricDetDirection,
      sourceFullFrameDetDirection, ContinuousLinearMap.smulRight_apply, L,
      hHgram]
  · change Complex.im (((H -
        (1 / (L u)) • (ContinuousLinearMap.smulRight L u) H :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2) = 0
    simp [u, sourceFullFrameSymmetricDetDirection,
      sourceFullFrameDetDirection, ContinuousLinearMap.smulRight_apply, L,
      hHdet, ha_im0, hb_im0]

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- On a complexified real slice input, the nonlinear gauge-slice symmetric
coordinate minus the complexified real base has zero imaginary parts. -/
theorem sourceFullFrameGaugeSliceMapSymmetric_realComplexify_sub_base_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (X : sourceFullFrameRealDifferentialRightInverseRange d hM0R) :
    (∀ a b : Fin (d + 1),
      Complex.im ((((sourceFullFrameGaugeSliceMapSymmetric d
        (M0R.map Complex.ofReal)
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R))
        ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R X.property⟩ -
        sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 a b)) = 0) ∧
      Complex.im ((((sourceFullFrameGaugeSliceMapSymmetric d
        (M0R.map Complex.ofReal)
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R))
        ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R X.property⟩ -
        sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2)) = 0 := by
  constructor
  · intro a b
    simp [sourceFullFrameGaugeSliceMapSymmetric,
      sourceFullFrameGaugeSliceMap, sourceFullFrameSymmetricBase,
      sourceFullFrameOrientedGramCoord, sourceFullFrameOrientedGram]
  · have hmap :
        M0R.map Complex.ofReal +
            ((X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal) =
          (M0R + (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)).map
            Complex.ofReal := by
      ext i j
      simp
    simp [sourceFullFrameGaugeSliceMapSymmetric,
      sourceFullFrameGaugeSliceMap, sourceFullFrameSymmetricBase,
      sourceFullFrameOrientedGramCoord, sourceFullFrameOrientedGram, hmap,
      sourceFullFrame_matrix_map_ofReal_det]

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- The explicit real-compatible kernel map has real-valued output on
componentwise complexified real slice inputs. -/
theorem sourceFullFrameRealCompatibleExplicitKernelMap_real_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (X : sourceFullFrameRealDifferentialRightInverseRange d hM0R) :
    (∀ a b : Fin (d + 1),
      Complex.im ((((sourceFullFrameRealCompatibleExplicitKernelMap d hM0R
        ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R X.property⟩ :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 a b) = 0) ∧
      Complex.im ((((sourceFullFrameRealCompatibleExplicitKernelMap d hM0R
        ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
          sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
            d hM0R X.property⟩ :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2) = 0 := by
  let S := sourceFullFrameExplicitGaugeSliceData d
      (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
  let XC : S.slice :=
    ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
      sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
        d hM0R X.property⟩
  let H : sourceFullFrameSymmetricCoordSubmodule d :=
    sourceFullFrameGaugeSliceMapSymmetric d (M0R.map Complex.ofReal) S XC -
      sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal)
  have hH :=
    sourceFullFrameGaugeSliceMapSymmetric_realComplexify_sub_base_im d hM0R X
  have hproj :=
    sourceFullFrameRealCompatibleKernelProjection_im_zero d hM0R H hH.1 hH.2
  simpa [sourceFullFrameRealCompatibleExplicitKernelMap, H, S, XC] using hproj

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- The kernel derivative equivalence sends complexified real slice vectors to
real-valued kernel coordinates. -/
theorem sourceFullFrameGaugeSliceKernelDerivCLM_realComplexify_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (X : sourceFullFrameRealDifferentialRightInverseRange d hM0R) :
    let hM0C := sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
    let S := sourceFullFrameExplicitGaugeSliceData d hM0C
    let XC : S.slice :=
      ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
        sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
          d hM0R X.property⟩
    (∀ a b : Fin (d + 1),
      Complex.im ((((sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S XC :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 a b) = 0) ∧
      Complex.im ((((sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S XC :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2) = 0 := by
  intro hM0C S XC
  rcases X.property with ⟨Y, hY⟩
  let YC := sourceFullFrameRealOrientedTangentComplexifyLinear d M0R Y
  have hXc :
      ((X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal) =
        sourceFullFrameOrientedDifferentialRightInverseLinear d hM0C YC := by
    rw [← hY]
    simpa [hM0C, YC, sourceFullFrameRealOrientedTangentComplexifyLinear] using
      sourceFullFrameRealDifferentialRightInverseLinear_complexify d hM0R Y
  have hdiff :
      sourceFullFrameOrientedDifferential d (M0R.map Complex.ofReal)
          ((X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal) =
        (YC : SourceFullFrameOrientedCoord d) := by
    rw [hXc]
    exact sourceFullFrameOrientedDifferential_rightInverse d hM0C YC
  constructor
  · intro a b
    change Complex.im
      ((sourceFullFrameOrientedDifferential d (M0R.map Complex.ofReal)
        ((X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map
          Complex.ofReal)).1 a b) = 0
    rw [hdiff]
    simp [YC, sourceFullFrameRealOrientedCoordComplexify]
  · change Complex.im
      (sourceFullFrameOrientedDifferential d (M0R.map Complex.ofReal)
        ((X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map
          Complex.ofReal)).2 = 0
    rw [hdiff]
    simp [YC, sourceFullFrameRealOrientedCoordComplexify]

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- The finite kernel-coordinate equivalence sends real finite coordinates to
real-valued kernel coordinates. -/
theorem sourceFullFrameRealSliceKernelCoordEquiv_real_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (q : Fin F.realModelDim → ℝ) :
    (∀ a b : Fin (d + 1),
      Complex.im (((((sourceFullFrameRealSliceKernelCoordEquiv d hM0R F)
        (fun i => (q i : ℂ)) :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 a b) = 0) ∧
      Complex.im (((((sourceFullFrameRealSliceKernelCoordEquiv d hM0R F)
        (fun i => (q i : ℂ)) :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
        sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2) = 0 := by
  let hM0C := sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
  let S := sourceFullFrameExplicitGaugeSliceData d hM0C
  let X : sourceFullFrameRealDifferentialRightInverseRange d hM0R :=
    F.realCoordEquiv q
  let XC : S.slice :=
    ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal,
      sourceFullFrameRealDifferentialRightInverseRange_complexify_mem_complexSlice
        d hM0R X.property⟩
  have hE :
      (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F)
        (fun i => (q i : ℂ)) =
      sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S XC := by
    rw [sourceFullFrameRealSliceKernelCoordEquiv]
    change (sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv d hM0C S)
        (F.complexCoordEquiv (fun i => (q i : ℂ))) = _
    rw [F.complexCoordEquiv_real_eq q]
    let K := (sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker
    have hcoe := congrArg (fun T : S.slice →L[ℂ] K => T XC)
      (sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv_coe d hM0C S)
    change
      ((sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv d hM0C S :
        S.slice →L[ℂ] K) XC) =
      (sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S) XC
    exact hcoe
  have him := sourceFullFrameGaugeSliceKernelDerivCLM_realComplexify_im d hM0R X
  simpa [hE, hM0C, S, XC, X] using him

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 500000 in
/-- If a kernel coordinate is real-valued, applying the inverse finite
kernel-coordinate equivalence gives a real-valued finite coordinate vector. -/
theorem sourceFullFrameRealSliceKernelCoordEquiv_symm_real_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (K : (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker)
    (hKgram : ∀ a b : Fin (d + 1),
      Complex.im (((K : sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).1 a b) = 0)
    (hKdet : Complex.im (((K : sourceFullFrameSymmetricCoordSubmodule d) :
        SourceFullFrameOrientedCoord d).2) = 0) :
    ∀ i : Fin F.realModelDim,
      Complex.im (((sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm K)
        i) = 0 := by
  let E := sourceFullFrameRealSliceKernelCoordEquiv d hM0R F
  let q : Fin F.realModelDim → ℂ := E.symm K
  let qR : Fin F.realModelDim → ℝ := fun i => (q i).re
  let qI : Fin F.realModelDim → ℝ := fun i => (q i).im
  let KR := E (fun i => (qR i : ℂ))
  let KI := E (fun i => (qI i : ℂ))
  have hKRim := sourceFullFrameRealSliceKernelCoordEquiv_real_im d hM0R F qR
  have hKIim := sourceFullFrameRealSliceKernelCoordEquiv_real_im d hM0R F qI
  have hqsplit :
      q = (fun i => (qR i : ℂ)) +
        Complex.I • (fun i => (qI i : ℂ)) := by
    ext i
    simp [qR, qI, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im (q i)).symm
  have hKsplit : K = KR + Complex.I • KI := by
    calc
      K = E q := (E.apply_symm_apply K).symm
      _ = E ((fun i => (qR i : ℂ)) +
            Complex.I • (fun i => (qI i : ℂ))) := by
        rw [hqsplit]
      _ = E (fun i => (qR i : ℂ)) +
            E (Complex.I • (fun i => (qI i : ℂ))) := by
        rw [map_add]
      _ = KR + Complex.I • KI := by
        rw [map_smul]
  have hKI_zero : KI = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · funext a b
      have hentry := congrArg
        (fun T : (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker =>
          (((T : sourceFullFrameSymmetricCoordSubmodule d) :
            SourceFullFrameOrientedCoord d).1 a b)) hKsplit
      have him := congrArg Complex.im hentry
      have himKR : Complex.im (((KR : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).1 a b) = 0 := hKRim.1 a b
      have himKI : Complex.im (((KI : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).1 a b) = 0 := hKIim.1 a b
      have hreKI : Complex.re (((KI : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).1 a b) = 0 := by
        simp [Submodule.coe_add, hKgram a b,
          himKR, himKI, Complex.mul_im, Complex.I_re, Complex.I_im] at him
        exact him.symm
      apply Complex.ext
      · exact hreKI
      · exact himKI
    · have hentry := congrArg
        (fun T : (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker =>
          (((T : sourceFullFrameSymmetricCoordSubmodule d) :
            SourceFullFrameOrientedCoord d).2)) hKsplit
      have him := congrArg Complex.im hentry
      have himKR : Complex.im (((KR : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).2) = 0 := hKRim.2
      have himKI : Complex.im (((KI : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).2) = 0 := hKIim.2
      have hreKI : Complex.re (((KI : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).2) = 0 := by
        simp [Submodule.coe_add, hKdet,
          himKR, himKI, Complex.mul_im, Complex.I_re, Complex.I_im] at him
        exact him.symm
      apply Complex.ext
      · exact hreKI
      · exact himKI
  have hqI_zero : qI = 0 := by
    have h : (fun i => (qI i : ℂ)) = 0 := by
      apply E.injective
      simpa [KI] using hKI_zero
    ext i
    have hi := congrFun h i
    exact Complex.ofReal_injective hi
  intro i
  simpa [qI] using congrFun hqI_zero i

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- The explicit real-compatible normalized kernel map preserves the real
form in finite coordinates. -/
theorem sourceFullFrameRealCompatibleNormalizedKernelMap_real_im
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (q : Fin F.realModelDim → ℝ) :
    ∀ i : Fin F.realModelDim,
      Complex.im (sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
        (fun i => (q i : ℂ)) i) = 0 := by
  let K := sourceFullFrameRealCompatibleExplicitKernelMap d hM0R
      (F.complexCoordEquiv (fun i => (q i : ℂ)))
  have hKreal :
      (∀ a b : Fin (d + 1),
        Complex.im (((K : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).1 a b) = 0) ∧
        Complex.im (((K : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d).2) = 0 := by
    dsimp [K]
    rw [F.complexCoordEquiv_real_eq q]
    exact sourceFullFrameRealCompatibleExplicitKernelMap_real_im d hM0R
      (F.realCoordEquiv q)
  have hsymm := sourceFullFrameRealSliceKernelCoordEquiv_symm_real_im
    d hM0R F K hKreal.1 hKreal.2
  simpa [sourceFullFrameRealCompatibleNormalizedKernelMap, K] using hsymm

/-- Coordinatewise complexification as a continuous real-linear map. -/
noncomputable def sourceFullFrameRealCoordinateComplexifyCLM (m : ℕ) :
    (Fin m → ℝ) →L[ℝ] (Fin m → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

@[simp]
theorem sourceFullFrameRealCoordinateComplexifyCLM_apply
    (m : ℕ) (q : Fin m → ℝ) :
    sourceFullFrameRealCoordinateComplexifyCLM m q =
      fun i => (q i : ℂ) := by
  ext i
  simp [sourceFullFrameRealCoordinateComplexifyCLM]

/-- Coordinatewise real part as a continuous real-linear map. -/
noncomputable def sourceFullFrameComplexCoordinateReCLM (m : ℕ) :
    (Fin m → ℂ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    Complex.reCLM.comp (ContinuousLinearMap.proj i)

@[simp]
theorem sourceFullFrameComplexCoordinateReCLM_apply
    (m : ℕ) (q : Fin m → ℂ) :
    sourceFullFrameComplexCoordinateReCLM m q =
      fun i => (q i).re := by
  ext i
  simp [sourceFullFrameComplexCoordinateReCLM]

/-- The real restriction of the explicit normalized kernel map. -/
noncomputable def sourceFullFrameRealCompatibleNormalizedKernelMapReal
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (Fin F.realModelDim → ℝ) → (Fin F.realModelDim → ℝ) :=
  fun q => sourceFullFrameComplexCoordinateReCLM F.realModelDim
    (sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
      (sourceFullFrameRealCoordinateComplexifyCLM F.realModelDim q))

@[simp]
theorem sourceFullFrameRealCompatibleNormalizedKernelMapReal_zero
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F 0 = 0 := by
  let fC := sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
  let incl := sourceFullFrameRealCoordinateComplexifyCLM F.realModelDim
  have harg : incl (0 : Fin F.realModelDim → ℝ) =
      (0 : Fin F.realModelDim → ℂ) := by
    ext i
    simp [incl]
  have hzero :
      fC (incl (0 : Fin F.realModelDim → ℝ)) = 0 := by
    rw [harg]
    exact sourceFullFrameRealCompatibleNormalizedKernelMap_zero d hM0R F
  ext i
  change (fC (incl (0 : Fin F.realModelDim → ℝ)) i).re = 0
  rw [hzero]
  simp

set_option synthInstance.maxHeartbeats 100000 in
/-- Complexifying the real restriction recovers the explicit normalized
complex kernel map on real finite coordinates. -/
theorem sourceFullFrameRealCompatibleNormalizedKernelMapReal_complexify
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (q : Fin F.realModelDim → ℝ) :
    SCV.realToComplex
        (sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F q) =
      sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
        (SCV.realToComplex q) := by
  change (fun i =>
      ((sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F q i : ℝ) :
        ℂ)) =
      sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
        (fun i => (q i : ℂ))
  ext i
  apply Complex.ext
  · simp [sourceFullFrameRealCompatibleNormalizedKernelMapReal,
      sourceFullFrameRealCoordinateComplexifyCLM]
  · simpa [sourceFullFrameRealCompatibleNormalizedKernelMapReal] using
      (sourceFullFrameRealCompatibleNormalizedKernelMap_real_im
        d hM0R F q i).symm

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- The real restriction of the explicit normalized kernel map has identity
strict derivative at the origin. -/
theorem sourceFullFrameRealCompatibleNormalizedKernelMapReal_hasStrictFDerivAt
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    HasStrictFDerivAt
      (sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F)
      (1 : (Fin F.realModelDim → ℝ) →L[ℝ]
        (Fin F.realModelDim → ℝ)) 0 := by
  let m := F.realModelDim
  let fC := sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
  let incl := sourceFullFrameRealCoordinateComplexifyCLM m
  let re := sourceFullFrameComplexCoordinateReCLM m
  have hfC : HasStrictFDerivAt fC
      (1 : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) 0 := by
    simpa [fC, m] using
      sourceFullFrameRealCompatibleNormalizedKernelMap_hasStrictFDerivAt
        d hM0R F
  have hfC_R : HasStrictFDerivAt fC
      ((1 : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)).restrictScalars ℝ) 0 :=
    hfC.restrictScalars ℝ
  have hincl : HasStrictFDerivAt
      (fun q : Fin m → ℝ => incl q) incl 0 :=
    incl.hasStrictFDerivAt
  have hcomp1 : HasStrictFDerivAt
      (fun q : Fin m → ℝ => fC (incl q))
      (((1 : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)).restrictScalars ℝ).comp incl)
      0 := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℝ) (x := (0 : Fin m → ℝ))
        (g := fC) (f := fun q : Fin m → ℝ => incl q) hfC_R hincl)
  have hre : HasStrictFDerivAt
      (fun z : Fin m → ℂ => re z) re
      (fC (incl (0 : Fin m → ℝ))) :=
    re.hasStrictFDerivAt
  have hcomp2 : HasStrictFDerivAt
      (fun q : Fin m → ℝ => re (fC (incl q)))
      (re.comp
        (((1 : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)).restrictScalars ℝ).comp incl))
      0 := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℝ) (x := (0 : Fin m → ℝ))
        (g := fun z : Fin m → ℂ => re z)
        (f := fun q : Fin m → ℝ => fC (incl q)) hre hcomp1)
  have hderiv :
      re.comp
        (((1 : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)).restrictScalars ℝ).comp incl) =
      (1 : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) := by
    ext q i
    simp [re, incl, sourceFullFrameComplexCoordinateReCLM,
      sourceFullFrameRealCoordinateComplexifyCLM]
  have hfun :
      (fun q : Fin m → ℝ => re (fC (incl q))) =
        sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F := by
    funext q
    rfl
  simpa [hfun, hderiv] using hcomp2

/-- The real inverse-function chart for the real restriction of the explicit
normalized kernel map. -/
noncomputable def sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    OpenPartialHomeomorph (Fin F.realModelDim → ℝ) (Fin F.realModelDim → ℝ) := by
  let f := sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F
  let e : (Fin F.realModelDim → ℝ) ≃L[ℝ] (Fin F.realModelDim → ℝ) :=
    ContinuousLinearEquiv.refl ℝ (Fin F.realModelDim → ℝ)
  have hderiv : HasStrictFDerivAt f
      (e : (Fin F.realModelDim → ℝ) →L[ℝ] (Fin F.realModelDim → ℝ)) 0 := by
    simpa [f, e] using
      sourceFullFrameRealCompatibleNormalizedKernelMapReal_hasStrictFDerivAt
        d hM0R F
  exact @HasStrictFDerivAt.toOpenPartialHomeomorph ℝ _
    (Fin F.realModelDim → ℝ) _ _ (Fin F.realModelDim → ℝ) _ _
    f e 0 inferInstance hderiv

@[simp]
theorem sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph_coe
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F : (Fin F.realModelDim → ℝ) → (Fin F.realModelDim → ℝ)) =
      sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F := by
  rfl

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 400000 in
/-- The real normalized kernel chart contains the origin in its source. -/
theorem sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartSource
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (0 : Fin F.realModelDim → ℝ) ∈
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
        d hM0R F).source := by
  let f := sourceFullFrameRealCompatibleNormalizedKernelMapReal d hM0R F
  let e : (Fin F.realModelDim → ℝ) ≃L[ℝ] (Fin F.realModelDim → ℝ) :=
    ContinuousLinearEquiv.refl ℝ (Fin F.realModelDim → ℝ)
  have hderiv : HasStrictFDerivAt f
      (e : (Fin F.realModelDim → ℝ) →L[ℝ] (Fin F.realModelDim → ℝ)) 0 := by
    simpa [f, e] using
      sourceFullFrameRealCompatibleNormalizedKernelMapReal_hasStrictFDerivAt
        d hM0R F
  unfold sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
  simp only [HasStrictFDerivAt.toOpenPartialHomeomorph,
    ApproximatesLinearOn.toOpenPartialHomeomorph_source]
  exact (Classical.choose_spec hderiv.approximates_deriv_on_open_nhds).1

/-- The real normalized kernel chart contains the origin in its target. -/
theorem sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartTarget
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (0 : Fin F.realModelDim → ℝ) ∈
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
        d hM0R F).target := by
  have hsource :=
    sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartSource
      d hM0R F
  have htarget :=
    (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F).map_source hsource
  simpa using htarget

end BHW
