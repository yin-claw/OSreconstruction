import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRealFullFrameChart
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameHolomorphicSection
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameJacobi

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

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 400000 in
/-- The complex inverse-function chart for the determinant-direction
normalized kernel map.  This is the complex chart that is compatible with the
real route; it uses `sourceFullFrameRealCompatibleKernelProjection`, not the
generic closed-complement projection. -/
noncomputable def sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    OpenPartialHomeomorph (Fin F.realModelDim → ℂ) (Fin F.realModelDim → ℂ) := by
  let f := sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
  let e : (Fin F.realModelDim → ℂ) ≃L[ℂ] (Fin F.realModelDim → ℂ) :=
    ContinuousLinearEquiv.refl ℂ (Fin F.realModelDim → ℂ)
  have hderiv : HasStrictFDerivAt f
      (e : (Fin F.realModelDim → ℂ) →L[ℂ] (Fin F.realModelDim → ℂ)) 0 := by
    simpa [f, e] using
      sourceFullFrameRealCompatibleNormalizedKernelMap_hasStrictFDerivAt
        d hM0R F
  exact @HasStrictFDerivAt.toOpenPartialHomeomorph ℂ _
    (Fin F.realModelDim → ℂ) _ _ (Fin F.realModelDim → ℂ) _ _
    f e 0 inferInstance hderiv

@[simp]
theorem sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC_coe
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
      d hM0R F : (Fin F.realModelDim → ℂ) → (Fin F.realModelDim → ℂ)) =
      sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F := by
  rfl

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 400000 in
/-- The determinant-direction complex normalized kernel chart contains the
origin in its source. -/
theorem sourceFullFrameRealCompatibleNormalizedKernelC_zero_mem_chartSource
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (0 : Fin F.realModelDim → ℂ) ∈
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
        d hM0R F).source := by
  let f := sourceFullFrameRealCompatibleNormalizedKernelMap d hM0R F
  let e : (Fin F.realModelDim → ℂ) ≃L[ℂ] (Fin F.realModelDim → ℂ) :=
    ContinuousLinearEquiv.refl ℂ (Fin F.realModelDim → ℂ)
  have hderiv : HasStrictFDerivAt f
      (e : (Fin F.realModelDim → ℂ) →L[ℂ] (Fin F.realModelDim → ℂ)) 0 := by
    simpa [f, e] using
      sourceFullFrameRealCompatibleNormalizedKernelMap_hasStrictFDerivAt
        d hM0R F
  unfold sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
  simp only [HasStrictFDerivAt.toOpenPartialHomeomorph,
    ApproximatesLinearOn.toOpenPartialHomeomorph_source]
  exact (Classical.choose_spec hderiv.approximates_deriv_on_open_nhds).1

/-- The determinant-direction complex normalized kernel chart contains the
origin in its target. -/
theorem sourceFullFrameRealCompatibleNormalizedKernelC_zero_mem_chartTarget
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (0 : Fin F.realModelDim → ℂ) ∈
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
        d hM0R F).target := by
  have hsource :=
    sourceFullFrameRealCompatibleNormalizedKernelC_zero_mem_chartSource
      d hM0R F
  have htarget :=
    (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorphC
      d hM0R F).map_source hsource
  simpa using htarget

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

/-- Complex frame-level target coordinate for the real-compatible normalized
kernel chart.  It sends a full-frame matrix to the determinant-direction
projected symmetric equation coordinate, written in the finite kernel target
coordinates supplied by the real-form slice packet. -/
noncomputable def sourceFullFrameRealCompatibleFrameTargetCoordC
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →
      Fin F.realModelDim → ℂ :=
  fun M =>
    (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm
      (sourceFullFrameRealCompatibleKernelProjection d hM0R
        (sourceFullFrameSymmetrizeCoord d
            (sourceFullFrameOrientedGramCoord d M) -
          sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal)))

/-- The complex frame-level target coordinate is continuous. -/
theorem continuous_sourceFullFrameRealCompatibleFrameTargetCoordC
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Continuous
      (sourceFullFrameRealCompatibleFrameTargetCoordC d hM0R F) := by
  unfold sourceFullFrameRealCompatibleFrameTargetCoordC
  exact
    (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm.continuous.comp
      ((sourceFullFrameRealCompatibleKernelProjection d hM0R).continuous.comp
        (((continuous_sourceFullFrameSymmetrizeCoord d).comp
          (continuous_sourceFullFrameOrientedGramCoord d)).sub
            continuous_const))

@[simp]
theorem sourceFullFrameRealCompatibleFrameTargetCoordC_base
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    sourceFullFrameRealCompatibleFrameTargetCoordC d hM0R F
        (M0R.map Complex.ofReal) = 0 := by
  unfold sourceFullFrameRealCompatibleFrameTargetCoordC
  have hsymm :
      sourceFullFrameSymmetrizeCoord d
          (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal)) =
        sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal) := by
    apply Subtype.ext
    simpa [sourceFullFrameSymmetricBase] using
      sourceFullFrameSymmetrizeCoord_eq_of_mem_symmetric d
        (sourceFullFrameOrientedGramCoord_mem_symmetric d
          (M0R.map Complex.ofReal))
  rw [hsymm, sub_self]
  change (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm
      ((sourceFullFrameRealCompatibleKernelProjection d hM0R) 0) = 0
  rw [(sourceFullFrameRealCompatibleKernelProjection d hM0R).map_zero]
  exact (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm.map_zero

/-- Complex derivative of the frame-level target coordinate used by the
selected-frame product-chart construction. -/
noncomputable def sourceFullFrameRealCompatibleFrameTargetDerivC
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →L[ℂ]
      (Fin F.realModelDim → ℂ) :=
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker
  ((sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm :
      K →L[ℂ] (Fin F.realModelDim → ℂ)).comp
    ((sourceFullFrameRealCompatibleKernelProjection d hM0R).comp
      ((sourceFullFrameSymmetrizeCoordCLM d).comp
        (sourceFullFrameOrientedDifferentialCLM d (M0R.map Complex.ofReal))))

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 500000 in
/-- The complex frame-level target coordinate has the explicit derivative
obtained by differentiating the oriented full-frame invariant, symmetrizing,
projecting to the real-compatible tangent kernel, and applying finite kernel
coordinates. -/
theorem sourceFullFrameRealCompatibleFrameTargetCoordC_hasStrictFDerivAt
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    HasStrictFDerivAt
      (sourceFullFrameRealCompatibleFrameTargetCoordC d hM0R F)
      (sourceFullFrameRealCompatibleFrameTargetDerivC d hM0R F)
      (M0R.map Complex.ofReal) := by
  let M0C := M0R.map Complex.ofReal
  let Lsym := sourceFullFrameSymmetrizeCoordCLM d
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d M0C)).ker
  let P : sourceFullFrameSymmetricCoordSubmodule d →L[ℂ] K :=
    sourceFullFrameRealCompatibleKernelProjection d hM0R
  let E := sourceFullFrameRealSliceKernelCoordEquiv d hM0R F
  let Es : K →L[ℂ] (Fin F.realModelDim → ℂ) := E.symm
  have hGram : HasStrictFDerivAt
      (sourceFullFrameOrientedGramCoord d)
      (sourceFullFrameOrientedDifferentialCLM d M0C) M0C := by
    simpa [M0C] using sourceFullFrameOrientedGram_hasStrictFDerivAt
      (d := d) (M0 := M0C)
      (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
  have hL : HasStrictFDerivAt
      (fun H : SourceFullFrameOrientedCoord d => Lsym H)
      Lsym (sourceFullFrameOrientedGramCoord d M0C) :=
    Lsym.hasStrictFDerivAt
  have hSymm : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        Lsym (sourceFullFrameOrientedGramCoord d M))
      (Lsym.comp (sourceFullFrameOrientedDifferentialCLM d M0C)) M0C := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := M0C)
        (g := fun H : SourceFullFrameOrientedCoord d => Lsym H)
        (f := sourceFullFrameOrientedGramCoord d) hL hGram)
  let base := sourceFullFrameSymmetricBase d M0C
  have hSub : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        Lsym (sourceFullFrameOrientedGramCoord d M) - base)
      (Lsym.comp (sourceFullFrameOrientedDifferentialCLM d M0C)) M0C := by
    exact hSymm.sub_const base
  have hP : HasStrictFDerivAt
      (P : sourceFullFrameSymmetricCoordSubmodule d → K)
      P (Lsym (sourceFullFrameOrientedGramCoord d M0C) - base) :=
    @ContinuousLinearMap.hasStrictFDerivAt ℂ _
      (sourceFullFrameSymmetricCoordSubmodule d) _ _ _
      K _ _ _
      P (Lsym (sourceFullFrameOrientedGramCoord d M0C) - base)
  have hPcomp : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        P (Lsym (sourceFullFrameOrientedGramCoord d M) - base))
      (P.comp (Lsym.comp (sourceFullFrameOrientedDifferentialCLM d M0C)))
      M0C := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := M0C)
        (g := (P : sourceFullFrameSymmetricCoordSubmodule d → K))
        (f := fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
          Lsym (sourceFullFrameOrientedGramCoord d M) - base) hP hSub)
  have hE : HasStrictFDerivAt
      (Es : K → Fin F.realModelDim → ℂ)
      Es (P (Lsym (sourceFullFrameOrientedGramCoord d M0C) - base)) :=
    @ContinuousLinearMap.hasStrictFDerivAt ℂ _
      K _ _ _
      (Fin F.realModelDim → ℂ) _ _ _
      Es (P (Lsym (sourceFullFrameOrientedGramCoord d M0C) - base))
  have hcomp : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        Es (P (Lsym (sourceFullFrameOrientedGramCoord d M) - base)))
      (Es.comp (P.comp (Lsym.comp
        (sourceFullFrameOrientedDifferentialCLM d M0C)))) M0C := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := M0C)
        (g := (Es : K → Fin F.realModelDim → ℂ))
        (f := fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
          P (Lsym (sourceFullFrameOrientedGramCoord d M) - base))
        hE hPcomp)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards with M
  simp [sourceFullFrameRealCompatibleFrameTargetCoordC,
    M0C, Lsym, P, E, Es, K, base, sourceFullFrameSymmetrizeCoordCLM]

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 500000 in
/-- On the explicit complex slice coordinates, the complex frame-target
derivative recovers the finite coordinate vector. -/
theorem sourceFullFrameRealCompatibleFrameTargetDerivC_complexCoordEquiv
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (q : Fin F.realModelDim → ℂ) :
    sourceFullFrameRealCompatibleFrameTargetDerivC d hM0R F
        (F.complexCoordEquiv q :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = q := by
  let hM0C := sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
  let S := sourceFullFrameExplicitGaugeSliceData d hM0C
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker
  let E := sourceFullFrameRealSliceKernelCoordEquiv d hM0R F
  let X : S.slice := F.complexCoordEquiv q
  have hsymm :
      (sourceFullFrameSymmetrizeCoordCLM d)
          (sourceFullFrameOrientedDifferentialCLM d (M0R.map Complex.ofReal)
            (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) =
        sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S X := by
    apply Subtype.ext
    change
      (sourceFullFrameSymmetrizeCoord d
          (sourceFullFrameOrientedDifferential d (M0R.map Complex.ofReal)
            (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) :
          SourceFullFrameOrientedCoord d) =
        sourceFullFrameOrientedDifferential d (M0R.map Complex.ofReal)
          (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    exact sourceFullFrameSymmetrizeCoord_eq_of_mem_symmetric d
      (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S X).property
  have hproj :
      (sourceFullFrameRealCompatibleKernelProjection d hM0R)
          (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0C S X) =
        sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S X := by
    have hp := sourceFullFrameRealCompatibleKernelProjection_apply_ker d hM0R
      (sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S X)
    simpa [sourceFullFrameGaugeSliceKernelDerivCLM] using hp
  calc
    sourceFullFrameRealCompatibleFrameTargetDerivC d hM0R F
        (F.complexCoordEquiv q :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
        = E.symm ((sourceFullFrameRealCompatibleKernelProjection d hM0R)
            ((sourceFullFrameSymmetrizeCoordCLM d)
              (sourceFullFrameOrientedDifferentialCLM d
                (M0R.map Complex.ofReal)
                (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)))) := by
          simp [sourceFullFrameRealCompatibleFrameTargetDerivC, E, X]
    _ = E.symm (sourceFullFrameGaugeSliceKernelDerivCLM d hM0C S X) := by
          rw [hsymm, hproj]
    _ = q := by
          rw [← sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv_coe]
          let e :=
            sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv
              d hM0C S
          change F.complexCoordEquiv.symm
              (e.symm (e (F.complexCoordEquiv q))) = q
          rw [ContinuousLinearEquiv.symm_apply_apply]
          exact ContinuousLinearEquiv.symm_apply_apply F.complexCoordEquiv q

/-- Complexification of real full-frame matrices as a continuous real-linear
map. -/
noncomputable def sourceFullFrameRealMatrixComplexifyCLM
    (d : ℕ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →L[ℝ]
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.pi fun j =>
      Complex.ofRealCLM.comp
        ((ContinuousLinearMap.proj j).comp
          (ContinuousLinearMap.proj i :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →L[ℝ]
              Fin (d + 1) → ℝ))

@[simp]
theorem sourceFullFrameRealMatrixComplexifyCLM_apply
    (d : ℕ)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    sourceFullFrameRealMatrixComplexifyCLM d M = M.map Complex.ofReal := by
  ext i j
  change Complex.ofRealCLM (M i j) = (M i j : ℂ)
  simp

/-- Real frame-level target coordinate, obtained by restricting the complex
target coordinate to complexified real frames and taking coordinatewise real
part. -/
noncomputable def sourceFullFrameRealCompatibleFrameTargetCoordR
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →
      Fin F.realModelDim → ℝ :=
  fun M =>
    sourceFullFrameComplexCoordinateReCLM F.realModelDim
      (sourceFullFrameRealCompatibleFrameTargetCoordC d hM0R F
        (M.map Complex.ofReal))

/-- The real frame-level target coordinate is continuous. -/
theorem continuous_sourceFullFrameRealCompatibleFrameTargetCoordR
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Continuous
      (sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F) := by
  unfold sourceFullFrameRealCompatibleFrameTargetCoordR
  apply (sourceFullFrameComplexCoordinateReCLM F.realModelDim).continuous.comp
  apply
    (continuous_sourceFullFrameRealCompatibleFrameTargetCoordC d hM0R F).comp
  fun_prop

@[simp]
theorem sourceFullFrameRealCompatibleFrameTargetCoordR_base
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F M0R = 0 := by
  unfold sourceFullFrameRealCompatibleFrameTargetCoordR
  rw [sourceFullFrameRealCompatibleFrameTargetCoordC_base d hM0R F]
  ext i
  simp [sourceFullFrameComplexCoordinateReCLM]

/-- Real derivative of the frame-level target coordinate used by the
selected-frame product-chart construction. -/
noncomputable def sourceFullFrameRealCompatibleFrameTargetDerivR
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →L[ℝ]
      (Fin F.realModelDim → ℝ) :=
  (sourceFullFrameComplexCoordinateReCLM F.realModelDim).comp
    (((sourceFullFrameRealCompatibleFrameTargetDerivC d hM0R F).restrictScalars ℝ).comp
      (sourceFullFrameRealMatrixComplexifyCLM d))

set_option synthInstance.maxHeartbeats 140000 in
set_option maxHeartbeats 500000 in
/-- The real frame-level target coordinate has the real derivative obtained by
restricting the complex derivative to complexified real matrices and taking
coordinatewise real part. -/
theorem sourceFullFrameRealCompatibleFrameTargetCoordR_hasStrictFDerivAt
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    HasStrictFDerivAt
      (sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F)
      (sourceFullFrameRealCompatibleFrameTargetDerivR d hM0R F)
      M0R := by
  let fC := sourceFullFrameRealCompatibleFrameTargetCoordC d hM0R F
  let LC := sourceFullFrameRealCompatibleFrameTargetDerivC d hM0R F
  let incl := sourceFullFrameRealMatrixComplexifyCLM d
  let re := sourceFullFrameComplexCoordinateReCLM F.realModelDim
  have hC : HasStrictFDerivAt fC LC (M0R.map Complex.ofReal) := by
    simpa [fC, LC] using
      sourceFullFrameRealCompatibleFrameTargetCoordC_hasStrictFDerivAt
        d hM0R F
  have hC_R : HasStrictFDerivAt fC (LC.restrictScalars ℝ)
      (M0R.map Complex.ofReal) :=
    hC.restrictScalars ℝ
  have hC_at_incl : HasStrictFDerivAt fC (LC.restrictScalars ℝ)
      (incl M0R) := by
    simpa [incl] using hC_R
  have hincl : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => incl M)
      incl M0R :=
    ContinuousLinearMap.hasStrictFDerivAt incl (x := M0R)
  have hcomp1 : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => fC (incl M))
      ((LC.restrictScalars ℝ).comp incl) M0R := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℝ) (x := M0R)
        (g := fC)
        (f := fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => incl M)
        hC_at_incl hincl)
  have hre : HasStrictFDerivAt
      (fun q : Fin F.realModelDim → ℂ => re q)
      re (fC (incl M0R)) :=
    ContinuousLinearMap.hasStrictFDerivAt re (x := fC (incl M0R))
  have hcomp2 : HasStrictFDerivAt
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ =>
        re (fC (incl M)))
      (re.comp ((LC.restrictScalars ℝ).comp incl)) M0R := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℝ) (x := M0R)
        (g := fun q : Fin F.realModelDim → ℂ => re q)
        (f := fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ =>
          fC (incl M)) hre hcomp1)
  simpa [sourceFullFrameRealCompatibleFrameTargetCoordR,
    sourceFullFrameRealCompatibleFrameTargetDerivR, fC, LC, incl, re]
    using hcomp2

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 500000 in
/-- On the explicit real slice coordinates, the real frame-target derivative
recovers the finite coordinate vector. -/
theorem sourceFullFrameRealCompatibleFrameTargetDerivR_realCoordEquiv
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (q : Fin F.realModelDim → ℝ) :
    sourceFullFrameRealCompatibleFrameTargetDerivR d hM0R F
        ((F.realCoordEquiv q :
            sourceFullFrameRealDifferentialRightInverseRange d hM0R) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) = q := by
  let XR : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    (F.realCoordEquiv q :
      sourceFullFrameRealDifferentialRightInverseRange d hM0R)
  have hcomplex :
      (F.complexCoordEquiv (fun i => (q i : ℂ)) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
        XR.map Complex.ofReal := by
    have h := F.complexCoordEquiv_real_eq q
    exact congrArg Subtype.val h
  change sourceFullFrameComplexCoordinateReCLM F.realModelDim
      (sourceFullFrameRealCompatibleFrameTargetDerivC d hM0R F
        (XR.map Complex.ofReal)) = q
  rw [← hcomplex]
  rw [sourceFullFrameRealCompatibleFrameTargetDerivC_complexCoordEquiv]
  ext i
  simp [sourceFullFrameComplexCoordinateReCLM]

/-- The real frame-target derivative is surjective. -/
theorem sourceFullFrameRealCompatibleFrameTargetDerivR_range_eq_top
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    LinearMap.range
        (sourceFullFrameRealCompatibleFrameTargetDerivR d hM0R F).toLinearMap =
      ⊤ := by
  rw [LinearMap.range_eq_top]
  intro q
  exact
    ⟨((F.realCoordEquiv q :
        sourceFullFrameRealDifferentialRightInverseRange d hM0R) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      sourceFullFrameRealCompatibleFrameTargetDerivR_realCoordEquiv
        d hM0R F q⟩

/-- Frame matrices whose real-compatible target coordinate lies in the local
real inverse-function target and whose determinant remains nonzero. -/
def sourceFullFrameRealCompatibleFrameDomain
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :=
  {M |
    sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F M ∈
      (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
        d hM0R F).target ∧
    M.det ≠ 0}

/-- The real-compatible frame domain is open. -/
theorem sourceFullFrameRealCompatibleFrameDomain_open
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    IsOpen (sourceFullFrameRealCompatibleFrameDomain d hM0R F) := by
  unfold sourceFullFrameRealCompatibleFrameDomain
  refine
    ((sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F).open_target.preimage
        (continuous_sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F)
      ).inter ?_
  exact
    isOpen_ne_fun
      (continuous_id.matrix_det :
        Continuous
          (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => M.det))
      continuous_const

/-- The base real frame lies in the real-compatible frame domain. -/
theorem sourceFullFrameRealCompatibleFrameDomain_base_mem
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    M0R ∈ sourceFullFrameRealCompatibleFrameDomain d hM0R F := by
  constructor
  · rw [sourceFullFrameRealCompatibleFrameTargetCoordR_base d hM0R F]
    exact
      sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartTarget
        d hM0R F
  · exact hM0R.ne_zero

/-- Every matrix in the real-compatible frame domain has nonzero determinant. -/
theorem sourceFullFrameRealCompatibleFrameDomain_det_nonzero
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    sourceFullFrameRealCompatibleFrameDomain d hM0R F ⊆ {M | M.det ≠ 0} := by
  intro M hM
  exact hM.2

/-- The real selected-frame slice coordinate obtained by applying the inverse
of the real normalized kernel chart to the frame-level target coordinate. -/
noncomputable def sourceFullFrameRealCompatibleFrameKernelCoordR
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →
      Fin F.realModelDim → ℝ :=
  fun M =>
    (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F).symm
        (sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F M)

/-- The real selected-frame slice coordinate is continuous on the local
real-compatible frame domain. -/
theorem continuousOn_sourceFullFrameRealCompatibleFrameKernelCoordR
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    ContinuousOn
      (sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F)
      (sourceFullFrameRealCompatibleFrameDomain d hM0R F) := by
  unfold sourceFullFrameRealCompatibleFrameKernelCoordR
  exact
    (sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F).continuousOn_symm.comp
        (continuous_sourceFullFrameRealCompatibleFrameTargetCoordR
          d hM0R F).continuousOn
        (by
          intro M hM
          exact hM.1)

@[simp]
theorem sourceFullFrameRealCompatibleFrameKernelCoordR_base
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F M0R = 0 := by
  let e :=
    sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F
  have hsource :
      (0 : Fin F.realModelDim → ℝ) ∈ e.source := by
    simpa [e] using
      sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartSource
        d hM0R F
  have htarget :
      (0 : Fin F.realModelDim → ℝ) ∈ e.target := by
    simpa [e] using
      sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartTarget
        d hM0R F
  have he0 : e (0 : Fin F.realModelDim → ℝ) =
      (0 : Fin F.realModelDim → ℝ) := by
    rw [sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph_coe]
    exact sourceFullFrameRealCompatibleNormalizedKernelMapReal_zero d hM0R F
  unfold sourceFullFrameRealCompatibleFrameKernelCoordR
  rw [sourceFullFrameRealCompatibleFrameTargetCoordR_base d hM0R F]
  exact ((e.eq_symm_apply hsource htarget).mpr he0).symm

/-- A total complex selected-frame coordinate obtained from the real coordinate
on complexified real frames.  Away from the real locus it is an arbitrary
zero extension; the full implicit-chart producer later proves that the actual
complex max-rank chart agrees with this coordinate on the real source patch
where it is used. -/
noncomputable def sourceFullFrameRealCompatibleComplexKernelCoordFromReal
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →
      (sourceFullFrameExplicitGaugeSliceData d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice :=
  fun M =>
    if h : ∃ MR : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
        M = MR.map Complex.ofReal then
      F.complexCoordEquiv
        (SCV.realToComplex
          (sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F
            (Classical.choose h)))
    else 0

/-- On complexified real frames, the total complex selected-frame coordinate
is exactly the complexification of the real selected-frame coordinate. -/
theorem sourceFullFrameRealCompatibleComplexKernelCoordFromReal_real_eq
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    sourceFullFrameRealCompatibleComplexKernelCoordFromReal d hM0R F
        (M.map Complex.ofReal) =
      F.complexCoordEquiv
        (SCV.realToComplex
          (sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F M)) := by
  unfold sourceFullFrameRealCompatibleComplexKernelCoordFromReal
  let h : ∃ MR : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      M.map Complex.ofReal = MR.map Complex.ofReal := ⟨M, rfl⟩
  have hchoose : Classical.choose h = M := by
    have hspec := Classical.choose_spec h
    ext i j
    exact Complex.ofReal_injective (congrFun (congrFun hspec i) j).symm
  rw [dif_pos h]
  rw [hchoose]

/-- Mechanical constructor for the real gauge-slice packet once a compatible
complex selected-frame coordinate is supplied.  The gauge-slice packet records
the local frame domain, determinant control, continuity, and real/complex
compatibility; the open-image obligation belongs to the final shrunken source
chart, not to this frame-domain-wide packet. -/
noncomputable def sourceFullFrameRealGaugeSliceData_of_frameKernelCoord
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R)
    (complexKernelCoord :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice)
    (complexKernelCoord_real_eq :
      ∀ M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
        complexKernelCoord (M.map Complex.ofReal) =
          F.complexCoordEquiv
            (SCV.realToComplex
              (sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F M))) :
    SourceFullFrameRealGaugeSliceData d M0R hM0R.ne_zero where
  M0_det_unit := sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
  complexSlice :=
    sourceFullFrameExplicitGaugeSliceData d
      (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
  realModelDim := F.realModelDim
  realModelToComplexSlice := F.complexCoordEquiv
  realKernelCoord :=
    sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F
  complexKernelCoord := complexKernelCoord
  complexKernelCoord_real_eq := complexKernelCoord_real_eq
  frameDomain := sourceFullFrameRealCompatibleFrameDomain d hM0R F
  frameDomain_open :=
    sourceFullFrameRealCompatibleFrameDomain_open d hM0R F
  center_mem_frameDomain :=
    sourceFullFrameRealCompatibleFrameDomain_base_mem d hM0R F
  frameDomain_det_nonzero :=
    sourceFullFrameRealCompatibleFrameDomain_det_nonzero d hM0R F
  realKernelCoord_continuousOn :=
    continuousOn_sourceFullFrameRealCompatibleFrameKernelCoordR d hM0R F

/-- Mechanical real gauge-slice constructor in the common case where the
complex selected-frame coordinate is the canonical real-locus extension above.
This is the direct constructor for `SourceFullFrameRealGaugeSliceData` from the
checked real-compatible IFT frame-domain packet. -/
noncomputable def sourceFullFrameRealGaugeSliceData_of_frameKernelCoord_realExtension
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    SourceFullFrameRealGaugeSliceData d M0R hM0R.ne_zero :=
  sourceFullFrameRealGaugeSliceData_of_frameKernelCoord d hM0R F
    (sourceFullFrameRealCompatibleComplexKernelCoordFromReal d hM0R F)
    (sourceFullFrameRealCompatibleComplexKernelCoordFromReal_real_eq
      d hM0R F)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 700000 in
/-- The real-compatible selected-frame slice supplies the local product chart
whose first coordinate is the checked real selected-frame kernel coordinate. -/
noncomputable def sourceFullFrameRealSelectedFrameProductChartData_of_realCompatibleSlice
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hM0R : IsUnit (sourceRealFullFrameMatrix d n ι x0).det)
    (F : SourceFullFrameRealSliceFiniteCoordData d
      (sourceRealFullFrameMatrix d n ι x0) hM0R) :
    Sigma fun O : Type =>
      Sigma fun instO : TopologicalSpace O =>
        @SourceFullFrameRealSelectedFrameProductChartData
          d n ι x0 hM0R.ne_zero
          (sourceFullFrameRealGaugeSliceData_of_frameKernelCoord_realExtension
            d hM0R F)
          O instO := by
  let M0R := sourceRealFullFrameMatrix d n ι x0
  let S :=
    sourceFullFrameRealGaugeSliceData_of_frameKernelCoord_realExtension
      d hM0R F
  let f := sourceFullFrameRealCompatibleFrameTargetCoordR d hM0R F
  let f' := sourceFullFrameRealCompatibleFrameTargetDerivR d hM0R F
  let O := f'.ker
  let eK :=
    sourceFullFrameRealCompatibleNormalizedKernelOpenPartialHomeomorph
      d hM0R F
  have hf : HasStrictFDerivAt f f' M0R := by
    simpa [f, f', M0R] using
      sourceFullFrameRealCompatibleFrameTargetCoordR_hasStrictFDerivAt
        d hM0R F
  have hsurj : LinearMap.range f'.toLinearMap = ⊤ := by
    simpa [f'] using
      sourceFullFrameRealCompatibleFrameTargetDerivR_range_eq_top d hM0R F
  let eT : OpenPartialHomeomorph
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      ((Fin F.realModelDim → ℝ) × O) :=
    hf.implicitToOpenPartialHomeomorph f f' hsurj
  let eProd : OpenPartialHomeomorph
      ((Fin F.realModelDim → ℝ) × O)
      ((Fin F.realModelDim → ℝ) × O) :=
    eK.symm.prod (OpenPartialHomeomorph.refl O)
  let sourceOpen : Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :=
    S.frameDomain ∩ {M | M.det ≠ 0}
  have hsourceOpen : IsOpen sourceOpen := by
    exact S.frameDomain_open.inter
      (isOpen_ne_fun
        (continuous_id.matrix_det :
          Continuous
            (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ =>
              M.det))
        continuous_const)
  let frameChart := (eT.trans eProd).restrOpen sourceOpen hsourceOpen
  refine ⟨O, ?_⟩
  letI : TopologicalSpace O := inferInstance
  refine ⟨inferInstance, ?_⟩
  refine
    { frameChart := frameChart
      center_mem_source := ?_
      source_det := ?_
      source_frameDomain := ?_
      first_eq_realKernelCoord := ?_ }
  · have hTsource : M0R ∈ eT.source :=
      hf.mem_implicitToOpenPartialHomeomorph_source hsurj
    have hTself : eT M0R = (f M0R, (0 : O)) := by
      exact hf.implicitToOpenPartialHomeomorph_self hsurj
    have hKtarget : (0 : Fin F.realModelDim → ℝ) ∈ eK.target := by
      simpa [eK] using
        sourceFullFrameRealCompatibleNormalizedKernel_zero_mem_chartTarget
          d hM0R F
    have hProdSource : eT M0R ∈ eProd.source := by
      have hf0 : f M0R = 0 := by
        simp [f, M0R]
      rw [hTself]
      simpa [eProd, hf0] using hKtarget
    have hTrans : M0R ∈ (eT.trans eProd).source :=
      ⟨hTsource, hProdSource⟩
    have hOpen : M0R ∈ sourceOpen :=
      ⟨S.center_mem_frameDomain, hM0R.ne_zero⟩
    exact ⟨hTrans, hOpen⟩
  · intro M hM
    exact hM.2.2
  · intro M hM
    exact hM.2.1
  · intro M _hM
    have hfirstT : (eT M).1 = f M := by
      exact hf.implicitToOpenPartialHomeomorph_fst hsurj M
    change (eProd (eT M)).1 = eK.symm (f M)
    simp [eProd, hfirstT]

/-- The checked real-compatible full-frame gauge-slice packet at a real
determinant-nonzero base. -/
theorem sourceFullFrameRealGaugeSliceData
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    Nonempty (SourceFullFrameRealGaugeSliceData d M0R hM0R.ne_zero) := by
  rcases sourceFullFrameRealSliceFiniteCoordData d hM0R with ⟨F⟩
  exact
    ⟨sourceFullFrameRealGaugeSliceData_of_frameKernelCoord_realExtension
      d hM0R F⟩

end BHW
