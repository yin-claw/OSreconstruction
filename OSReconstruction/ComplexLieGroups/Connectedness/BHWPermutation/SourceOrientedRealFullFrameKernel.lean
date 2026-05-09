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

end BHW
