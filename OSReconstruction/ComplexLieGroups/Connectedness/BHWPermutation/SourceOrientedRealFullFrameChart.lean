import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRealUniqueness

/-!
# Real-compatible full-frame chart data

This file contains the mechanical packaging layer for the hard full-frame real
chart theorem.  The remaining analytic input is the construction of the
real-compatible slice and real/complex implicit chart data; once that data is
available, the conversion to `SourceOrientedLocalRealChartData` is formal.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- A real gauge-slice packet whose complexification is the complex full-frame
gauge slice used by the existing full-frame max-rank chart. -/
structure SourceFullFrameRealGaugeSliceData
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (_hM0R : M0R.det ≠ 0) where
  M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := M0R.map Complex.ofReal
  M0_det_unit : IsUnit M0.det
  complexSlice : SourceFullFrameGaugeSliceData d M0
  realModelDim : ℕ
  realModelToComplexSlice :
    (Fin realModelDim → ℂ) ≃L[ℂ] complexSlice.slice
  realKernelCoord :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ → Fin realModelDim → ℝ
  complexKernelCoord :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ → complexSlice.slice
  complexKernelCoord_real_eq :
    ∀ M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      complexKernelCoord (M.map Complex.ofReal) =
        realModelToComplexSlice (SCV.realToComplex (realKernelCoord M))
  frameDomain : Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
  frameDomain_open : IsOpen frameDomain
  center_mem_frameDomain : M0R ∈ frameDomain
  frameDomain_det_nonzero : frameDomain ⊆ {M | M.det ≠ 0}
  realKernelCoord_continuous : Continuous realKernelCoord
  realKernelCoord_image_open_on_frameDomain :
    ∀ {S : Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)},
      IsOpen S → S ⊆ frameDomain → IsOpen (realKernelCoord '' S)

/-- Full-frame real/complex chart data before it is collapsed to the generic
`SourceOrientedLocalRealChartData` interface. -/
structure SourceFullFrameRealCompatibleImplicitChartData
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x0 : Fin n → Fin (d + 1) → ℝ)
    (hdet : sourceRealFullFrameDet d n ι x0 ≠ 0) where
  slice :
    SourceFullFrameRealGaugeSliceData d
      (sourceRealFullFrameMatrix d n ι x0) hdet
  m : ℕ
  C :
    SourceOrientedMaxRankChartData d n
      (M := Fin m → ℂ)
      (sourceRealOrientedMinkowskiInvariant d n x0)
  coordEquivR :
    (Fin m → ℝ) ≃ₗ[ℝ]
      ((Fin slice.realModelDim → ℝ) ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))
  coordEquivC :
    (Fin m → ℂ) ≃ₗ[ℂ]
      ((Fin slice.realModelDim → ℂ) ×
        (sourceComplementIndex ι → Fin (d + 1) → ℂ))
  coordEquiv_realToComplex :
    ∀ u : Fin m → ℝ,
      coordEquivC (SCV.realToComplex u) =
        (SCV.realToComplex (coordEquivR u).1,
          fun k a => ((coordEquivR u).2 k a : ℂ))
  E0 : Set (Fin n → Fin (d + 1) → ℝ)
  E0_open : IsOpen E0
  center_mem : x0 ∈ E0
  invariant_mem_chart :
    ∀ x ∈ E0, sourceRealOrientedMinkowskiInvariant d n x ∈ C.Ω
  frame_mem_domain :
    ∀ x ∈ E0,
      sourceRealFullFrameMatrix d n ι x ∈ slice.frameDomain
  realCoord : (Fin n → Fin (d + 1) → ℝ) → Fin m → ℝ
  realCoord_eq_kernel_mixed :
    ∀ x ∈ E0,
      coordEquivR (realCoord x) =
        (slice.realKernelCoord (sourceRealFullFrameMatrix d n ι x),
          sourceRealSelectedMixedRows d n ι x)
  chart_eq_kernel_mixed :
    ∀ x ∈ E0,
      coordEquivC (C.chart (sourceRealOrientedMinkowskiInvariant d n x)) =
        (slice.realModelToComplexSlice.symm
          (slice.complexKernelCoord
            ((sourceRealFullFrameMatrix d n ι x).map Complex.ofReal)),
          sourceSelectedMixedRows d n ι
            (sourceRealOrientedMinkowskiInvariant d n x))
  realCoord_continuous : Continuous realCoord
  realCoord_image_open :
    ∀ {S : Set (Fin n → Fin (d + 1) → ℝ)},
      IsOpen S → S ⊆ E0 → IsOpen (realCoord '' S)

namespace SourceFullFrameRealCompatibleImplicitChartData

/-- The kernel/mixed real-compatibility equations imply the generic
`chart_real_eq` field required by the totally-real identity consumer. -/
theorem chart_real_eq
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (R : SourceFullFrameRealCompatibleImplicitChartData d n ι x0 hdet)
    (x : Fin n → Fin (d + 1) → ℝ)
    (hx : x ∈ R.E0) :
    R.C.chart (sourceRealOrientedMinkowskiInvariant d n x) =
      SCV.realToComplex (R.realCoord x) := by
  apply R.coordEquivC.injective
  rw [R.chart_eq_kernel_mixed x hx, R.coordEquiv_realToComplex]
  rw [R.realCoord_eq_kernel_mixed x hx]
  apply Prod.ext
  · rw [R.slice.complexKernelCoord_real_eq]
    simp
  · exact sourceSelectedMixedRows_sourceRealOrientedMinkowskiInvariant d n ι x

/-- Collapse real-compatible full-frame chart data to the generic local real
chart data used by the oriented uniqueness theorem. -/
noncomputable def to_localRealChartData
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (R : SourceFullFrameRealCompatibleImplicitChartData d n ι x0 hdet) :
    SourceOrientedLocalRealChartData d n x0 where
  m := R.m
  C := R.C
  E0 := R.E0
  E0_open := R.E0_open
  center_mem := R.center_mem
  invariant_mem_chart := R.invariant_mem_chart
  realCoord := R.realCoord
  realCoord_continuous := R.realCoord_continuous
  realCoord_image_open := R.realCoord_image_open
  chart_real_eq := R.chart_real_eq

end SourceFullFrameRealCompatibleImplicitChartData

/-- Once the hard real-compatible implicit chart data is available, the
pointwise full-frame local real chart theorem is immediate. -/
theorem sourceOrientedLocalRealChartData_of_fullFrameRealCompatibleImplicitChartData
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (R :
      Nonempty
        (SourceFullFrameRealCompatibleImplicitChartData d n ι x0 hdet)) :
    Nonempty (SourceOrientedLocalRealChartData d n x0) := by
  rcases R with ⟨R⟩
  exact ⟨R.to_localRealChartData⟩

end BHW
