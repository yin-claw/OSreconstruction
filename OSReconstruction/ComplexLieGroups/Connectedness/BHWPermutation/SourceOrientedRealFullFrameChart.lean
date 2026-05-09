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

/-- Complexifying a real selected full-frame matrix complexifies its
determinant. -/
theorem sourceRealFullFrameMatrix_map_ofReal_det
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    ((sourceRealFullFrameMatrix d n ι x).map Complex.ofReal).det =
      (sourceRealFullFrameDet d n ι x : ℂ) := by
  rw [sourceRealFullFrameDet]
  exact
    (RingHom.map_det Complex.ofRealHom
      (sourceRealFullFrameMatrix d n ι x)
    ).symm

/-- A nonzero real selected full-frame determinant remains a unit after
complexifying the selected full-frame matrix. -/
theorem sourceRealFullFrameMatrix_map_ofReal_det_isUnit
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hdet : sourceRealFullFrameDet d n ι x ≠ 0) :
    IsUnit ((sourceRealFullFrameMatrix d n ι x).map Complex.ofReal).det := by
  rw [sourceRealFullFrameMatrix_map_ofReal_det]
  exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hdet)

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

/-- The real kernel coordinate together with the selected mixed-row coordinates
of a source tuple.  This is the raw real coordinate map before applying the
finite coordinate equivalence in `SourceFullFrameRealCompatibleImplicitChartData`. -/
def sourceFullFrameRealKernelMixedCoord
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (x : Fin n → Fin (d + 1) → ℝ) :
    (Fin S.realModelDim → ℝ) ×
      (sourceComplementIndex ι → Fin (d + 1) → ℝ) :=
  (S.realKernelCoord (sourceRealFullFrameMatrix d n ι x),
    sourceRealSelectedMixedRows d n ι x)

/-- The kernel-plus-mixed real coordinate map is continuous. -/
theorem continuous_sourceFullFrameRealKernelMixedCoord
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet) :
    Continuous (sourceFullFrameRealKernelMixedCoord S) := by
  apply Continuous.prodMk
  · exact S.realKernelCoord_continuous.comp
      (continuous_sourceRealFullFrameMatrix d n ι)
  · exact continuous_sourceRealSelectedMixedRows d n ι

/-- Composing the raw kernel/mixed coordinate map with a finite real coordinate
equivalence gives a continuous real coordinate map. -/
theorem continuous_sourceFullFrameRealCoord_of_kernelMixedCoord
    {d n m : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (coordEquivR :
      (Fin m → ℝ) ≃ₗ[ℝ]
        ((Fin S.realModelDim → ℝ) ×
          (sourceComplementIndex ι → Fin (d + 1) → ℝ))) :
    Continuous
      (fun x : Fin n → Fin (d + 1) → ℝ =>
        coordEquivR.symm (sourceFullFrameRealKernelMixedCoord S x)) := by
  exact
    (LinearMap.continuous_of_finiteDimensional coordEquivR.symm.toLinearMap).comp
      (continuous_sourceFullFrameRealKernelMixedCoord S)

/-- If the raw kernel/mixed coordinate image is open, then applying the inverse
finite real coordinate equivalence preserves openness. -/
theorem isOpen_sourceFullFrameRealCoord_image_of_kernelMixedCoord_image_open
    {d n m : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (coordEquivR :
      (Fin m → ℝ) ≃ₗ[ℝ]
        ((Fin S.realModelDim → ℝ) ×
          (sourceComplementIndex ι → Fin (d + 1) → ℝ)))
    {U : Set (Fin n → Fin (d + 1) → ℝ)}
    (hU :
      IsOpen (sourceFullFrameRealKernelMixedCoord S '' U)) :
    IsOpen
      ((fun x : Fin n → Fin (d + 1) → ℝ =>
        coordEquivR.symm (sourceFullFrameRealKernelMixedCoord S x)) '' U) := by
  rw [← Set.image_image]
  exact coordEquivR.symm.toContinuousLinearEquiv.toHomeomorph.isOpenMap
    (sourceFullFrameRealKernelMixedCoord S '' U) hU

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

/-- Pointwise producer for the remaining hard real-compatible full-frame chart
theorem. -/
def SourceFullFrameRealCompatibleImplicitChartProducer
    (d n : ℕ) : Prop :=
  ∀ (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ},
    (hdet : sourceRealFullFrameDet d n ι x0 ≠ 0) →
      Nonempty (SourceFullFrameRealCompatibleImplicitChartData d n ι x0 hdet)

/-- A pointwise real-compatible full-frame chart producer supplies the public
local real chart theorem on every determinant-nonzero sheet. -/
theorem sourceOrientedLocalRealChartData_of_fullFrameDet_ne_zero_of_realCompatibleImplicitChartProducer
    {d n : ℕ}
    (P : SourceFullFrameRealCompatibleImplicitChartProducer d n)
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hdet : sourceRealFullFrameDet d n ι x0 ≠ 0) :
    Nonempty (SourceOrientedLocalRealChartData d n x0) :=
  sourceOrientedLocalRealChartData_of_fullFrameRealCompatibleImplicitChartData
    (P ι hdet)

/-- A source-open determinant-nonzero Jost patch is an oriented real
environment once the pointwise real-compatible full-frame chart producer is
available. -/
theorem sourceOrientedRealEnvironment_of_realCompatibleImplicitChartProducer
    {d n : ℕ}
    (P : SourceFullFrameRealCompatibleImplicitChartProducer d n)
    (ι : Fin (d + 1) ↪ Fin n)
    {E : Set (Fin n → Fin (d + 1) → ℝ)}
    (hE_open : IsOpen E)
    (hE_nonempty : E.Nonempty)
    (hE_jost : E ⊆ JostSet d n)
    (hdet :
      ∀ x ∈ E, sourceRealFullFrameDet d n ι x ≠ 0) :
    IsHWOrientedRealEnvironment d n E :=
  sourceOrientedRealEnvironment_of_fullFrameDetNonzero_localCharts
    d n ι hE_open hE_nonempty hE_jost hdet
    (fun {_x} hx =>
      sourceOrientedLocalRealChartData_of_fullFrameRealCompatibleImplicitChartData
        (P ι hx))

/-- The checked OS45 determinant-regular subpatch becomes an oriented real
environment from the pointwise real-compatible full-frame chart producer. -/
theorem os45Figure24_checkedRealPatch_fullFrameOrientedEnvironmentSubpatch_of_realCompatibleImplicitChartProducer
    {d : ℕ} [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    (hn : d + 1 ≤ n)
    (π : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (E0 : Set (Fin n → Fin (d + 1) → ℝ))
    (hE0 : IsOS45Figure24CheckedRealPatch (d := d) n π i hi E0)
    (P : SourceFullFrameRealCompatibleImplicitChartProducer d n) :
    ∃ E : Set (Fin n → Fin (d + 1) → ℝ),
      E ⊆ E0 ∧
      IsOpen E ∧
      E.Nonempty ∧
      IsHWOrientedRealEnvironment d n
        {y | ∃ x ∈ E, y = fun k => x (π k)} :=
  os45Figure24_checkedRealPatch_fullFrameOrientedEnvironmentSubpatch_of_localCharts
    hd n hn π i hi E0 hE0
    (fun ι {_y} hy =>
      sourceOrientedLocalRealChartData_of_fullFrameRealCompatibleImplicitChartData
        (P ι hy))

/-- From the real-compatible full-frame chart producer, a checked OS45 real
patch contains a source-oriented distributional uniqueness subpatch. -/
theorem os45Figure24_checkedRealPatch_sourceOrientedDistributionalUniquenessSubpatch_of_realCompatibleImplicitChartProducer
    {d : ℕ} [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    (hn : d + 1 ≤ n)
    (π : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (E0 : Set (Fin n → Fin (d + 1) → ℝ))
    (hE0 : IsOS45Figure24CheckedRealPatch (d := d) n π i hi E0)
    (P : SourceFullFrameRealCompatibleImplicitChartProducer d n) :
    ∃ E : Set (Fin n → Fin (d + 1) → ℝ),
      E ⊆ E0 ∧
      IsOpen E ∧
      E.Nonempty ∧
      sourceOrientedDistributionalUniquenessPatch d n
        {y | ∃ x ∈ E, y = fun k => x (π k)} := by
  rcases
      os45Figure24_checkedRealPatch_fullFrameOrientedEnvironmentSubpatch_of_realCompatibleImplicitChartProducer
        hd n hn π i hi E0 hE0 P with
    ⟨E, hE_sub, hE_open, hE_ne, hEnv⟩
  exact
    ⟨E, hE_sub, hE_open, hE_ne,
      sourceOrientedDistributionalUniquenessPatch_of_HWRealEnvironment
        hd hn hEnv⟩

end BHW
