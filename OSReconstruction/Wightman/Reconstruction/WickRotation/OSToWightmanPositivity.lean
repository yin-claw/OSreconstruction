/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValueLimits
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup
import OSReconstruction.Wightman.Reconstruction.WickRotation.EuclideanPositiveTime
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43Codomain
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerTemperedness
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions
import OSReconstruction.SCV.PaleyWiener
import OSReconstruction.SCV.PartialFourierSpatial
import OSReconstruction.Mathlib429Compat
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Theorem 3 Positivity Infrastructure

This file contains the live production infrastructure for theorem 3
`bvt_W_positive`.

The endorsed route is now:
1. right-half-plane identity theorem,
2. single-component semigroup bridge on `{Re(z) > 0}`,
3. OS I Section 4.3 transport infrastructure,
4. quadratic identity on the transformed image,
5. final closure to arbitrary `BorchersSequence`.

The old same-test-function comparison route is false, even at `t = 0`, so this
file should not try to identify `WightmanInnerProduct (bvt_W ...)` with
`OSInnerProduct OS.S` on the same raw test data. The transport map is
essential.
-/

open scoped Topology Classical NNReal
open BigOperators Finset Complex
open MeasureTheory Filter
open OSReconstruction

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Part 1: Identity theorem on the right half-plane -/

/-- Two holomorphic functions on {Re(z) > 0} that agree on (0,∞) agree everywhere.
This is the standard identity theorem for connected domains. -/
theorem identity_theorem_right_halfplane
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re})
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re})
    (hagree : ∀ t : ℝ, 0 < t → f (t : ℂ) = g (t : ℂ)) :
    ∀ z : ℂ, 0 < z.re → f z = g z := by
  have hU_open : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hU_preconn : IsPreconnected {z : ℂ | 0 < z.re} := by
    apply Convex.isPreconnected
    intro z hz w hw a b ha hb hab
    simp only [Set.mem_setOf_eq] at hz hw ⊢
    calc (a • z + b • w).re = a * z.re + b * w.re := by
            simp [Complex.add_re]
      _ > 0 := by
        rcases ha.lt_or_eq with ha' | ha'
        · have : b * w.re ≥ 0 := mul_nonneg hb hw.le
          have : a * z.re > 0 := mul_pos ha' hz
          linarith
        · have hab' : b = 1 := by linarith
          simp [← ha', hab', hw]
  have hf_an : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re} := hf.analyticOnNhd hU_open
  have hg_an : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re} := hg.analyticOnNhd hU_open
  have h1_mem : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have hfg_an : AnalyticAt ℂ (f - g) 1 := (hf_an 1 h1_mem).sub (hg_an 1 h1_mem)
  have hfreq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, (f - g) z = 0 := by
    rw [Filter.Frequently]
    intro hev
    rw [Filter.Eventually] at hev
    rw [(nhdsWithin_basis_open 1 {(1 : ℂ)}ᶜ).mem_iff] at hev
    obtain ⟨u, ⟨h1u, hu_open⟩, hus⟩ := hev
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu_open 1 h1u
    have hmem : ((1 + ε / 2 : ℝ) : ℂ) ∈ u := by
      apply hball
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : ((1 + ε / 2 : ℝ) : ℂ) - 1 = ((ε / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hsub]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    have hne : ((1 + ε / 2 : ℝ) : ℂ) ≠ (1 : ℂ) := by
      intro heq
      have := congr_arg Complex.re heq
      simp at this; linarith [half_pos hε]
    have hzero : (f - g) ((1 + ε / 2 : ℝ) : ℂ) = 0 := by
      simp only [Pi.sub_apply, sub_eq_zero]; exact hagree (1 + ε / 2) (by linarith)
    exact hus ⟨hmem, hne⟩ hzero
  have hev : ∀ᶠ z in nhds (1 : ℂ), (f - g) z = 0 :=
    hfg_an.frequently_zero_iff_eventually_zero.mp hfreq
  have hfg_an_on : AnalyticOnNhd ℂ (f - g) {z : ℂ | 0 < z.re} := hf_an.sub hg_an
  have heqOn : Set.EqOn (f - g) 0 {z : ℂ | 0 < z.re} :=
    hfg_an_on.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_preconn h1_mem hev
  intro z hz
  have := heqOn hz
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

private theorem identity_theorem_upperHalfPlane
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f SCV.upperHalfPlane)
    (hg : DifferentiableOn ℂ g SCV.upperHalfPlane)
    (hagree : ∀ η : ℝ, 0 < η → f (η * Complex.I) = g (η * Complex.I)) :
    ∀ z : ℂ, 0 < z.im → f z = g z := by
  let fR : ℂ → ℂ := fun w => f (Complex.I * w)
  let gR : ℂ → ℂ := fun w => g (Complex.I * w)
  have hmap : Set.MapsTo (fun w : ℂ => Complex.I * w)
      {z : ℂ | 0 < z.re} SCV.upperHalfPlane := by
    intro z hz
    simpa [SCV.upperHalfPlane, Complex.mul_im] using hz
  have hmul :
      DifferentiableOn ℂ (fun w : ℂ => Complex.I * w)
        {z : ℂ | 0 < z.re} := by
    intro z hz
    simpa using
      (((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z).const_mul
        Complex.I).differentiableWithinAt)
  have hfR : DifferentiableOn ℂ fR {z : ℂ | 0 < z.re} := hf.comp hmul hmap
  have hgR : DifferentiableOn ℂ gR {z : ℂ | 0 < z.re} := hg.comp hmul hmap
  have hagreeR : ∀ t : ℝ, 0 < t → fR (t : ℂ) = gR (t : ℂ) := by
    intro t ht
    simpa [fR, gR, mul_comm] using hagree t ht
  intro z hz
  have hzR : 0 < (-Complex.I * z).re := by
    simpa [Complex.mul_re] using hz
  have hmain :=
    identity_theorem_right_halfplane fR gR hfR hgR hagreeR (-Complex.I * z) hzR
  dsimp [fR, gR] at hmain
  convert hmain using 1 <;> ring_nf <;> simp

/-! ## Part 2: Semigroup bridge for single-component pairs -/

/-- For single-component positive-time Borchers sequences, the two holomorphic
extensions `bvt_singleSplit_xiShiftHolomorphicValue` and
`OSInnerProductTimeShiftHolomorphicValue` agree on the entire right half-plane.

Both are holomorphic on {Re(z) > 0} and both equal OS.S at real t > 0. -/
theorem bvt_xiShift_eq_osInnerProduct_holomorphicValue_single
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (z : ℂ) (hz : 0 < z.re) :
    bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact z =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) z := by
  apply identity_theorem_right_halfplane
  · exact differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact
  · exact OSInnerProductTimeShiftHolomorphicValue_differentiableOn
      (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n f hf_ord)
      (PositiveTimeBorchersSequence.single m g hg_ord)
  · intro t ht
    -- LHS at real t > 0: equals OS.S(n+m)(osConj f ⊗ timeShift_t g)
    rw [bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift
      (d := d) (OS := OS) (lgc := lgc) hm f hf_ord hf_compact g hg_ord hg_compact t ht]
    -- RHS at real t > 0: equals sum over k of OS.S(k+m)(...)
    rw [OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single
      (d := d) (OS := OS) (lgc := lgc)
      (F := PositiveTimeBorchersSequence.single n f hf_ord)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact) (t := t) ht]
    -- The sum collapses: single n f has bound = n, so only k = n contributes
    simp only [PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single_bound]
    rw [Finset.sum_range_succ]
    simp only [BorchersSequence.single_funcs_eq]
    have hvanish :
        ∑ k ∈ Finset.range n,
          OS.S (k + m) (ZeroDiagonalSchwartz.ofClassical
            (((BorchersSequence.single n f).funcs k).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk_ne : k ≠ n := by
        have := Finset.mem_range.mp hk; omega
      rw [BorchersSequence.single_funcs_ne hk_ne]
      have : (0 : SchwartzNPoint d k).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) t g) = 0 := by
        simp [SchwartzNPoint.osConjTensorProduct, SchwartzNPoint.osConj_zero,
          SchwartzMap.tensorProduct_zero_left]
      rw [this]
      rw [ZeroDiagonalSchwartz.ofClassical_zero]
      exact (OS.E0_linear (k + m)).map_zero
    rw [hvanish, zero_add]
  · exact hz

/-- Rotated-horizontal-line form of the single-component semigroup bridge:
inside the Route `3b-II` boundary-value pairing, the rotated OS holomorphic
matrix element can be rewritten pointwise as the already-built
`singleSplit_xiShift` holomorphic trace.

This is not the missing Phase C' identity. It only transfers the **OS side** of
the horizontal-line boundary-value integral to the single-split holomorphic
supplier on the same right-half-plane point `-I * (x + η I)`. The remaining
frontier is the boundary-value identification of that trace with the Wightman
time-shift functional. -/
private theorem
    integral_rotated_OSInnerProductTimeShiftHolomorphicValue_eq_singleSplit_xiShiftHolomorphicValue_fourierTransform
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (χ : SchwartzMap ℝ ℂ) {η : ℝ} (hη : 0 < η) :
    (∫ x : ℝ,
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord)
          (-Complex.I * ((x : ℂ) + η * Complex.I)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) x)
      =
    ∫ x : ℝ,
      bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact
          (-Complex.I * ((x : ℂ) + η * Complex.I)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) x := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  have hz : 0 < (-Complex.I * ((x : ℂ) + η * Complex.I)).re := by
    ring_nf
    simpa using hη
  have hpt :=
    bvt_xiShift_eq_osInnerProduct_holomorphicValue_single
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
      (z := -Complex.I * ((x : ℂ) + η * Complex.I)) hz
  exact congrArg (fun z => z * (SchwartzMap.fourierTransformCLM ℂ χ) x) hpt.symm

/-- Distributional boundary value of the rotated `singleSplit_xiShift`
holomorphic trace on the real axis of the upper half-plane.

This is the semigroup-side boundary-value theorem transferred through Package
B. It gives the `singleSplit` trace the same spectral boundary functional as
the rotated OS holomorphic matrix element. The remaining Phase C' work is to
identify this boundary functional with the canonical Wightman time-shift
boundary functional. -/
private theorem
    tendsto_bvt_singleSplit_xiShiftHolomorphicValue_rotated_boundaryValue_fourierTransform
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (χ : SchwartzMap ℝ ℂ) :
    Filter.Tendsto
      (fun η : ℝ =>
        ∫ x : ℝ,
          bvt_singleSplit_xiShiftHolomorphicValue
              (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (selfAdjointSpectralBoundaryValueOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
          (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
          χ)) := by
  have hOS :=
    tendsto_rotated_OSInnerProductTimeShiftHolomorphicValue_boundaryValue_fourierTransform
      (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n f hf_ord)
      (PositiveTimeBorchersSequence.single m g hg_ord) χ
  have hEq :
      (fun η : ℝ =>
        ∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single m g hg_ord)
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun η : ℝ =>
        ∫ x : ℝ,
          bvt_singleSplit_xiShiftHolomorphicValue
              (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact
      integral_rotated_OSInnerProductTimeShiftHolomorphicValue_eq_singleSplit_xiShiftHolomorphicValue_fourierTransform
        (d := d) (OS := OS) (lgc := lgc) (hm := hm)
        (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
        (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
        (χ := χ) hη
  exact Filter.Tendsto.congr' hEq hOS

/-! ## Part 3: Sorry 3 — Wightman positive-definiteness

CRITICAL ROUTE CORRECTION (Entry #277):

The former Package C (`hschw`) — equating `OS.S(osConj f ⊗ timeShift_t g)` with
`bvt_W(conj f ⊗ timeShift_t g)` — is MATHEMATICALLY FALSE.

Reason: `timeShiftSchwartzNPoint t` is a real time translation. On the OS/Euclidean
side it corresponds to the contraction semigroup `e^{-tH}` (decaying). On the
Wightman/Minkowski side it corresponds to the unitary group `e^{itH}` (oscillating).
The equation `e^{-tH} = e^{itH}` is false for nontrivial H.

The entire production reduction chain through `hschw` consumes a false hypothesis.

The correct route is OS I Section 4.3: construct the transport map
`u : BorchersSequence d → OSHilbertSpace OS` via Fourier-Laplace transform,
and prove `W(f* × f) = ‖u(f)‖²_H ≥ 0` directly. This does NOT go through
any time-shifted Schwinger-vs-Wightman comparison. -/

namespace EuclideanPositiveTimeComponent

variable {n : ℕ}

/-- A positive-time component viewed as the corresponding single positive-time
Borchers sequence. This is the Euclidean-side input object whose image under
the eventual Section 4.3 transport map will be compared against the Wightman
quadratic form. -/
def toPositiveTimeSingle
    (f : EuclideanPositiveTimeComponent d n) :
    PositiveTimeBorchersSequence d :=
  PositiveTimeBorchersSequence.single n f.1 f.2

end EuclideanPositiveTimeComponent

/-! ### Ordered head-gap frozen-time helpers -/

/-- The head time coordinate used when the OS I one-variable time interchange
isolates the first point of a positive-time block. -/
private def headSliceIndex {q : ℕ} (hq : 0 < q) : Fin q :=
  ⟨0, hq⟩

/-- Frozen background times relative to the head coordinate of an ordered
positive-time block. These are nonnegative away from the head, by ordering. -/
private def orderedHeadGapTimes {q : ℕ} (hq : 0 < q)
    (x : NPointDomain d q) : Fin q → ℝ :=
  fun i => x i 0 - x (headSliceIndex hq) 0

set_option linter.unusedSectionVars false in
/-- In an ordered positive-time block, every non-head time is after the head
time, so the head-gap frozen background times are nonnegative. -/
private theorem orderedHeadGapTimes_nonneg_of_orderedPositive
    {q : ℕ} (hq : 0 < q)
    {x : NPointDomain d q}
    (hx : x ∈ OrderedPositiveTimeRegion d q) :
    ∀ i : Fin q, i ≠ headSliceIndex hq →
      0 ≤ orderedHeadGapTimes (d := d) hq x i := by
  intro i hi
  have h0i : headSliceIndex hq < i := by
    rw [Fin.lt_def, headSliceIndex]
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hi (Fin.ext hzero))
  have hlt : x (headSliceIndex hq) 0 < x i 0 :=
    (hx (headSliceIndex hq)).2 i h0i
  dsimp [orderedHeadGapTimes]
  linarith

/-! ### One-point positive-time slice support -/

/-- A one-point Euclidean Schwartz test supported in strictly positive time has
every fixed-spatial slice supported in nonnegative time. This is the exact
support input needed by the one-variable Section 4.3 Paley-Wiener supplier. -/
private theorem tsupport_spatialSlice_subset_Ici_of_timePositive
    (f : SchwartzSpacetime d)
    (hf_pos : tsupport (f : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (y : Fin d → ℝ) :
    tsupport (fun t : ℝ => f (Fin.cons t y)) ⊆ Set.Ici 0 := by
  intro t ht
  by_contra ht_neg
  have ht_lt : t < 0 := by
    simpa [Set.mem_Ici, not_le] using ht_neg
  have ht_not : t ∉ tsupport (fun s : ℝ => f (Fin.cons s y)) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    have hball : Metric.ball t (-t / 2) ∈ 𝓝 t := by
      apply Metric.ball_mem_nhds
      linarith
    filter_upwards [hball] with s hs
    have hsabs : |s - t| < -t / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hs
    have hs_lt : s < 0 := by
      linarith [(abs_lt.mp hsabs).2, ht_lt]
    have hs_not_mem : (Fin.cons s y : SpacetimeDim d) ∉ tsupport (f : SpacetimeDim d → ℂ) := by
      intro hs_mem
      have hs_pos : 0 < (Fin.cons s y : SpacetimeDim d) 0 := hf_pos hs_mem
      have : 0 < s := by simpa using hs_pos
      linarith
    exact image_eq_zero_of_notMem_tsupport hs_not_mem
  exact ht_not ht

/-! ### n-point ordered-positive slice support for branch `3b` -/

/-- If one chosen time coordinate is negative, the time/spatial reindexing of
an ordered-positive-time Euclidean test vanishes at that point. -/
private theorem nPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (η : EuclideanSpace ℝ (Fin n × Fin d))
    {s : ℝ} (hs : s < 0) :
    OSReconstruction.nPointTimeSpatialSchwartzCLE (d := d) (n := n) f.1
      (Function.update t r s, η) = 0 := by
  have hnot_ord :
      (OSReconstruction.nPointTimeSpatialCLE (d := d) n).symm (Function.update t r s, η) ∉
        OrderedPositiveTimeRegion d n := by
    intro hmem
    have htime : 0 <
        (((OSReconstruction.nPointTimeSpatialCLE (d := d) n).symm
          (Function.update t r s, η)) r 0) := (hmem r).1
    have hEq :
        (((OSReconstruction.nPointTimeSpatialCLE (d := d) n).symm
          (Function.update t r s, η)) r 0) = s := by
      simp [OSReconstruction.nPointTimeSpatialCLE]
    linarith
  have hnot_supp :
      (OSReconstruction.nPointTimeSpatialCLE (d := d) n).symm (Function.update t r s, η) ∉
        tsupport (f.1 : NPointDomain d n → ℂ) := by
    intro hx
    exact hnot_ord (f.2 hx)
  change f.1 ((OSReconstruction.nPointTimeSpatialCLE (d := d) n).symm
    (Function.update t r s, η)) = 0
  simpa using image_eq_zero_of_notMem_tsupport hnot_supp

/-- Negative time in one chosen coordinate forces the branch-`3b` partial
spatial Fourier transform to vanish at that point. -/
private theorem partialFourierSpatial_fun_eq_zero_of_neg_time
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {s : ℝ} (hs : s < 0) :
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1
      (Function.update t r s, ξ) = 0 := by
  rw [OSReconstruction.partialFourierSpatial_fun_eq_integral]
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards with η
  simp [nPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time (f := f) (r := r)
    (t := t) (η := η) hs]

/-- Fixing the spatial momentum block and all but one time coordinate, the
branch-`3b` partial spatial Fourier transform of an ordered-positive-time
Euclidean test is supported in `t ≥ 0` in the remaining time variable. This is
the exact support input needed for the one-variable Section 4.3 supplier. -/
private theorem tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    tsupport (fun s : ℝ =>
      OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1
        (Function.update t r s, ξ)) ⊆ Set.Ici 0 := by
  intro s hs
  by_contra hs_neg
  have hs_lt : s < 0 := by
    simpa [Set.mem_Ici, not_le] using hs_neg
  have hs_not :
      s ∉ tsupport (fun s' : ℝ =>
        OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1
          (Function.update t r s', ξ)) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    have hball : Metric.ball s (-s / 2) ∈ 𝓝 s := by
      apply Metric.ball_mem_nhds
      linarith
    filter_upwards [hball] with s' hs'
    have hsabs : |s' - s| < -s / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hs'
    have hs'_lt : s' < 0 := by
      linarith [(abs_lt.mp hsabs).2, hs_lt]
    exact partialFourierSpatial_fun_eq_zero_of_neg_time
      (f := f) r t ξ hs'_lt
  exact hs_not hs

/-- A branch-`3b` one-variable time slice is continuous. -/
private theorem continuous_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Continuous (fun s : ℝ =>
      OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1
        (Function.update t r s, ξ)) := by
  have hupdate : Continuous (fun s : ℝ => (Function.update t r s, ξ)) := by
    refine Continuous.prodMk ?_ continuous_const
    refine continuous_pi ?_
    intro i
    by_cases hi : i = r
    · subst hi
      simpa using continuous_id
    · simpa [Function.update, hi] using (continuous_const : Continuous fun _ : ℝ => t i)
  exact (OSReconstruction.continuous_partialFourierSpatial_fun (d := d) (n := n) f.1).comp hupdate

/-- A branch-`3b` one-variable time slice has polynomial growth on the real
line. In fact it is uniformly bounded, by the companion-file partial Fourier
estimate. -/
private theorem hasPolynomialGrowthOnLine_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    SCV.HasPolynomialGrowthOnLine (fun s : ℝ =>
      OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1
        (Function.update t r s, ξ)) := by
  rcases OSReconstruction.exists_norm_bound_partialFourierSpatial_fun (d := d) (n := n) f.1 with
    ⟨C, hC, hbound⟩
  refine ⟨C + 1, 0, by positivity, ?_⟩
  intro s
  calc
    ‖OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1
        (Function.update t r s, ξ)‖ ≤ C := hbound (Function.update t r s, ξ)
    _ ≤ (C + 1) * (1 + |s|) ^ (0 : ℕ) := by
      simp

/-- Every fixed time-coordinate polynomial weight is uniformly bounded on a
branch-`3b` one-variable time slice. This is the first weighted bound toward
proving that the slice itself is a Schwartz function of the chosen time
variable. -/
private theorem exists_timePow_norm_bound_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ,
        ‖((s : ℂ) ^ k) *
          OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r s, ξ)‖ ≤ C := by
  rcases OSReconstruction.exists_timeCoordPow_norm_bound_partialFourierSpatial_fun
      (d := d) (n := n) f r k with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro s
  simpa using hbound (Function.update t r s, ξ)

/-- The ordinary one-variable derivative of a branch-`3b` time slice is the
same transported Schwartz input that appears in the ambient time-direction
`fderiv` theorem, specialized to the update curve in the chosen coordinate. -/
private theorem deriv_partialFourierSpatial_timeSlice_eq_transport
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (s : ℝ) :
    deriv
      (fun u : ℝ =>
        OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
          (Function.update t r u, ξ))
      s =
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
      ((OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
        (LineDeriv.lineDerivOp
          ((0 : EuclideanSpace ℝ (Fin n × Fin d)),
            Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))
          (OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
      (Function.update t r s, ξ) := by
  have hcomp :
      HasDerivAt
        (fun u : ℝ =>
          OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r u, ξ))
        ((fderiv ℝ
            (fun u : Fin n → ℝ =>
              OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f (u, ξ))
            (Function.update t r s))
          (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ)))
        s := by
    simpa using
      (((OSReconstruction.differentiableAt_partialFourierSpatial_fun_time
          (d := d) (n := n) f ξ (Function.update t r s)).hasFDerivAt).comp s
        (hasDerivAt_update t r s).hasFDerivAt).hasDerivAt
  calc
    deriv
        (fun u : ℝ =>
          OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r u, ξ))
        s
      =
        ((fderiv ℝ
            (fun u : Fin n → ℝ =>
              OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f (u, ξ))
            (Function.update t r s))
          (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))) := hcomp.deriv
    _ = OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
          ((OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
            (LineDeriv.lineDerivOp
              ((0 : EuclideanSpace ℝ (Fin n × Fin d)),
                Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))
              (OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
          (Function.update t r s, ξ) := by
            simpa using
              OSReconstruction.fderiv_partialFourierSpatial_fun_time_apply_eq_transport
                (d := d) (n := n) f ξ (Function.update t r s)
                (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))

/-- The first derivative of a branch-`3b` time slice also satisfies every
fixed time-coordinate polynomial bound. This is the first honest `n = 1` step
toward proving the slice is Schwartz in the chosen time variable. -/
private theorem exists_timePow_norm_bound_deriv_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ,
        ‖((s : ℂ) ^ k) *
          deriv
            (fun u : ℝ =>
              OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
                (Function.update t r u, ξ))
            s‖ ≤ C := by
  let g : SchwartzNPoint d n :=
    ((OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
      (LineDeriv.lineDerivOp
        ((0 : EuclideanSpace ℝ (Fin n × Fin d)),
          Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))
        (OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
  rcases OSReconstruction.exists_timeCoordPow_norm_bound_partialFourierSpatial_fun
      (d := d) (n := n) g r k with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro s
  rw [deriv_partialFourierSpatial_timeSlice_eq_transport (f := f) r t ξ s]
  simpa [g] using hbound (Function.update t r s, ξ)

/-- The Schwartz-input transport corresponding to one ordinary derivative of
the branch-`3b` time slice in the chosen coordinate. -/
private noncomputable def timeDerivTransportInput
    {n : ℕ} (r : Fin n) (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  ((OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
    (LineDeriv.lineDerivOp
      ((0 : EuclideanSpace ℝ (Fin n × Fin d)),
        Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))
      (OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))

/-- Repeated time differentiation of the branch-`3b` slice corresponds to
repeated application of `timeDerivTransportInput` on the Schwartz input. -/
private noncomputable def iteratedTimeDerivTransport
    {n : ℕ} (r : Fin n) (m : ℕ) (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  (timeDerivTransportInput (d := d) (n := n) r)^[m] f

/-- The `m`-th iterated ordinary derivative of the branch-`3b` time slice is
again the same slice, but with the input replaced by the recursively
transported Schwartz datum. -/
private theorem iteratedDeriv_partialFourierSpatial_timeSlice_eq_transport
    {n : ℕ}
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ∀ (m : ℕ) (f : SchwartzNPoint d n) (s : ℝ),
      iteratedDeriv m
        (fun u : ℝ =>
          OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r u, ξ))
        s =
      OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
        (iteratedTimeDerivTransport (d := d) (n := n) r m f)
        (Function.update t r s, ξ) := by
  intro m
  induction m with
  | zero =>
      intro f s
      simp [iteratedTimeDerivTransport]
  | succ m ih =>
      intro f s
      rw [iteratedDeriv_succ']
      have hArg :
          iteratedDeriv m
            (deriv
              (fun u : ℝ =>
                OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
                  (Function.update t r u, ξ)))
            s =
          iteratedDeriv m
            (fun u : ℝ =>
              OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
                (timeDerivTransportInput (d := d) (n := n) r f)
                (Function.update t r u, ξ))
            s := by
        congr 1
        ext u
        simpa [timeDerivTransportInput] using
          deriv_partialFourierSpatial_timeSlice_eq_transport
            (d := d) (n := n) (f := f) r t ξ u
      calc
        iteratedDeriv m
            (deriv
              (fun u : ℝ =>
                OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
                  (Function.update t r u, ξ)))
            s
          =
            iteratedDeriv m
              (fun u : ℝ =>
                OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
                  (timeDerivTransportInput (d := d) (n := n) r f)
                  (Function.update t r u, ξ))
              s := hArg
        _ = OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
              (iteratedTimeDerivTransport (d := d) (n := n) r (m + 1) f)
              (Function.update t r s, ξ) := by
              simpa [iteratedTimeDerivTransport, timeDerivTransportInput,
                Function.iterate_succ_apply] using
                ih (timeDerivTransportInput (d := d) (n := n) r f) s

/-- Every iterated ordinary derivative of the branch-`3b` time slice satisfies
every fixed polynomial time-weight bound. -/
private theorem exists_timePow_norm_bound_iteratedDeriv_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ,
        ‖((s : ℂ) ^ k) *
          iteratedDeriv m
            (fun u : ℝ =>
              OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
                (Function.update t r u, ξ))
            s‖ ≤ C := by
  rcases exists_timePow_norm_bound_partialFourierSpatial_timeSlice
      (d := d) (n := n)
      (f := iteratedTimeDerivTransport (d := d) (n := n) r m f)
      r t ξ k with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro s
  rw [iteratedDeriv_partialFourierSpatial_timeSlice_eq_transport
      (d := d) (n := n) r t ξ m f s]
  simpa using hbound s

/-- Every branch-`3b` time slice is differentiable, with derivative given by
the transported Schwartz input from `timeDerivTransportInput`. -/
private theorem differentiable_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Differentiable ℝ
      (fun s : ℝ =>
        OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
          (Function.update t r s, ξ)) := by
  intro s
  have hcomp :
      HasDerivAt
        (fun u : ℝ =>
          OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r u, ξ))
        (OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
          (timeDerivTransportInput (d := d) (n := n) r f)
          (Function.update t r s, ξ))
        s := by
    have hbase :
        HasDerivAt
          (fun u : ℝ =>
            OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
              (Function.update t r u, ξ))
          ((fderiv ℝ
              (fun u : Fin n → ℝ =>
              OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f (u, ξ))
              (Function.update t r s))
            (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ)))
        s := by
      simpa using
        (((OSReconstruction.differentiableAt_partialFourierSpatial_fun_time
            (d := d) (n := n) f ξ (Function.update t r s)).hasFDerivAt).comp s
          (hasDerivAt_update t r s).hasFDerivAt).hasDerivAt
    convert hbase using 1
    simpa [timeDerivTransportInput] using
      (OSReconstruction.fderiv_partialFourierSpatial_fun_time_apply_eq_transport
        (d := d) (n := n) f ξ (Function.update t r s)
        (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))).symm
  exact hcomp.differentiableAt

/-- The branch-`3b` time slice is a Schwartz function of the chosen time
variable. -/
private theorem contDiff_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ =>
        OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
          (Function.update t r s, ξ)) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m hm
  have hEq :
      iteratedDeriv m
        (fun s : ℝ =>
          OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r s, ξ)) =
      fun s : ℝ =>
        OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
          (iteratedTimeDerivTransport (d := d) (n := n) r m f)
          (Function.update t r s, ξ) := by
    ext s
    simpa using
      iteratedDeriv_partialFourierSpatial_timeSlice_eq_transport
        (d := d) (n := n) r t ξ m f s
  rw [hEq]
  exact differentiable_partialFourierSpatial_timeSlice
    (d := d) (n := n)
    (f := iteratedTimeDerivTransport (d := d) (n := n) r m f) r t ξ

/-- The branch-`3b` time slice, packaged honestly as a Schwartz function in the
chosen time variable. -/
noncomputable def partialFourierSpatial_timeSliceSchwartz
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    SchwartzMap ℝ ℂ where
  toFun := fun s : ℝ =>
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
      (Function.update t r s, ξ)
  smooth' := contDiff_partialFourierSpatial_timeSlice (d := d) (n := n) f r t ξ
  decay' := by
    intro k m
    rcases exists_timePow_norm_bound_iteratedDeriv_partialFourierSpatial_timeSlice
        (d := d) (n := n) f r t ξ k m with ⟨C, _, hC⟩
    refine ⟨C, ?_⟩
    intro s
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hC s

/-! ### One-variable Section 4.3 Fourier-Laplace supplier -/

/-- The one-variable complex Laplace transform used by the Section 4.3
Fourier-Laplace transport. -/
private noncomputable def complexLaplaceTransform
    (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-s * (t : ℂ)) * f t

private theorem complexCoord_hasTemperateGrowth :
    (fun t : ℝ => (t : ℂ)).HasTemperateGrowth := by
  fun_prop

private theorem complexNegCoordPow_hasTemperateGrowth (N : ℕ) :
    (fun t : ℝ => (-(t : ℂ)) ^ N).HasTemperateGrowth := by
  fun_prop

private theorem complexLaplaceTransform_integrable_of_nonneg_re
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    (s : ℂ) (hs : 0 ≤ s.re) :
    Integrable (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * f t) := by
  apply MeasureTheory.Integrable.mono f.integrable
  · exact ((Complex.continuous_exp.comp
        ((continuous_const : Continuous (fun _ : ℝ => -s)).mul Complex.continuous_ofReal)).mul
        f.continuous).aestronglyMeasurable
  · filter_upwards with t
    simp only [norm_mul, Complex.norm_exp]
    by_cases ht : (f : ℝ → ℂ) t = 0
    · simp [ht]
    · have ht_supp : t ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ ht
      have ht_nonneg : 0 ≤ t := Set.mem_Ici.mp (hf_supp ht_supp)
      have hre : (-s * (t : ℂ)).re = -(s.re * t) := by
        simp [Complex.mul_re]
      rw [hre]
      have hexp : Real.exp (-(s.re * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      exact mul_le_of_le_one_left (norm_nonneg _) hexp

private theorem weightedSchwartz_integrable
    (f : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => (t : ℂ) * f t) := by
  convert
    ((SchwartzMap.smulLeftCLM (F := ℂ) (g := fun t : ℝ => (t : ℂ)) f).integrable
      (μ := MeasureTheory.volume)) using 1
  ext t
  rw [SchwartzMap.smulLeftCLM_apply_apply (F := ℂ) complexCoord_hasTemperateGrowth]
  simp [smul_eq_mul]

private noncomputable def weightedNegCoordPowSchwartz
    (N : ℕ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM (F := ℂ) (g := fun t : ℝ => (-(t : ℂ)) ^ N) f

private theorem weightedNegCoordPowSchwartz_apply
    (N : ℕ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    weightedNegCoordPowSchwartz N f t = (-(t : ℂ)) ^ N * f t := by
  rw [weightedNegCoordPowSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply (F := ℂ) (complexNegCoordPow_hasTemperateGrowth N)]
  simp [smul_eq_mul]

private theorem weightedNegCoordPowSchwartz_support
    (N : ℕ) (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    tsupport (weightedNegCoordPowSchwartz N f : ℝ → ℂ) ⊆ Set.Ici 0 := by
  exact (SchwartzMap.tsupport_smulLeftCLM_subset (g := fun t : ℝ => (-(t : ℂ)) ^ N) (f := f)).trans
    (Set.inter_subset_left.trans hf_supp)

private theorem weightedNegCoordPowSchwartz_integrable
    (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => (-(t : ℂ)) ^ N * f t) := by
  convert (weightedNegCoordPowSchwartz N f).integrable (μ := MeasureTheory.volume) using 1
  ext t
  rw [weightedNegCoordPowSchwartz_apply]

private theorem re_mem_rightHalfPlane_of_mem_ball
    {s s₀ : ℂ} (hs₀ : 0 < s₀.re)
    (hs : s ∈ Metric.ball s₀ (s₀.re / 2)) :
    0 < s.re := by
  have hs_norm : ‖s - s₀‖ < s₀.re / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hs
  have h_re_lower : -(‖s - s₀‖) ≤ (s - s₀).re := by
    have habs : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm (s - s₀)
    exact (abs_le.mp habs).1
  have hdelta : -(s₀.re / 2) < (s - s₀).re := by
    linarith
  have hs_eq : s.re = s₀.re + (s - s₀).re := by
    have : s = s₀ + (s - s₀) := by ring
    exact congrArg Complex.re this
  linarith

private theorem complexLaplaceKernel_hasDerivAt
    (t : ℝ) (s : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (-z * (t : ℂ)))
      ((-(t : ℂ)) * Complex.exp (-s * (t : ℂ))) s := by
  have hlin : HasDerivAt (fun z : ℂ => -z * (t : ℂ)) (-(t : ℂ)) s := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id s).neg).mul_const (t : ℂ))
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (Complex.hasDerivAt_exp (-s * (t : ℂ))).comp s hlin

private theorem complexLaplaceKernelDeriv_norm_le_weighted
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {s s₀ : ℂ} (hs₀ : 0 < s₀.re)
    (hs : s ∈ Metric.ball s₀ (s₀.re / 2))
    (t : ℝ) :
    ‖((-(t : ℂ)) * Complex.exp (-s * (t : ℂ)) * f t)‖ ≤ ‖((t : ℂ) * f t)‖ := by
  by_cases ht : (f : ℝ → ℂ) t = 0
  · simp [ht]
  · have ht_supp : t ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ ht
    have ht_nonneg : 0 ≤ t := Set.mem_Ici.mp (hf_supp ht_supp)
    have hs_re_nonneg : 0 ≤ s.re := le_of_lt (re_mem_rightHalfPlane_of_mem_ball hs₀ hs)
    have hre : (-s * (t : ℂ)).re = -(s.re * t) := by
      simp [Complex.mul_re]
    rw [norm_mul, norm_mul, Complex.norm_exp, hre]
    have hexp : Real.exp (-(s.re * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    calc
      ‖-(t : ℂ)‖ * Real.exp (-(s.re * t)) * ‖f t‖
          ≤ ‖-(t : ℂ)‖ * 1 * ‖f t‖ := by
            gcongr
      _ = ‖(t : ℂ)‖ * ‖f t‖ := by simp
      _ = ‖(t : ℂ) * f t‖ := by rw [norm_mul]

private theorem complexLaplaceTransform_hasDerivAt_rightHalfPlane
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    ∀ s₀ : ℂ, 0 < s₀.re →
      HasDerivAt (complexLaplaceTransform f)
        (∫ t : ℝ, (-(t : ℂ)) * Complex.exp (-s₀ * (t : ℂ)) * f t) s₀ := by
  intro s₀ hs₀
  let F : ℂ → ℝ → ℂ := fun s t => Complex.exp (-s * (t : ℂ)) * f t
  let F' : ℂ → ℝ → ℂ := fun s t => (-(t : ℂ)) * Complex.exp (-s * (t : ℂ)) * f t
  let bound : ℝ → ℝ := fun t => ‖(t : ℂ) * f t‖
  have hs_ball : Metric.ball s₀ (s₀.re / 2) ∈ nhds s₀ := Metric.ball_mem_nhds s₀ (half_pos hs₀)
  have h :
      HasDerivAt (fun s => ∫ t, F s t) (∫ t, F' s₀ t) s₀ :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := s₀) (s := Metric.ball s₀ (s₀.re / 2))
    (bound := bound)
    hs_ball
    (Filter.Eventually.of_forall (fun s =>
      ((Complex.continuous_exp.comp
        ((continuous_const : Continuous (fun _ : ℝ => -s)).mul Complex.continuous_ofReal)).mul
        f.continuous).aestronglyMeasurable))
    (complexLaplaceTransform_integrable_of_nonneg_re f hf_supp s₀ hs₀.le)
    (((Complex.continuous_ofReal.neg.mul
        (Complex.continuous_exp.comp
          ((continuous_const : Continuous (fun _ : ℝ => -s₀)).mul Complex.continuous_ofReal))).mul
        f.continuous).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t s hs =>
      complexLaplaceKernelDeriv_norm_le_weighted f hf_supp hs₀ hs t))
    ((weightedSchwartz_integrable f).norm)
    (Filter.Eventually.of_forall (fun t s _ => by
      simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using
        ((complexLaplaceKernel_hasDerivAt t s).mul_const (f t))))
    ).2
  change HasDerivAt (fun s => ∫ t : ℝ, Complex.exp (-s * (t : ℂ)) * f t)
    (∫ t : ℝ, (-(t : ℂ)) * Complex.exp (-s₀ * (t : ℂ)) * f t) s₀
  simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using h

private theorem complexLaplaceTransform_real_hasDerivAt
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    HasDerivAt (fun s : ℝ => complexLaplaceTransform f (s : ℂ))
      (∫ t : ℝ, (-(t : ℂ)) * Complex.exp (-((s₀ : ℂ)) * (t : ℂ)) * f t) s₀ := by
  simpa using
    (complexLaplaceTransform_hasDerivAt_rightHalfPlane f hf_supp (s₀ : ℂ) (by simpa using hs₀)).comp_ofReal

private theorem complexLaplaceTransform_real_differentiableOn
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    DifferentiableOn ℝ (fun s : ℝ => complexLaplaceTransform f (s : ℂ)) (Set.Ioi 0) := by
  intro s hs
  exact (complexLaplaceTransform_real_hasDerivAt f hf_supp hs).differentiableAt.differentiableWithinAt

private theorem complexLaplaceTransform_real_hasDerivAt_weighted
    (N : ℕ)
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    HasDerivAt
      (fun s : ℝ => complexLaplaceTransform (weightedNegCoordPowSchwartz N f) (s : ℂ))
      (∫ t : ℝ, (-(t : ℂ)) ^ (N + 1) * Complex.exp (-((s₀ : ℂ)) * (t : ℂ)) * f t) s₀ := by
  have hbase :=
    complexLaplaceTransform_real_hasDerivAt
      (weightedNegCoordPowSchwartz N f)
      (weightedNegCoordPowSchwartz_support N f hf_supp)
      hs₀
  convert hbase using 1
  congr with t
  rw [weightedNegCoordPowSchwartz_apply]
  ring_nf

private theorem complexLaplaceTransform_differentiableOn_rightHalfPlane
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    DifferentiableOn ℂ (complexLaplaceTransform f) {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (complexLaplaceTransform_hasDerivAt_rightHalfPlane f hf_supp s hs).differentiableAt.differentiableWithinAt

private theorem schwartz_eq_zero_of_neg
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {x : ℝ} (hx : x < 0) :
    f x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx_mem
  exact not_lt_of_ge (Set.mem_Ici.mp (hf_supp hx_mem)) hx

private theorem schwartz_zero_at_zero_of_support
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    f 0 = 0 := by
  have hseq : Tendsto (fun n : ℕ => (-(1 / ((n : ℝ) + 1)) : ℝ)) atTop (𝓝 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (𝓝 0)).neg
  have hcont :
      Tendsto (fun n : ℕ => f (-(1 / ((n : ℝ) + 1)) : ℝ)) atTop (𝓝 (f 0)) :=
    f.continuous.continuousAt.tendsto.comp hseq
  have hzero :
      Tendsto (fun n : ℕ => f (-(1 / ((n : ℝ) + 1)) : ℝ)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' <| Filter.Eventually.of_forall ?_
    intro n
    symm
    apply schwartz_eq_zero_of_neg f hf_supp
    have hpos : 0 < (1 / ((n : ℝ) + 1)) := by positivity
    linarith
  exact tendsto_nhds_unique hcont hzero

private theorem schwartz_tendsto_zero_nhdsWithin_right_of_support
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    Tendsto (fun x : ℝ => f x) (𝓝[>] 0) (𝓝 0) := by
  simpa [ContinuousWithinAt, schwartz_zero_at_zero_of_support f hf_supp] using
    (f.continuous.continuousAt.continuousWithinAt : ContinuousWithinAt f (Set.Ioi 0) 0)

private def iteratedDerivSchwartz : ℕ → SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ
  | 0, f => f
  | n + 1, f => SchwartzMap.derivCLM ℂ ℂ (iteratedDerivSchwartz n f)

private theorem tsupport_iteratedDerivSchwartz_subset
    (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    tsupport ((iteratedDerivSchwartz n f : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      tsupport (f : ℝ → ℂ) := by
  induction n with
  | zero =>
      simp [iteratedDerivSchwartz]
  | succ n ih =>
      simpa [iteratedDerivSchwartz] using
        ((SchwartzMap.tsupport_derivCLM_subset (𝕜 := ℂ) (F := ℂ) (iteratedDerivSchwartz n f)).trans ih)

private theorem complexLaplaceKernel_norm_le_self
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {s : ℂ} (hs : 0 ≤ s.re)
    (t : ℝ) :
    ‖Complex.exp (-s * (t : ℂ)) * f t‖ ≤ ‖f t‖ := by
  by_cases ht : (f : ℝ → ℂ) t = 0
  · simp [ht]
  · have ht_supp : t ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ ht
    have ht_nonneg : 0 ≤ t := Set.mem_Ici.mp (hf_supp ht_supp)
    have hre : (-s * (t : ℂ)).re = -(s.re * t) := by
      simp [Complex.mul_re]
    rw [norm_mul, Complex.norm_exp, hre]
    have hexp : Real.exp (-(s.re * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    calc
      Real.exp (-(s.re * t)) * ‖f t‖ ≤ 1 * ‖f t‖ := by
        gcongr
      _ = ‖f t‖ := by simp

private theorem complexLaplaceTransform_real_eq_inv_mul_deriv
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {s : ℝ} (hs : 0 < s) :
    complexLaplaceTransform f (s : ℂ)
      = (1 / (s : ℂ)) * complexLaplaceTransform (SchwartzMap.derivCLM ℂ ℂ f) (s : ℂ) := by
  have h_exp_integrable :
      IntegrableOn (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * deriv f x) (Set.Ioi 0) := by
    convert (complexLaplaceTransform_integrable_of_nonneg_re
      (SchwartzMap.derivCLM ℂ ℂ f)
      ((SchwartzMap.tsupport_derivCLM_subset (𝕜 := ℂ) (F := ℂ) f).trans hf_supp)
      (s : ℂ) hs.le).integrableOn using 1
    ext x
    rw [SchwartzMap.derivCLM_apply]
    congr 1
    ring_nf
  have h_deriv_exp_integrable :
      IntegrableOn
        (fun x : ℝ =>
          ((-(s : ℂ)) * Complex.exp (-((s : ℂ) * (x : ℂ)))) * f x) (Set.Ioi 0) := by
    have hint : Integrable (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * f x) := by
      simpa using complexLaplaceTransform_integrable_of_nonneg_re f hf_supp (s : ℂ) hs.le
    convert (hint.const_mul (-(s : ℂ))).integrableOn using 1
    ext x
    ring
  have h_zero :
      Tendsto (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * f x) (𝓝[>] 0) (𝓝 0) := by
    have h_exp :
        Tendsto (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ)))) (𝓝[>] 0) (𝓝 1) := by
      have hcont : Continuous fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) := by
        fun_prop
      simpa [ContinuousWithinAt] using
        (hcont.continuousAt.continuousWithinAt :
          ContinuousWithinAt (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ)))) (Set.Ioi 0) 0)
    have hf_zero' : Tendsto (fun x : ℝ => f x) (𝓝[>] 0) (𝓝 0) :=
      schwartz_tendsto_zero_nhdsWithin_right_of_support f hf_supp
    simpa using h_exp.mul hf_zero'
  have h_infty :
      Tendsto (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * f x) atTop (𝓝 0) := by
    have hf_top : Tendsto (fun x : ℝ => f x) atTop (𝓝 0) := by
      exact Tendsto.mono_left (SchwartzMap.tendsto_cocompact f) _root_.atTop_le_cocompact
    have hf_top_norm : Tendsto (fun x : ℝ => ‖f x‖) atTop (𝓝 0) := by
      simpa using (Tendsto.norm hf_top)
    have hexp_bdd :
        ∀ᶠ x : ℝ in atTop, ‖Complex.exp (-((s : ℂ) * (x : ℂ))) * f x‖ ≤ ‖f x‖ := by
      filter_upwards [Filter.eventually_ge_atTop 0] with x hx
      by_cases hfx : f x = 0
      · simp [hfx]
      · have hx_supp : x ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ hfx
        have hx_nonneg : 0 ≤ x := Set.mem_Ici.mp (hf_supp hx_supp)
        have hre : (-((s : ℂ) * (x : ℂ))).re = -(s * x) := by
          simp [Complex.mul_re]
        rw [norm_mul, Complex.norm_exp, hre]
        have hexp : Real.exp (-(s * x)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith)
        simpa using mul_le_of_le_one_left (norm_nonneg (f x)) hexp
    exact squeeze_zero_norm' hexp_bdd hf_top_norm
  have hparts :=
    MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      (a := 0)
      (u := fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))))
      (u' := fun x : ℝ => (-(s : ℂ)) * Complex.exp (-((s : ℂ) * (x : ℂ))))
      (v := fun x : ℝ => f x)
      (v' := fun x : ℝ => deriv f x)
      (fun x _ => by
        have hlin : HasDerivAt (fun t : ℝ => -((s : ℂ) * (t : ℂ))) (-(s : ℂ)) x := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (((Complex.ofRealCLM.hasDerivAt).const_mul (s : ℂ)).neg : HasDerivAt _ _ x)
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (Complex.hasDerivAt_exp (-((s : ℂ) * (x : ℂ)))).comp x hlin)
      (fun x _ => f.hasDerivAt x)
      h_exp_integrable
      h_deriv_exp_integrable
      h_zero
      h_infty
  let G : ℝ → ℂ := fun x => Complex.exp (-((s : ℂ) * (x : ℂ))) * f x
  have hIoi_eq :
      ∫ x : ℝ in Set.Ioi 0, G x
        = complexLaplaceTransform f (s : ℂ) := by
    have hGsupport : tsupport G ⊆ Set.Ici 0 := by
      have hbase :
          tsupport G ⊆ tsupport (fun x : ℝ => f x) := by
        simpa [G] using
          (tsupport_mul_subset_right :
            tsupport (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * f x) ⊆
              tsupport (fun x : ℝ => f x))
      exact hbase.trans hf_supp
    have hIci :
        ∫ x : ℝ in Set.Ici 0, G x = ∫ x : ℝ in tsupport G, G x := by
      apply MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ici hGsupport
      intro x hx
      exact image_eq_zero_of_notMem_tsupport hx.2
    calc
      ∫ x : ℝ in Set.Ioi 0, G x = ∫ x : ℝ in Set.Ici 0, G x := by
        rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]
      _ = ∫ x : ℝ in tsupport G, G x := hIci
      _ = ∫ x : ℝ, G x := MeasureTheory.setIntegral_tsupport (F := G) (ν := MeasureTheory.volume)
      _ = complexLaplaceTransform f (s : ℂ) := by
        simp [G, complexLaplaceTransform]
  let Gd : ℝ → ℂ := fun x => Complex.exp (-((s : ℂ) * (x : ℂ))) * deriv f x
  have hIoi_deriv_eq :
      ∫ x : ℝ in Set.Ioi 0, Gd x
        = complexLaplaceTransform (SchwartzMap.derivCLM ℂ ℂ f) (s : ℂ) := by
    have hGd_support : tsupport Gd ⊆ Set.Ici 0 := by
      simpa [Gd] using
        ((tsupport_mul_subset_right :
          tsupport (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * deriv f x) ⊆
            tsupport (fun x : ℝ => deriv f x)).trans
          ((SchwartzMap.tsupport_derivCLM_subset (𝕜 := ℂ) (F := ℂ) f).trans hf_supp))
    have hIci :
        ∫ x : ℝ in Set.Ici 0, Gd x = ∫ x : ℝ in tsupport Gd, Gd x := by
      apply MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ici hGd_support
      intro x hx
      exact image_eq_zero_of_notMem_tsupport hx.2
    calc
      ∫ x : ℝ in Set.Ioi 0, Gd x = ∫ x : ℝ in Set.Ici 0, Gd x := by
        rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]
      _ = ∫ x : ℝ in tsupport Gd, Gd x := hIci
      _ = ∫ x : ℝ, Gd x := MeasureTheory.setIntegral_tsupport (F := Gd) (ν := MeasureTheory.volume)
      _ = complexLaplaceTransform (SchwartzMap.derivCLM ℂ ℂ f) (s : ℂ) := by
        rw [complexLaplaceTransform]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with t
        dsimp [Gd]
        congr 1
        ring_nf
  have hs_ne : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hparts' :
      ∫ x : ℝ in Set.Ioi 0, Gd x = (s : ℂ) * ∫ x : ℝ in Set.Ioi 0, G x := by
    calc
      ∫ x : ℝ in Set.Ioi 0, Gd x
          = -∫ x : ℝ in Set.Ioi 0, ((-(s : ℂ)) * Complex.exp (-((s : ℂ) * (x : ℂ)))) * f x := by
              simpa [Gd] using hparts
      _ = -((-(s : ℂ)) * ∫ x : ℝ in Set.Ioi 0, G x) := by
            congr 1
            have hconst :
                ∫ x : ℝ in Set.Ioi 0, ((-(s : ℂ)) * Complex.exp (-((s : ℂ) * (x : ℂ)))) * f x
                  = (-(s : ℂ)) * ∫ x : ℝ in Set.Ioi 0, G x := by
                    simpa [G, mul_assoc] using
                      (MeasureTheory.integral_const_mul
                        (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
                        (-(s : ℂ))
                        (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * f x))
            exact hconst
      _ = (s : ℂ) * ∫ x : ℝ in Set.Ioi 0, G x := by ring
  calc
    complexLaplaceTransform f (s : ℂ)
        = ∫ x : ℝ in Set.Ioi 0, G x := by
            simp [hIoi_eq]
    _ = (1 / (s : ℂ)) * ∫ x : ℝ in Set.Ioi 0, Gd x := by
          calc
            ∫ x : ℝ in Set.Ioi 0, G x = (1 / (s : ℂ)) * ((s : ℂ) * ∫ x : ℝ in Set.Ioi 0, G x) := by
              field_simp [hs_ne]
            _ = (1 / (s : ℂ)) * ∫ x : ℝ in Set.Ioi 0, Gd x := by rw [hparts']
    _ = (1 / (s : ℂ)) * complexLaplaceTransform (SchwartzMap.derivCLM ℂ ℂ f) (s : ℂ) := by
          rw [hIoi_deriv_eq]

private theorem complexLaplaceTransform_real_eq_inv_pow_mul_iteratedDeriv
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {s : ℝ} (hs : 0 < s) (N : ℕ) :
    complexLaplaceTransform f (s : ℂ)
      = (1 / (s : ℂ)) ^ N * complexLaplaceTransform (iteratedDerivSchwartz N f) (s : ℂ) := by
  induction N with
  | zero =>
      simp [iteratedDerivSchwartz]
  | succ N ih =>
      have hN_supp :
          tsupport ((iteratedDerivSchwartz N f : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆ Set.Ici 0 :=
        (tsupport_iteratedDerivSchwartz_subset N f).trans hf_supp
      calc
        complexLaplaceTransform f (s : ℂ)
            = (1 / (s : ℂ)) ^ N * complexLaplaceTransform (iteratedDerivSchwartz N f) (s : ℂ) := ih
        _ = (1 / (s : ℂ)) ^ N *
              ((1 / (s : ℂ)) *
                complexLaplaceTransform (iteratedDerivSchwartz (N + 1) f) (s : ℂ)) := by
              rw [complexLaplaceTransform_real_eq_inv_mul_deriv (iteratedDerivSchwartz N f) hN_supp hs]
              simp [iteratedDerivSchwartz]
        _ = (1 / (s : ℂ)) ^ (N + 1) *
              complexLaplaceTransform (iteratedDerivSchwartz (N + 1) f) (s : ℂ) := by
              simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

private theorem complexLaplaceTransform_real_rapid_decay
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 ≤ s →
      ‖complexLaplaceTransform f (s : ℂ)‖ ≤ C * s ^ (-(N : ℤ)) := by
  let g : SchwartzMap ℝ ℂ := iteratedDerivSchwartz N f
  have hg_supp : tsupport (g : ℝ → ℂ) ⊆ Set.Ici 0 := by
    exact (tsupport_iteratedDerivSchwartz_subset N f).trans hf_supp
  let C0 : ℝ := ∫ t : ℝ, ‖g t‖
  refine ⟨C0 + 1, by positivity, ?_⟩
  intro s hs1
  have hs : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hIntExpNorm :
      Integrable (fun t : ℝ => ‖Complex.exp (-((s : ℂ) * (t : ℂ))) * g t‖) := by
    simpa only [neg_mul] using
      ((complexLaplaceTransform_integrable_of_nonneg_re g hg_supp (s : ℂ) hs.le).norm :
        Integrable (fun t : ℝ => ‖Complex.exp (-((s : ℂ)) * (t : ℂ)) * g t‖))
  have hLg : ‖complexLaplaceTransform g (s : ℂ)‖ ≤ C0 := by
    calc
      ‖complexLaplaceTransform g (s : ℂ)‖
          ≤ ∫ t : ℝ, ‖Complex.exp (-((s : ℂ) * (t : ℂ))) * g t‖ := by
              simpa [complexLaplaceTransform] using
                (MeasureTheory.norm_integral_le_integral_norm
                  (fun t : ℝ => Complex.exp (-((s : ℂ) * (t : ℂ))) * g t))
      _ ≤ ∫ t : ℝ, ‖g t‖ := by
            refine MeasureTheory.integral_mono_ae
              hIntExpNorm
              g.integrable.norm
              (Filter.Eventually.of_forall fun t =>
                by simpa [neg_mul] using complexLaplaceKernel_norm_le_self g hg_supp (s := (s : ℂ)) hs.le t)
      _ = C0 := rfl
  have hpow :
      ‖((1 / (s : ℂ)) ^ N)‖ = s ^ (-(N : ℤ)) := by
    calc
      ‖((1 / (s : ℂ)) ^ N)‖ = ‖(1 / (s : ℂ))‖ ^ N := by rw [norm_pow]
      _ = (s⁻¹) ^ N := by
            simp [one_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hs)]
      _ = s ^ (-(N : ℤ)) := by
            simp [zpow_neg, zpow_natCast, inv_pow]
  calc
    ‖complexLaplaceTransform f (s : ℂ)‖
        = ‖((1 / (s : ℂ)) ^ N) * complexLaplaceTransform g (s : ℂ)‖ := by
            rw [complexLaplaceTransform_real_eq_inv_pow_mul_iteratedDeriv f hf_supp hs N]
    _ = ‖((1 / (s : ℂ)) ^ N)‖ * ‖complexLaplaceTransform g (s : ℂ)‖ := by
          rw [norm_mul]
    _ ≤ ‖((1 / (s : ℂ)) ^ N)‖ * C0 := by
          gcongr
    _ = C0 * s ^ (-(N : ℤ)) := by
          rw [hpow, mul_comm]
    _ ≤ (C0 + 1) * s ^ (-(N : ℤ)) := by
          have hz_nonneg : 0 ≤ s ^ (-(N : ℤ)) := by
            rw [zpow_neg, zpow_natCast]
            positivity
          nlinarith

private theorem complexLaplaceTransform_real_tendsto_at_zero
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    Tendsto (fun s : ℝ => complexLaplaceTransform f (s : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ t : ℝ, f t)) := by
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun t : ℝ => ‖f t‖)
  · apply Filter.Eventually.of_forall
    intro s
    exact ((Complex.continuous_exp.comp
      ((continuous_const : Continuous (fun _ : ℝ => -(s : ℂ))).mul Complex.continuous_ofReal)).mul
      f.continuous).aestronglyMeasurable
  · have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin 0 (Set.Ioi 0) :=
      mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, Set.mem_Iio.mpr zero_lt_one,
        fun s hs => Set.mem_Ioo.mpr ⟨hs.2, hs.1⟩⟩
    apply Filter.eventually_of_mem hmem
    intro s hs
    obtain ⟨hs_pos, _hs_lt⟩ := Set.mem_Ioo.mp hs
    apply Filter.Eventually.of_forall
    intro t
    simpa using complexLaplaceKernel_norm_le_self f hf_supp (s := (s : ℂ)) (by simpa using le_of_lt hs_pos) t
  · exact f.integrable.norm
  · apply Filter.Eventually.of_forall
    intro t
    have hcont : Continuous fun s : ℝ => Complex.exp (-((s : ℂ) * (t : ℂ))) * f t := by
      fun_prop
    have htend :
        Tendsto (fun s : ℝ => Complex.exp (-((s : ℂ) * (t : ℂ))) * f t)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Complex.exp (-((0 : ℂ) * (t : ℂ))) * f t)) :=
      hcont.continuousAt.continuousWithinAt.tendsto
    simpa using htend

private theorem complexLaplaceTransform_weighted_real_tendsto_at_zero
    (N : ℕ)
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    Tendsto
      (fun s : ℝ => complexLaplaceTransform (weightedNegCoordPowSchwartz N f) (s : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ t : ℝ, (-(t : ℂ)) ^ N * f t)) := by
  simpa [weightedNegCoordPowSchwartz_apply] using
    (complexLaplaceTransform_real_tendsto_at_zero
      (weightedNegCoordPowSchwartz N f)
      (weightedNegCoordPowSchwartz_support N f hf_supp))

/-- The tempered functional pairing against `𝓕⁻¹ f`. -/
private noncomputable def fourierInvPairingCLM
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  (SchwartzMap.integralCLM ℂ (MeasureTheory.volume : MeasureTheory.Measure ℝ)).comp
    (SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => FourierTransform.fourierInv f t))

@[simp] private theorem fourierInvPairingCLM_apply
    (f φ : SchwartzMap ℝ ℂ) :
    fourierInvPairingCLM f φ =
      ∫ t : ℝ, FourierTransform.fourierInv f t * φ t := by
  rw [fourierInvPairingCLM, ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply]
  rw [SchwartzMap.smulLeftCLM_apply]
  · simp [smul_eq_mul]
  · fun_prop

/-- Positive-support Schwartz input gives one-sided Fourier support for the
inverse-Fourier pairing functional. This is the exact half-line spectral input
for the one-variable Section 4.3 Paley-Wiener step. -/
theorem fourierInvPairing_hasOneSidedFourierSupport
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    SCV.HasOneSidedFourierSupport (fourierInvPairingCLM f) := by
  intro φ hφ_supp
  rw [fourierInvPairingCLM_apply, SchwartzMap.integral_fourierInv_mul_eq]
  have hzero : ∀ x : ℝ, f x * φ x = 0 := by
    intro x
    by_cases hx : f x = 0
    · simp [hx]
    · have hx_mem : x ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ hx
      have hx_nonneg : 0 ≤ x := Set.mem_Ici.mp (hf_supp hx_mem)
      by_cases hφx : φ x = 0
      · simp [hφx]
      · have hx_neg : x < 0 := hφ_supp x (Function.mem_support.mpr hφx)
        exact (not_lt_of_ge hx_nonneg hx_neg).elim
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards with x
  simp [hzero x]

/-- One-variable core of the current Stage-5 spectral route: if `f` has
positive-time support and `φ` has negative support, then the inverse-Fourier
pairing induced by `f` annihilates the Fourier transform of any pointwise
product `g * φ`.

This is not a new route or wrapper theorem. It is exactly the support-disjoint
Parseval step needed after the future time-convolution / spatial-factorization
rewrite: once the time-shift functional is rewritten into this one-variable
form, the vanishing is immediate from `integral_fourierInv_mul_eq`. -/
theorem fourierInvPairing_annihilates_FT_of_negSupport_product
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    (g φ : SchwartzMap ℝ ℂ)
    (hφ_supp : ∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0) :
    fourierInvPairingCLM f
      ((SchwartzMap.fourierTransformCLM ℂ)
        ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => g x)) φ)) = 0 := by
  have hprod_supp :
      ∀ x ∈ Function.support
        (((SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => g y)) φ : SchwartzMap ℝ ℂ) : ℝ → ℂ),
        x < 0 := by
    intro x hx
    apply hφ_supp x
    apply Function.mem_support.mpr
    intro hφx
    apply hx
    rw [SchwartzMap.smulLeftCLM_apply_apply (F := ℂ) g.hasTemperateGrowth, hφx]
    simp
  exact
    (fourierInvPairing_hasOneSidedFourierSupport f hf_supp)
      (((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => g x)) φ)) hprod_supp

/-- Route-specific consumer of
`fourierInvPairing_annihilates_FT_of_negSupport_product`: every branch-`3b`
time slice coming from a positive-time Euclidean input has positive support, so
its inverse-Fourier pairing annihilates Fourier transforms of pointwise
products with a negative-support Schwartz factor.

This is the exact one-variable statement the later Stage-5 factorization will
need after rewriting the time-shift functional slice-by-slice; it keeps the
remaining blocker on the factorization step itself rather than on support
bookkeeping. -/
theorem fourierInvPairingCLM_partialFourierSpatial_timeSlice_annihilates_FT_of_negSupport_product
    {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (g χ : SchwartzMap ℝ ℂ)
    (hχ_supp : ∀ x ∈ Function.support (χ : ℝ → ℂ), x < 0) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => g x)) χ)) = 0 := by
  refine fourierInvPairing_annihilates_FT_of_negSupport_product
    (f := partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
      (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
    (g := g) (φ := χ) ?_ hχ_supp
  exact tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
    (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ

/-- Honest one-variable Section 4.3 supplier: from positive-support Schwartz
input, obtain the Paley-Wiener upper-half-plane extension with the correct
distributional boundary value. -/
theorem complexLaplaceTransform_hasPaleyWienerExtension
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    ∃ F_ext : ℂ → ℂ,
      DifferentiableOn ℂ F_ext SCV.upperHalfPlane ∧
      (∀ η : ℝ, 0 < η →
        SCV.HasPolynomialGrowthOnLine (fun x => F_ext (↑x + ↑η * Complex.I))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Filter.Tendsto (fun η : ℝ => ∫ x : ℝ, F_ext (↑x + ↑η * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ t : ℝ, FourierTransform.fourierInv f t * φ t))) := by
  simpa [fourierInvPairingCLM_apply] using
    SCV.paley_wiener_half_line
      (fourierInvPairingCLM f)
      (fourierInvPairing_hasOneSidedFourierSupport f hf_supp)

/-- On the positive imaginary axis, the canonical Fourier-Laplace extension of
the inverse-Fourier functional induced by `f` reproduces the raw one-sided
Laplace transform, with the built-in `2π` scaling from `SCV.paley_wiener_half_line`. -/
private theorem fourierLaplaceExt_fourierInvPairing_eq_complexLaplaceTransform
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {η : ℝ} (hη : 0 < η) :
    SCV.fourierLaplaceExt
        (fourierInvPairingCLM f)
        (((2 * Real.pi * η : ℂ) * Complex.I))
        (by simpa [Complex.mul_im, hη.ne'] using mul_pos Real.two_pi_pos hη)
      = complexLaplaceTransform f ((2 * Real.pi * η : ℂ)) := by
  let ψ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ (((2 * Real.pi * η : ℂ) * Complex.I))
      (by simpa [Complex.mul_im, hη.ne'] using mul_pos Real.two_pi_pos hη)
  have hψ_inv :
      FourierTransform.fourierInv ((SchwartzMap.fourierTransformCLM ℂ) ψ) = ψ := by
    simpa [ψ] using (FourierTransform.fourierInv_fourier_eq ψ)
  rw [SCV.fourierLaplaceExt_eq, fourierInvPairingCLM_apply, SchwartzMap.integral_fourierInv_mul_eq]
  rw [hψ_inv]
  change ∫ ξ : ℝ, f ξ * ψ ξ = ∫ t : ℝ, Complex.exp (-((2 * Real.pi * η : ℂ)) * (t : ℂ)) * f t
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with ξ
  by_cases hξ : f ξ = 0
  · simp [hξ]
  · have hξ_mem : ξ ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ hξ
    have hξ_nonneg : 0 ≤ ξ := Set.mem_Ici.mp (hf_supp hξ_mem)
    rw [show ψ ξ =
        SCV.schwartzPsiZ (((2 * Real.pi * η : ℂ) * Complex.I))
          (by simpa [Complex.mul_im, hη.ne'] using mul_pos Real.two_pi_pos hη) ξ by rfl]
    rw [SCV.schwartzPsiZ_apply, SCV.psiZ_eq_exp_of_nonneg hξ_nonneg]
    have hexp :
        Complex.exp (Complex.I * ((((2 * Real.pi * η : ℂ) * Complex.I)) * ξ)) =
          Complex.exp (-((2 * Real.pi * η : ℂ) * ξ)) := by
      congr 1
      ring_nf
      simp
    simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z => f ξ * z) hexp

/-- Explicit `2π` normalization check for the standard Paley-Wiener kernel on
the positive imaginary axis: when the spectral boundary functional later
evaluates a test at `u / 2π`, the kernel becomes the plain Laplace weight
`e^{-ηu}` on the nonnegative half-axis. -/
private theorem schwartzPsiZ_two_pi_imagAxis_apply_div_two_pi
    {η u : ℝ} (hη : 0 < η) (hu : 0 ≤ u) :
    SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (η * Complex.I)))
        (by simpa [Complex.mul_im, hη.ne'] using mul_pos Real.two_pi_pos hη)
        (u / (2 * Real.pi)) =
      Complex.exp (-((η * u : ℝ) : ℂ)) := by
  rw [SCV.schwartzPsiZ_apply, SCV.psiZ_eq_exp_of_nonneg]
  · congr 1
    have hI :
        Complex.I * (((2 * Real.pi : ℂ) * (η * Complex.I))) =
          -(((2 * Real.pi * η : ℝ) : ℂ)) := by
      calc
        Complex.I * (((2 * Real.pi : ℂ) * (η * Complex.I)))
            = ((2 * Real.pi : ℂ) * (η : ℂ)) * (Complex.I * Complex.I) := by
                ring
        _ = -(((2 * Real.pi * η : ℝ) : ℂ)) := by
              simp [Complex.I_mul_I, mul_comm, mul_left_comm, mul_assoc]
    have hscalar :
        (((2 * Real.pi * η : ℝ) : ℂ)) * (((u / (2 * Real.pi) : ℝ) : ℂ)) =
          ((η * u : ℝ) : ℂ) := by
      exact_mod_cast (show (2 * Real.pi * η) * (u / (2 * Real.pi)) = η * u by
        field_simp [Real.pi_ne_zero])
    calc
      Complex.I * (((2 * Real.pi : ℂ) * (η * Complex.I))) * (((u / (2 * Real.pi) : ℝ) : ℂ))
          = -(((2 * Real.pi * η : ℝ) : ℂ)) * (((u / (2 * Real.pi) : ℝ) : ℂ)) := by
              rw [hI]
      _ = -((((2 * Real.pi * η : ℝ) : ℂ)) * (((u / (2 * Real.pi) : ℝ) : ℂ))) := by
            ring
      _ = -((η * u : ℝ) : ℂ) := by
            rw [hscalar]
  · exact div_nonneg hu Real.two_pi_pos.le

/-- The one-variable Paley-Wiener supplier applied to the actual branch-`3b`
positive-time time slice: on the positive imaginary axis, the canonical
Fourier-Laplace extension of the induced inverse-Fourier pairing reproduces the
raw one-sided Laplace transform of the slice itself. -/
theorem fourierLaplaceExt_partialFourierSpatial_timeSlice_eq_complexLaplaceTransform
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {η : ℝ} (hη : 0 < η) :
    SCV.fourierLaplaceExt
        (fourierInvPairingCLM
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
        (((2 * Real.pi * η : ℂ) * Complex.I))
        (by simpa [Complex.mul_im, hη.ne'] using mul_pos Real.two_pi_pos hη)
      =
    complexLaplaceTransform
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
      ((2 * Real.pi * η : ℂ)) := by
  exact fourierLaplaceExt_fourierInvPairing_eq_complexLaplaceTransform
    (f := partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
    (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
      (d := d) (n := n) f r t ξ)
    hη

/-- The one-variable Paley-Wiener theorem, specialized to the actual branch-`3b`
positive-time time slice. This is the exact existential supplier that still
needs to be assembled into the global Section 4.3 transport map.

Source-first obstruction note for the live theorem-3 seam:
- this theorem only produces an upper-half-plane extension for one descended
  slice
  `partialFourierSpatial_timeSliceSchwartz ...`;
- together with
  `section43_iteratedSlice_descendedPairing` later in this file, the current
  graph can therefore descend those slice extensions along
  `os1TransportComponent` equalities;
- however, no theorem in this file or in
  `OSToWightmanBoundaryValueLimits.lean` / `...Comparison.lean` currently
  assembles those descended one-variable slices into the per-pair right-half-
  plane witness needed by
  `one_variable_time_interchange_for_wightman_pairing`;
- equivalently, no existing theorem on the explicit family inputs
  `F, hF, hcomp, f, hf, hprecompact, hambientCompact, hF0`
  lands either
  `∃ H : ℂ → ℂ, DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧ ...`
  with the required positive-real shell and Wightman values, or the immediate
  antecedent
  `bvt_singleSplit_xiShiftHolomorphicValue ... (t : ℂ) = bvt_W ...`;
- that witness-construction theorem remains the earliest honest missing
  upstream surface strictly before the public `hreal` payload. -/
theorem partialFourierSpatial_timeSlice_hasPaleyWienerExtension
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ∃ F_ext : ℂ → ℂ,
      DifferentiableOn ℂ F_ext SCV.upperHalfPlane ∧
      (∀ η : ℝ, 0 < η →
        SCV.HasPolynomialGrowthOnLine (fun x => F_ext (↑x + ↑η * Complex.I))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Filter.Tendsto (fun η : ℝ => ∫ x : ℝ, F_ext (↑x + ↑η * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (fourierInvPairingCLM
              (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
              φ))) := by
  simpa [fourierInvPairingCLM_apply] using
    complexLaplaceTransform_hasPaleyWienerExtension
      (f := partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
      (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
        (d := d) (n := n) f r t ξ)

/-- The canonical one-variable Section-4.3 upper-half-plane extension attached
to the actual branch-`3b` positive-time slice. This avoids arbitrary
`Classical.choose` packaging: it is exactly the scaled `SCV.fourierLaplaceExt`
that `paley_wiener_half_line` builds under the hood. -/
noncomputable def partialFourierSpatial_timeSliceCanonicalExtension
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (w : ℂ) : ℂ :=
  if hw : 0 < w.im then
    SCV.fourierLaplaceExt
      (fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
      (((2 * Real.pi : ℂ) * w))
      (by
        have hmul : 0 < (2 * Real.pi) * w.im := mul_pos Real.two_pi_pos hw
        simpa [Complex.mul_im] using hmul)
  else
    0

/-- On the positive imaginary axis, the canonical slice extension reproduces
the raw one-sided Laplace transform of the branch-`3b` time slice. -/
theorem partialFourierSpatial_timeSliceCanonicalExtension_eq_complexLaplaceTransform
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {η : ℝ} (hη : 0 < η) :
    partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ (η * Complex.I)
      =
    complexLaplaceTransform
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
      ((2 * Real.pi * η : ℂ)) := by
  have him : 0 < (η * Complex.I).im := by simpa using hη
  simp only [partialFourierSpatial_timeSliceCanonicalExtension, dif_pos him]
  have harg :
      ((2 * Real.pi : ℂ) * (η * Complex.I)) = ((2 * Real.pi * η : ℂ) * Complex.I) := by
    norm_num
    ring
  simpa [harg] using
    (fourierLaplaceExt_partialFourierSpatial_timeSlice_eq_complexLaplaceTransform
      (d := d) (n := n) f r t ξ hη)

/-- The one-variable Paley-Wiener Fourier-Laplace value at `2π i η` is the
same scalar as the Section-4.3 descended pairing against the corresponding
`ψ_Z` kernel. This is the local Lemma-8.4 atom used by the transported
time-interchange packets. -/
private theorem lemma84_oneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : SCV.HasOneSidedFourierSupport T)
    {η : ℝ} (hη : 0 < η) :
    SCV.fourierLaplaceExt T
        (((2 * Real.pi * η : ℂ) * Complex.I))
        (by
          simpa [Complex.mul_im, hη.ne']
            using mul_pos Real.two_pi_pos hη) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        T hT_supp
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi * η : ℂ) * Complex.I))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) := by
  rw [SCV.fourierLaplaceExt_eq]
  symm
  exact
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply
      (T := T) (hT_supp := hT_supp)
      (f := SCV.schwartzPsiZ
        (((2 * Real.pi * η : ℂ) * Complex.I))
        (by
          simpa [Complex.mul_im, hη.ne']
            using mul_pos Real.two_pi_pos hη))

/-- On the positive imaginary axis, the canonical one-variable slice extension
is exactly the descended Section-4.3 Fourier pairing evaluated on the quotient
class of the same Paley-Wiener kernel `ψ_{2πiη}`. This is the first explicit
meeting point between the slice Paley-Wiener package and the current
Section-4.3 codomain on the actual `ψ`-family used in Phase C'. -/
private theorem
    partialFourierSpatial_timeSliceCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {η : ℝ} (hη : 0 < η) :
    partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ (η * Complex.I) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (fourierInvPairingCLM
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
        (fourierInvPairing_hasOneSidedFourierSupport
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := n) f r t ξ))
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi * η : ℂ) * Complex.I))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) := by
  let T : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    fourierInvPairingCLM
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
  let ψ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi * η : ℂ) * Complex.I))
      (by
        simpa [Complex.mul_im, hη.ne']
          using mul_pos Real.two_pi_pos hη)
  have him : 0 < (η * Complex.I).im := by
    simpa using hη
  have hApply :
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          T
          (fourierInvPairing_hasOneSidedFourierSupport
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
            (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
              (d := d) (n := n) f r t ξ))
          (section43PositiveEnergyQuotientMap1D ψ) =
        T ((SchwartzMap.fourierTransformCLM ℂ) ψ) := by
    simpa [T, ψ] using
      (OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply
        (T := T)
        (hT_supp := fourierInvPairing_hasOneSidedFourierSupport
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := n) f r t ξ))
        (f := ψ))
  rw [partialFourierSpatial_timeSliceCanonicalExtension, dif_pos him, SCV.fourierLaplaceExt_eq]
  have harg : ((2 * Real.pi : ℂ) * (η * Complex.I)) =
      (((2 * Real.pi * η : ℝ) : ℂ) * Complex.I) := by
    norm_num
    ring
  simpa [T, ψ, harg] using hApply.symm

private theorem partialFourierSpatial_timeSliceCanonicalExtension_differentiableOn
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    DifferentiableOn ℂ
      (partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ)
      SCV.upperHalfPlane := by
  let T :=
    fourierInvPairingCLM
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
  let Fcore : ℂ → ℂ := fun w =>
    if hw : 0 < w.im then
      SCV.fourierLaplaceExt T w hw
    else
      0
  let F : ℂ → ℂ := Fcore ∘ fun w => (((2 * Real.pi : ℝ) : ℂ) * w)
  have hF_diff : DifferentiableOn ℂ F SCV.upperHalfPlane := by
    have hmap : Set.MapsTo (fun w : ℂ => (((2 * Real.pi : ℝ) : ℂ) * w))
        SCV.upperHalfPlane SCV.upperHalfPlane := by
      intro z hz
      dsimp [SCV.upperHalfPlane] at hz ⊢
      simpa [Complex.mul_im, mul_assoc] using mul_pos Real.two_pi_pos hz
    have hmul :
        DifferentiableOn ℂ (fun w : ℂ => (((2 * Real.pi : ℝ) : ℂ) * w))
          SCV.upperHalfPlane := by
      intro z hz
      simpa using
        ((((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z).const_mul
          (((2 * Real.pi : ℝ) : ℂ))).differentiableWithinAt))
    simpa [F, Fcore] using (SCV.fourierLaplaceExt_differentiableOn T).comp hmul hmap
  have hEq : partialFourierSpatial_timeSliceCanonicalExtension
      (d := d) (n := n) f r t ξ = F := by
    funext w
    by_cases hw : 0 < w.im
    · have hscaled : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im := by
        simpa [Complex.mul_im, mul_assoc] using mul_pos Real.two_pi_pos hw
      show partialFourierSpatial_timeSliceCanonicalExtension
          (d := d) (n := n) f r t ξ w =
        Fcore ((((2 * Real.pi : ℝ) : ℂ) * w))
      change partialFourierSpatial_timeSliceCanonicalExtension
          (d := d) (n := n) f r t ξ w =
        if hw' : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im then
          SCV.fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * w)) hw'
        else 0
      rw [partialFourierSpatial_timeSliceCanonicalExtension, dif_pos hw, dif_pos hscaled]
      simp [T]
    · have hnotscaled : ¬ 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im := by
        intro hscaled
        have hscaled' : 0 < (2 * Real.pi) * w.im := by
          simpa [Complex.mul_im, mul_assoc] using hscaled
        nlinarith [Real.two_pi_pos, hscaled']
      show partialFourierSpatial_timeSliceCanonicalExtension
          (d := d) (n := n) f r t ξ w =
        Fcore ((((2 * Real.pi : ℝ) : ℂ) * w))
      change partialFourierSpatial_timeSliceCanonicalExtension
          (d := d) (n := n) f r t ξ w =
        if hw' : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im then
          SCV.fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * w)) hw'
        else 0
      rw [partialFourierSpatial_timeSliceCanonicalExtension, dif_neg hw, dif_neg hnotscaled]
  rw [hEq]
  exact hF_diff

/-- The actual branch-`3b` time slice, packaged as the one-variable Section 4.3
positive-time test input. -/
private noncomputable def partialFourierSpatial_timeSliceTest
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ↥(OSReconstruction.euclideanPositiveTimeTest1D) :=
  ⟨partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ,
    tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
      (d := d) (n := n) f r t ξ⟩

/-- The quotient-side descended pairing for the actual branch-`3b` time slice.
This is the first direct bridge from the existing slice-level analytic package
to the new Section 4.3 transport codomain. -/
private theorem fourierPairingDescendsToSection43PositiveEnergy1D_partialFourierSpatial_timeSlice
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (fourierInvPairingCLM
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
        (fourierInvPairing_hasOneSidedFourierSupport
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := n) f r t ξ))
        (OSReconstruction.os1TransportOneVar
          (partialFourierSpatial_timeSliceTest (d := d) (n := n) f r t ξ)) =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)) := by
  simpa [partialFourierSpatial_timeSliceTest] using
    (OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_os1TransportOneVar
      (T := fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
      (hT_supp := fourierInvPairing_hasOneSidedFourierSupport
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
        (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
          (d := d) (n := n) f r t ξ))
      (f := partialFourierSpatial_timeSliceTest (d := d) (n := n) f r t ξ))

/-- If two ambient Schwartz tests agree on the Section 4.3 positive-energy
region, then their partial spatial Fourier transforms agree at every time
vector with nonnegative coordinates. -/
private theorem partialFourierSpatial_fun_eq_of_eqOn_section43PositiveEnergyRegion
    {n : ℕ} {f g : SchwartzNPoint d n}
    (hfg :
      Set.EqOn (f : NPointDomain d n → ℂ) (g : NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n))
    (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    partialFourierSpatial_fun (d := d) (n := n) f (t, ξ) =
      partialFourierSpatial_fun (d := d) (n := n) g (t, ξ) := by
  rw [partialFourierSpatial_fun_eq_integral (d := d) (n := n) f (t, ξ)]
  rw [partialFourierSpatial_fun_eq_integral (d := d) (n := n) g (t, ξ)]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with η
  have hregion :
      (nPointTimeSpatialCLE (d := d) n).symm (t, η) ∈
        section43PositiveEnergyRegion d n := by
    intro i
    simpa [nPointTimeSpatialCLE] using ht i
  have hval :
      nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (t, η) =
        nPointTimeSpatialSchwartzCLE (d := d) (n := n) g (t, η) := by
    simpa [nPointTimeSpatialSchwartzCLE, nPointTimeSpatialCLE,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hfg hregion
  simp [hval]

/-- Equality of multivariate Section 4.3 quotient classes forces equality of
the associated one-variable slice tests on `[0,\infty)`, provided the frozen
background times are nonnegative. This is the quotient-level frozen-slice
bridge needed to consume total-arity quotient equalities directly, without
repackaging them through the ordered-support transport subtype. -/
private theorem partialFourierSpatial_timeSlice_eqOn_nonneg_of_section43PositiveEnergyQuotientMap_eq
    {n : ℕ}
    {φ ψ : SchwartzNPoint d n}
    (hφψ :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        section43PositiveEnergyQuotientMap (d := d) n ψ)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Set.EqOn
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ :
          SchwartzMap ℝ ℂ) : ℝ → ℂ)
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) ψ r t ξ :
          SchwartzMap ℝ ℂ) : ℝ → ℂ)
      (Set.Ici (0 : ℝ)) := by
  have hregion :
      Set.EqOn (φ : NPointDomain d n → ℂ) (ψ : NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n) :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := n) (f := φ) (g := ψ) hφψ
  intro s hs
  have hnonneg : ∀ i : Fin n, 0 ≤ Function.update t r s i := by
    intro i
    by_cases hi : i = r
    · subst hi
      simpa using hs
    · rw [Function.update_of_ne hi]
      exact ht i hi
  simpa [partialFourierSpatial_timeSliceSchwartz] using
    partialFourierSpatial_fun_eq_of_eqOn_section43PositiveEnergyRegion
      (d := d) (n := n) hregion (Function.update t r s) hnonneg ξ

/-- If an ambient transformed-image representative `φ` and a positive-time
preimage `f` define the same Section 4.3 quotient class, then freezing all but
one time variable with nonnegative background times gives the same one-variable
slice on `[0,∞)`. This is the first honest ambient-representative bridge
needed by the corrected Stage-5 theorem surface.

Bounded-pass status note (2026-04-13): source-first inspection now matters one
notch more sharply here. The public frozen-slice chain used later near
`hlimit_os`

`section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
-> `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
-> `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
-> `section43_iteratedSlice_descendedPairing`

starts by applying `section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg` to
this exact `Set.EqOn` theorem. So if the fixed-time canonical-shell
specialization of that public chain is still too high, the exact first lower
source-backed ingredient is this theorem together with the still-missing choice
of canonical slice parameters `(r, t, ht, ξ)` matching the ambient shell. -/
private theorem partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Set.EqOn
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ :
          SchwartzMap ℝ ℂ) : ℝ → ℂ)
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ :
            SchwartzMap ℝ ℂ) : ℝ → ℂ)
      (Set.Ici (0 : ℝ)) := by
  have hregion :
      Set.EqOn (φ : NPointDomain d n → ℂ)
        ((f : euclideanPositiveTimeSubmodule (d := d) n) :
          NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n) := by
    have hq :
        section43PositiveEnergyQuotientMap (d := d) n φ =
          section43PositiveEnergyQuotientMap (d := d) n f.1 := by
      simpa [os1TransportComponent_apply] using hφf
    exact eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := n) (f := φ) (g := f.1) hq
  intro s hs
  have hnonneg : ∀ i : Fin n, 0 ≤ Function.update t r s i := by
    intro i
    by_cases hi : i = r
    · subst hi
      simpa using hs
    · rw [Function.update_of_ne hi]
      exact ht i hi
  simpa [partialFourierSpatial_timeSliceSchwartz] using
    partialFourierSpatial_fun_eq_of_eqOn_section43PositiveEnergyRegion
      (d := d) (n := n) hregion (Function.update t r s) hnonneg ξ

/-- Zero-left branch of the Section-4.3 representative bridge. For `n = 0`,
the positive-energy region condition is vacuous, so quotient equality already
gives pointwise equality of the ambient representative and its positive-time
preimage. -/
private theorem section43_zero_left_repr_eq_transport_pointwise
    {φ : SchwartzNPoint d 0}
    {f : euclideanPositiveTimeSubmodule (d := d) 0}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) 0 φ =
        os1TransportComponent d 0 f) :
    φ = (EuclideanPositiveTimeComponent.ofSubmodule f).1 := by
  ext x
  have hq :
      section43PositiveEnergyQuotientMap (d := d) 0 φ =
        section43PositiveEnergyQuotientMap (d := d) 0 f.1 := by
    simpa [os1TransportComponent_apply] using hφf
  have hEqOn :
      Set.EqOn (φ : NPointDomain d 0 → ℂ) (f.1 : NPointDomain d 0 → ℂ)
        (section43PositiveEnergyRegion d 0) :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := 0) hq
  exact hEqOn (by intro i; exact Fin.elim0 i)
/-- Negative time in the distinguished variable forces any frozen slice of a
mixed-order fixed-pair source test to vanish. Only the nonnegative-time part of
`FixedPairMixedOrderTimeRegion` is used here; the reversed/forward order split
is irrelevant at this one-variable entry point. -/
private theorem nPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time_of_fixedPairMixedOrder
    {n m : ℕ}
    (F : OSReconstruction.FixedPairMixedOrderComponent d n m)
    (r : Fin (n + m)) (t : Fin (n + m) → ℝ)
    (η : EuclideanSpace ℝ (Fin (n + m) × Fin d))
    {s : ℝ} (hs : s < 0) :
    OSReconstruction.nPointTimeSpatialSchwartzCLE (d := d) (n := n + m) F.1
      (Function.update t r s, η) = 0 := by
  have hnot_region :
        (OSReconstruction.nPointTimeSpatialCLE (d := d) (n + m)).symm
        (Function.update t r s, η) ∉
        OSReconstruction.FixedPairMixedOrderTimeRegion d n m := by
    intro hmem
    have htime :
        0 ≤
          (((OSReconstruction.nPointTimeSpatialCLE (d := d) (n + m)).symm
            (Function.update t r s, η)) r 0) := hmem.1 r
    have hEq :
        (((OSReconstruction.nPointTimeSpatialCLE (d := d) (n + m)).symm
          (Function.update t r s, η)) r 0) = s := by
      simp [OSReconstruction.nPointTimeSpatialCLE]
    linarith
  have hnot_supp :
      (OSReconstruction.nPointTimeSpatialCLE (d := d) (n + m)).symm
        (Function.update t r s, η) ∉
        tsupport (F.1 : NPointDomain d (n + m) → ℂ) := by
    intro hx
    exact hnot_region (F.2 hx)
  change F.1 ((OSReconstruction.nPointTimeSpatialCLE (d := d) (n + m)).symm
    (Function.update t r s, η)) = 0
  simpa using image_eq_zero_of_notMem_tsupport hnot_supp

/-- Equality of total-arity Section 4.3 quotient classes already forces
equality of the associated frozen mixed-order slices on `[0,\infty)`, provided
the frozen background times are nonnegative away from the distinguished
variable. This is the first exact mixed-order `EqOn` bridge beneath the later
1D quotient and pairing consumers. -/
private theorem partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_fixedPairMixedOrder
    {n m : ℕ}
    {Φ : SchwartzNPoint d (n + m)}
    {F : OSReconstruction.FixedPairMixedOrderComponent d n m}
    (hΦF :
      section43PositiveEnergyQuotientMap (d := d) (n + m) Φ =
        section43PositiveEnergyQuotientMap (d := d) (n + m) F.1)
    (r : Fin (n + m)) (t : Fin (n + m) → ℝ)
    (ht : ∀ i : Fin (n + m), i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d)) :
    Set.EqOn
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) Φ r t ξ :
          SchwartzMap ℝ ℂ) : ℝ → ℂ)
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) F.1 r t ξ :
          SchwartzMap ℝ ℂ) : ℝ → ℂ)
      (Set.Ici (0 : ℝ)) := by
  have hregion :
      Set.EqOn (Φ : NPointDomain d (n + m) → ℂ) (F.1 : NPointDomain d (n + m) → ℂ)
        (section43PositiveEnergyRegion d (n + m)) :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := n + m) (f := Φ) (g := F.1) hΦF
  intro s hs
  have hnonneg : ∀ i : Fin (n + m), 0 ≤ Function.update t r s i := by
    intro i
    by_cases hi : i = r
    · subst hi
      simpa using hs
    · rw [Function.update_of_ne hi]
      exact ht i hi
  simpa [partialFourierSpatial_timeSliceSchwartz] using
    partialFourierSpatial_fun_eq_of_eqOn_section43PositiveEnergyRegion
      (d := d) (n := n + m) hregion (Function.update t r s) hnonneg ξ

/-- Therefore every frozen branch-`3b` slice of a mixed-order fixed-pair source
test is supported in `t ≥ 0` in the distinguished variable, as long as the
other frozen times are nonnegative. This is the exact one-variable source fact
needed to feed the existing Section 4.3 1D quotient codomain. -/
private theorem tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_fixedPairMixedOrder
    {n m : ℕ}
    (F : OSReconstruction.FixedPairMixedOrderComponent d n m)
    (r : Fin (n + m)) (t : Fin (n + m) → ℝ)
    (ht : ∀ i : Fin (n + m), i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d)) :
    tsupport (fun s : ℝ =>
      OSReconstruction.partialFourierSpatial_fun (d := d) (n := n + m) F.1
        (Function.update t r s, ξ)) ⊆ Set.Ici 0 := by
  intro s hs
  by_contra hs_neg
  have hs_lt : s < 0 := by
    simpa [Set.mem_Ici, not_le] using hs_neg
  have hs_not :
      s ∉ tsupport (fun s' : ℝ =>
        OSReconstruction.partialFourierSpatial_fun (d := d) (n := n + m) F.1
          (Function.update t r s', ξ)) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    have hball : Metric.ball s (-s / 2) ∈ 𝓝 s := by
      apply Metric.ball_mem_nhds
      linarith
    filter_upwards [hball] with s' hs'
    have hsabs : |s' - s| < -s / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hs'
    have hs'_lt : s' < 0 := by
      linarith [(abs_lt.mp hsabs).2, hs_lt]
    rw [OSReconstruction.partialFourierSpatial_fun_eq_integral]
    refine MeasureTheory.integral_eq_zero_of_ae ?_
    filter_upwards with η
    simp [nPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time_of_fixedPairMixedOrder
      (d := d) (F := F) (r := r) (t := t) (η := η) hs'_lt]
  exact hs_not hs

/-- The actual branch-`3b` time slice of a mixed-order fixed-pair source,
packaged as a one-variable Section 4.3 positive-time test. This is the first
honest replacement for the old total-arity `EuclideanPositiveTimeComponent`
entry point on the fixed-pair mixed-order geometry. -/
private noncomputable def partialFourierSpatial_timeSliceTest_fixedPairMixedOrder
    {n m : ℕ} (F : OSReconstruction.FixedPairMixedOrderComponent d n m)
    (r : Fin (n + m)) (t : Fin (n + m) → ℝ)
    (ht : ∀ i : Fin (n + m), i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d)) :
    ↥(OSReconstruction.euclideanPositiveTimeTest1D) :=
  ⟨partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) F.1 r t ξ,
    tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_fixedPairMixedOrder
      (d := d) F r t ht ξ⟩

/-- First mixed-order transport consumer strictly below the live fixed-pair
frontier: if an ambient total-arity representative and a mixed-order fixed-pair
source test define the same Section 4.3 quotient class, then the corresponding
frozen one-variable slice already descends to the existing 1D transport codomain.

This replaces the old total-arity `EuclideanPositiveTimeComponent` entry point
for the fixed-pair geometry without reviving the false whole-shell
`OrderedPositiveTimeRegion` claim. -/
private theorem
    section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_fixedPairMixedOrder
    {n m : ℕ}
    {Φ : SchwartzNPoint d (n + m)}
    {F : OSReconstruction.FixedPairMixedOrderComponent d n m}
    (hΦF :
      section43PositiveEnergyQuotientMap (d := d) (n + m) Φ =
        section43PositiveEnergyQuotientMap (d := d) (n + m) F.1)
    (r : Fin (n + m)) (t : Fin (n + m) → ℝ)
    (ht : ∀ i : Fin (n + m), i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d)) :
    section43PositiveEnergyQuotientMap1D
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) Φ r t ξ) =
      os1TransportOneVar
        (partialFourierSpatial_timeSliceTest_fixedPairMixedOrder
          (d := d) F r t ht ξ) := by
  apply section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg
  have hregion :
      Set.EqOn (Φ : NPointDomain d (n + m) → ℂ) (F.1 : NPointDomain d (n + m) → ℂ)
        (section43PositiveEnergyRegion d (n + m)) :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := n + m) (f := Φ) (g := F.1) hΦF
  intro s hs
  have hnonneg : ∀ i : Fin (n + m), 0 ≤ Function.update t r s i := by
    intro i
    by_cases hi : i = r
    · subst hi
      simpa using hs
    · rw [Function.update_of_ne hi]
      exact ht i hi
  simpa [partialFourierSpatial_timeSliceTest_fixedPairMixedOrder,
    partialFourierSpatial_timeSliceSchwartz] using
    partialFourierSpatial_fun_eq_of_eqOn_section43PositiveEnergyRegion
      (d := d) (n := n + m) hregion (Function.update t r s) hnonneg ξ

/-- First actual frozen-slice consumer of the mixed-order fixed-pair source
entry point: any one-sided Fourier-support functional already sees the same
one-variable Section 4.3 class on the corresponding time slice. This is the
mixed-order replacement for the old total-arity
`EuclideanPositiveTimeComponent` consumer used later in the slice-descended
pairing chain. -/
private theorem
    fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_fixedPairMixedOrder
    {n m : ℕ}
    {Φ : SchwartzNPoint d (n + m)}
    {F : OSReconstruction.FixedPairMixedOrderComponent d n m}
    (hΦF :
      section43PositiveEnergyQuotientMap (d := d) (n + m) Φ =
        section43PositiveEnergyQuotientMap (d := d) (n + m) F.1)
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : SCV.HasOneSidedFourierSupport T)
    (r : Fin (n + m)) (t : Fin (n + m) → ℝ)
    (ht : ∀ i : Fin (n + m), i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d)) :
    fourierPairingDescendsToSection43PositiveEnergy1D T hT_supp
        (section43PositiveEnergyQuotientMap1D
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) Φ r t ξ)) =
      fourierPairingDescendsToSection43PositiveEnergy1D T hT_supp
        (os1TransportOneVar
          (partialFourierSpatial_timeSliceTest_fixedPairMixedOrder
            (d := d) F r t ht ξ)) := by
  rw [section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_fixedPairMixedOrder
    (d := d) (n := n) (m := m) hΦF r t ht ξ]

/-- Therefore the one-variable Section 4.3 quotient class of the ambient slice
is the same as the transport slice class of its positive-time preimage. This is
the direct current-code bridge from an ambient transformed-image representative
to the one-variable quotient theorem used later in the Stage-5 adapter. -/
private theorem fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_fixedPairMixedOrder
    {n m : ℕ}
    {Φ : SchwartzNPoint d (n + m)}
    {F : OSReconstruction.FixedPairMixedOrderComponent d n m}
    (hΦF :
      section43PositiveEnergyQuotientMap (d := d) (n + m) Φ =
        section43PositiveEnergyQuotientMap (d := d) (n + m) F.1)
    (r : Fin (n + m)) (t : Fin (n + m) → ℝ)
    (ht : ∀ i : Fin (n + m), i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d)) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) F.1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) Φ r t ξ)) =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) F.1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) F.1 r t ξ)) := by
  let FSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) F.1 r t ξ
  have hleft :
      fourierPairingDescendsToSection43PositiveEnergy1D
          (fourierInvPairingCLM FSlice)
          (fourierInvPairing_hasOneSidedFourierSupport FSlice
            (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_fixedPairMixedOrder
              (d := d) F r t ht ξ))
          (section43PositiveEnergyQuotientMap1D
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) Φ r t ξ)) =
        fourierInvPairingCLM FSlice
          ((SchwartzMap.fourierTransformCLM ℂ)
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) Φ r t ξ)) := by
    simpa [FSlice] using
      (fourierPairingDescendsToSection43PositiveEnergy1D_apply
        (T := fourierInvPairingCLM FSlice)
        (hT_supp := fourierInvPairing_hasOneSidedFourierSupport FSlice
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_fixedPairMixedOrder
            (d := d) F r t ht ξ))
        (f := partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) Φ r t ξ))
  calc
    fourierInvPairingCLM FSlice
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) Φ r t ξ)) =
      fourierPairingDescendsToSection43PositiveEnergy1D
          (fourierInvPairingCLM FSlice)
          (fourierInvPairing_hasOneSidedFourierSupport FSlice
            (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_fixedPairMixedOrder
              (d := d) F r t ht ξ))
          (section43PositiveEnergyQuotientMap1D
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) Φ r t ξ)) := by
        symm
        exact hleft
    _ =
      fourierPairingDescendsToSection43PositiveEnergy1D
          (fourierInvPairingCLM FSlice)
          (fourierInvPairing_hasOneSidedFourierSupport FSlice
            (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_fixedPairMixedOrder
              (d := d) F r t ht ξ))
          (os1TransportOneVar
            (partialFourierSpatial_timeSliceTest_fixedPairMixedOrder
              (d := d) F r t ht ξ)) := by
        exact fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_fixedPairMixedOrder
          (d := d) (n := n) (m := m) hΦF
          (T := fourierInvPairingCLM FSlice)
          (hT_supp := fourierInvPairing_hasOneSidedFourierSupport FSlice
            (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_fixedPairMixedOrder
              (d := d) F r t ht ξ))
          r t ht ξ
    _ =
      fourierInvPairingCLM FSlice
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) F.1 r t ξ)) := by
        simp [FSlice, partialFourierSpatial_timeSliceTest_fixedPairMixedOrder]

/-- Therefore the one-variable Section 4.3 quotient class of the ambient slice
is the same as the transport slice class of its positive-time preimage. This is
the direct current-code bridge from an ambient transformed-image representative
to the one-variable quotient theorem used later in the Stage-5 adapter. -/
private theorem section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    section43PositiveEnergyQuotientMap1D
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ) =
      os1TransportOneVar
        (partialFourierSpatial_timeSliceTest (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ) := by
  apply section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg
  exact partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport
    (d := d) (n := n) hφf r t ht ξ

/-- General one-variable descended-pairing form of the same bridge: once an
ambient representative `φ` and a positive-time preimage `f` determine the same
multivariate Section-4.3 class, every one-sided Fourier-support functional sees
the same one-variable quotient class on the corresponding time slice. This is
the real theorem surface needed later when the pairing functional is induced by
the opposite factor's slice rather than by the same slice. -/
private theorem fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_transport
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : SCV.HasOneSidedFourierSupport T)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    fourierPairingDescendsToSection43PositiveEnergy1D T hT_supp
        (section43PositiveEnergyQuotientMap1D
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) =
      fourierPairingDescendsToSection43PositiveEnergy1D T hT_supp
        (os1TransportOneVar
          (partialFourierSpatial_timeSliceTest (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ)) := by
  rw [section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
    (d := d) (n := n) hφf r t ht ξ]

/-- Scalar descended-pairing form of the same bridge: if an ambient
transformed-image representative `φ` and a positive-time preimage `f` define
the same multivariate Section 4.3 quotient class, then the one-variable
descended Fourier pairing attached to the positive-time slice of `f` already
recovers the quotient class of the ambient slice of `φ`. This is the exact
current-code scalar ingredient later needed inside the Lemma-4.2 matrix-element
adapter. -/
private theorem fourierPairingDescendsToSection43PositiveEnergy1D_repr_partialFourierSpatial_timeSlice
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (fourierInvPairingCLM
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ))
        (fourierInvPairing_hasOneSidedFourierSupport
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ))
        (section43PositiveEnergyQuotientMap1D
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)) := by
  rw [fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_transport
    (d := d) (n := n) hφf
    (T := fourierInvPairingCLM
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ))
    (hT_supp := fourierInvPairing_hasOneSidedFourierSupport
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
      (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ))
    r t ht ξ]
  exact fourierPairingDescendsToSection43PositiveEnergy1D_partialFourierSpatial_timeSlice
    (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ

/-- Wrapper-free scalar form of the same bridge: for the one-variable pairing
functional induced by the positive-time slice of `f`, the Fourier-side pairing
against the ambient slice of `φ` already equals the same pairing against the
actual positive-time slice. This is the scalar theorem-surface that the later
Lemma-4.2 adapter should consume directly, without reintroducing quotient
wrappers in its statement. -/
theorem fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)) := by
  have hleft :
      fourierPairingDescendsToSection43PositiveEnergy1D
          (fourierInvPairingCLM
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
              (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ))
          (fourierInvPairing_hasOneSidedFourierSupport
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
              (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
            (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
              (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ))
          (section43PositiveEnergyQuotientMap1D
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) =
        fourierInvPairingCLM
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
          ((SchwartzMap.fourierTransformCLM ℂ)
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) := by
    simpa using
      (fourierPairingDescendsToSection43PositiveEnergy1D_apply
        (T := fourierInvPairingCLM
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ))
        (hT_supp := fourierInvPairing_hasOneSidedFourierSupport
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ))
        (f := partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ))
  calc
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) =
      fourierPairingDescendsToSection43PositiveEnergy1D
          (fourierInvPairingCLM
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
              (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ))
          (fourierInvPairing_hasOneSidedFourierSupport
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
              (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
            (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
              (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ))
          (section43PositiveEnergyQuotientMap1D
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) := by
        symm
        exact hleft
    _ =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)) := by
        exact fourierPairingDescendsToSection43PositiveEnergy1D_repr_partialFourierSpatial_timeSlice
          (d := d) (n := n) hφf r t ht ξ

/-- Direct kernel form of the same slice bridge: under the Section-4.3
quotient-class hypothesis, the ambient-minus-preimage one-variable slice lies
in the kernel of every one-sided Fourier-support pairing. This is the exact
zero statement later needed in the Lemma-4.2 route, without reintroducing
quotient wrappers. -/
theorem oneSidedFourierSupport_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : SCV.HasOneSidedFourierSupport T)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    T ((SchwartzMap.fourierTransformCLM ℂ)
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ) -
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ))) = 0 := by
  refine SCV.fourier_pairing_vanishes_of_eqOn_nonneg
    (T := T) (hT_supp := hT_supp) ?_
  intro s hs
  have hslice :
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ : ℝ → ℂ) s =
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ : ℝ → ℂ) s :=
    partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport
      (d := d) (n := n) hφf r t ht ξ hs
  simp [hslice]

/-- Concrete scalar specialization of
`oneSidedFourierSupport_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`:
the one-variable pairing induced by any positive-time slice on the opposite
factor already kills the ambient-minus-preimage slice difference. This is the
exact "each slice pairing vanishes" statement later consumed by the
matrix-element factorization step. -/
theorem fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
    {n m : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {g : euclideanPositiveTimeSubmodule (d := d) m}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (rφ : Fin n) (tφ : Fin n → ℝ)
    (htφ : ∀ i : Fin n, i ≠ rφ → 0 ≤ tφ i)
    (ξφ : EuclideanSpace ℝ (Fin n × Fin d))
    (rψ : Fin m) (tψ : Fin m → ℝ)
    (htψ : ∀ i : Fin m, i ≠ rψ → 0 ≤ tψ i)
    (ξψ : EuclideanSpace ℝ (Fin m × Fin d)) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ rφ tφ ξφ) -
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
              (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ))) = 0 := by
  exact
    oneSidedFourierSupport_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
      (d := d)
      (T := fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ))
      (hT_supp := fourierInvPairing_hasOneSidedFourierSupport
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ)
        (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
          (d := d) (n := m) (EuclideanPositiveTimeComponent.ofSubmodule g) rψ tψ ξψ))
      hφf rφ tφ htφ ξφ

/-- Fourier-pairing symmetry on Fourier-transformed inputs: the slice pairing
induced by `f` and evaluated on `𝓕 g` is the same scalar as the opposite
pairing induced by `g` and evaluated on `𝓕 f`. This is the algebraic
commutativity step later used to move the Section-4.3 descended pairing from
one side of the Lemma-4.2 shell to the other without introducing any new
analytic content. -/
private theorem fourierInvPairingCLM_fourierTransform_symm
    (f g : SchwartzMap ℝ ℂ) :
    fourierInvPairingCLM f ((SchwartzMap.fourierTransformCLM ℂ) g) =
      fourierInvPairingCLM g ((SchwartzMap.fourierTransformCLM ℂ) f) := by
  rw [fourierInvPairingCLM_apply, fourierInvPairingCLM_apply]
  rw [SchwartzMap.integral_fourierInv_mul_eq, SchwartzMap.integral_fourierInv_mul_eq]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  simp [mul_comm]

/-- Opposite-factor scalar pairing bridge on the corrected Stage-5 surface: if
ambient representatives `φ, ψ` come from positive-time preimages `f, g`, then
the one-variable Fourier pairing induced by the positive-time slice of `g`
against the ambient slice of `φ` already agrees with the opposite pairing
induced by the positive-time slice of `f` against the ambient slice of `ψ`.

This is a genuine current-code ingredient for the later Lemma-4.2 adapter:
both pairing functionals come from positive-time slices, so the descended
pairing theorems apply on each side, and the middle equality is just the
Fourier-pairing symmetry above. -/
theorem fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
    {n m : ℕ}
    {φ : SchwartzNPoint d n}
    {ψ : SchwartzNPoint d m}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {g : euclideanPositiveTimeSubmodule (d := d) m}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    (rφ : Fin n) (tφ : Fin n → ℝ)
    (htφ : ∀ i : Fin n, i ≠ rφ → 0 ≤ tφ i)
    (ξφ : EuclideanSpace ℝ (Fin n × Fin d))
    (rψ : Fin m) (tψ : Fin m → ℝ)
    (htψ : ∀ i : Fin m, i ≠ rψ → 0 ≤ tψ i)
    (ξψ : EuclideanSpace ℝ (Fin m × Fin d)) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ rφ tφ ξφ)) =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m) ψ rψ tψ ξψ)) := by
  let φSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ rφ tφ ξφ
  let ψSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := m) ψ rψ tψ ξψ
  let fSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
      (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ
  let gSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
      (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ
  have hleft :
      fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) φSlice) =
        fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) fSlice) := by
    simpa [φSlice, fSlice, gSlice] using
      (fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_transport
        (d := d) (n := n) hφf
        (T := fourierInvPairingCLM gSlice)
        (hT_supp := fourierInvPairing_hasOneSidedFourierSupport gSlice
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := m) (EuclideanPositiveTimeComponent.ofSubmodule g)
            rψ tψ ξψ))
        rφ tφ htφ ξφ)
  have hright :
      fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) ψSlice) =
        fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) gSlice) := by
    simpa [ψSlice, fSlice, gSlice] using
      (fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_transport
        (d := d) (n := m) hψg
        (T := fourierInvPairingCLM fSlice)
        (hT_supp := fourierInvPairing_hasOneSidedFourierSupport fSlice
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f)
            rφ tφ ξφ))
        rψ tψ htψ ξψ)
  calc
    fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) φSlice) =
      fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) fSlice) := hleft
    _ =
      fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) gSlice) := by
        exact fourierInvPairingCLM_fourierTransform_symm gSlice fSlice
    _ =
      fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) ψSlice) := by
        symm
        exact hright

/-- Opposite-factor kernel form of the same bridge: once ambient
representatives `φ, ψ` come from positive-time preimages `f, g`, the
one-variable pairing induced by the positive-time slice of `f` already kills
the ambient-minus-preimage slice difference on the opposite factor.

This is the scalar zero theorem that the later Stage-5 spatial-Fourier
factorization can consume directly when the surviving slice pairing happens to
land on the opposite side. -/
theorem fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
    {n m : ℕ}
    {φ : SchwartzNPoint d n}
    {ψ : SchwartzNPoint d m}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {g : euclideanPositiveTimeSubmodule (d := d) m}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    (rφ : Fin n) (tφ : Fin n → ℝ)
    (htφ : ∀ i : Fin n, i ≠ rφ → 0 ≤ tφ i)
    (ξφ : EuclideanSpace ℝ (Fin n × Fin d))
    (rψ : Fin m) (tψ : Fin m → ℝ)
    (htψ : ∀ i : Fin m, i ≠ rψ → 0 ≤ tψ i)
    (ξψ : EuclideanSpace ℝ (Fin m × Fin d)) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := m) ψ rψ tψ ξψ) -
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
              (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ))) = 0 := by
  let φSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ rφ tφ ξφ
  let ψSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := m) ψ rψ tψ ξψ
  let fSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
      (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ
  let gSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
      (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ
  have hleft_zero :
      fourierInvPairingCLM gSlice
          ((SchwartzMap.fourierTransformCLM ℂ) (φSlice - fSlice)) = 0 := by
    simpa [φSlice, fSlice, gSlice] using
      (fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
        (d := d) (n := n) (m := m) (φ := φ) (f := f) (g := g)
        hφf rφ tφ htφ ξφ rψ tψ htψ ξψ)
  have hleft :
      fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) φSlice) =
        fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) fSlice) := by
    exact sub_eq_zero.mp (by simpa [map_sub] using hleft_zero)
  have hopposite :
      fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) φSlice) =
        fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) ψSlice) := by
    simpa [φSlice, ψSlice, fSlice, gSlice] using
      (fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
        (d := d) (n := n) (m := m) (φ := φ) (ψ := ψ) (f := f) (g := g)
        hφf hψg rφ tφ htφ ξφ rψ tψ htψ ξψ)
  have hsymm :
      fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) fSlice) =
        fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) gSlice) := by
    exact fourierInvPairingCLM_fourierTransform_symm gSlice fSlice
  have hmain :
      fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) ψSlice) =
        fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) gSlice) := by
    calc
      fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) ψSlice) =
        fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) φSlice) := by
          symm
          exact hopposite
      _ =
        fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) fSlice) := hleft
      _ =
        fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) gSlice) := hsymm
  exact sub_eq_zero.mp (by simpa [map_sub] using sub_eq_zero.mpr hmain)

/-- Concrete positive-time `ξ`-shift shell on the actual reconstructed
continuation kernel `bvt_F`: on positive real times, the Euclidean/OS matrix
element for a positive-time pair is exactly the `ξ`-shift integral of `bvt_F`.

This is just the current-code specialization of
`schwinger_simpleTensor_timeShift_eq_xiShift` to the actual kernel used in the
Stage-5 positivity route. It removes one more layer of generic witness
bookkeeping before the remaining Lemma-4.2 boundary-value step. -/
private theorem bvt_F_osConjTensorProduct_timeShift_eq_xiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (t : ℝ) (ht : 0 < t) :
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) =
      ∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct g) y := by
  exact schwinger_simpleTensor_timeShift_eq_xiShift
    (d := d) (OS := OS) (hm := hm) (Ψ := bvt_F OS lgc (n + m))
    (hΨ_euclid := bvt_euclidean_restriction (d := d) OS lgc (n + m))
    (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) (t := t) ht

/-- Concrete ambient `ξ`-shift shell on the actual reconstructed continuation
kernel `bvt_F`: moving the positive real right-time shift from the ambient
Wightman-side test tensor to the continuation variable produces the same
`ξ`-shift integral.

Together with `bvt_F_osConjTensorProduct_timeShift_eq_xiShift`, this isolates
the remaining Stage-5 content to the one-variable boundary-value / time-variable
interchange, not further configuration-space shell algebra. -/
private theorem bvt_F_conjTensorProduct_timeShift_eq_xiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m) (t : ℝ) :
    ∫ x : NPointDomain d (n + m),
      bvt_F OS lgc (n + m) (fun i => wickRotatePoint (x i)) *
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x =
      ∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (φ.conjTensorProduct ψ) y := by
  simpa using
    (simpleTensor_timeShift_integral_eq_xiShift_conj
      (d := d) (n := n) (m := m) (hm := hm)
      (f := φ) (g := ψ) (t := t) (Ψ := bvt_F OS lgc (n + m)))

/-- Canonical-shell version of `bvt_F_conjTensorProduct_timeShift_eq_xiShift`:
moving the positive real right-time shift from the ambient Wightman-side test
tensor to the continuation variable on the exact boundary-value shell
`x + ε η₀ i` produces the corresponding raw `ξ`-shift shell.

This is the current Step-2 configuration-space rewrite for Lemma 4.2. Unlike
`bvt_F_conjTensorProduct_timeShift_eq_xiShift`, it works directly on the
forward-cone boundary-value shell that appears in `bvt_boundary_values`. -/
private theorem bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (t ε : ℝ) :
    ∫ x : NPointDomain d (n + m),
      bvt_F OS lgc (n + m) (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x =
      ∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ := fun z =>
    bvt_F OS lgc (n + m) (fun k μ =>
      (if μ = 0 then (-Complex.I) * z k μ else z k μ) +
        ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
  calc
    ∫ x : NPointDomain d (n + m),
        bvt_F OS lgc (n + m) (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x
      =
        ∫ x : NPointDomain d (n + m),
          Ψ (fun i => wickRotatePoint (x i)) *
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          have hshell :
              Ψ (fun i => wickRotatePoint (x i)) =
                bvt_F OS lgc (n + m) (fun k μ =>
                  ↑(x k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) := by
            unfold Ψ
            congr 1
            ext k μ
            by_cases hμ : μ = 0
            · subst hμ
              simp [wickRotatePoint]
              calc
                -(Complex.I * (Complex.I * ↑(x k 0))) =
                    -((Complex.I * Complex.I) * ↑(x k 0)) := by ring
                _ = -((-1 : ℂ) * ↑(x k 0)) := by rw [Complex.I_mul_I]
                _ = ↑(x k 0) := by ring
            · simp [wickRotatePoint, hμ]
          rw [hshell]
    _ =
        ∫ y : NPointDomain d (n + m),
          Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (φ.conjTensorProduct ψ) y := by
          exact simpleTensor_timeShift_integral_eq_xiShift_conj
            (d := d) (n := n) (m := m) (hm := hm)
            (f := φ) (g := ψ) (t := t) (Ψ := Ψ)
    _ =
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with y
          have hshell :
              Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) =
                bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun k μ =>
                      ↑(y k μ) +
                        ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
                    (t : ℂ)) := by
            unfold Ψ
            congr 1
            ext k μ
            by_cases hμ : μ = 0
            · subst hμ
              by_cases hk : n ≤ k.val
              · simp [wickRotatePoint, xiShift, hk]
                calc
                  -(Complex.I * (Complex.I * ↑(y k 0) + ↑t * Complex.I)) +
                      ↑ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k 0) * Complex.I
                      =
                    -(((Complex.I * Complex.I) * ↑(y k 0)) +
                        ((Complex.I * Complex.I) * ↑t)) +
                      ↑ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k 0) * Complex.I := by
                        ring
                  _ =
                    -(((-1 : ℂ) * ↑(y k 0)) + ((-1 : ℂ) * ↑t)) +
                      ↑ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k 0) * Complex.I := by
                        simp [Complex.I_mul_I]
                  _ =
                    ↑(y k 0) +
                      ↑ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k 0) * Complex.I +
                      ↑t := by
                        ring
              · simp [wickRotatePoint, xiShift, hk]
                calc
                  -(Complex.I * (Complex.I * ↑(y k 0))) =
                      -((Complex.I * Complex.I) * ↑(y k 0)) := by ring
                  _ = -((-1 : ℂ) * ↑(y k 0)) := by rw [Complex.I_mul_I]
                  _ = ↑(y k 0) := by ring
            · by_cases hk : n ≤ k.val
              · simp [wickRotatePoint, xiShift, hμ, hk]
              · simp [wickRotatePoint, xiShift, hμ, hk]
          rw [hshell]

/-- The corrected finite-height canonical shell is genuinely in the forward
tube. The real `ξ`-shift contributes no imaginary part, while the fixed
canonical direction contributes the positive forward-cone height. -/
private theorem canonicalXiShift_mem_forwardTube
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε)
    (y : NPointDomain d (n + m)) :
    xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun k μ =>
        ↑(y k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
            Complex.I)
      (t : ℂ) ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) := by
  change
    (fun k μ =>
      (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I)
        (t : ℂ) k μ).im) ∈ ForwardConeAbs d (n + m)
  have hη_abs :
      canonicalForwardConeDirection (d := d) (n + m) ∈ ForwardConeAbs d (n + m) :=
    (inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n + m)
      (canonicalForwardConeDirection (d := d) (n + m))).mp
      (canonicalForwardConeDirection_mem (d := d) (n + m))
  have hscaled :
      ε • canonicalForwardConeDirection (d := d) (n + m) ∈ ForwardConeAbs d (n + m) :=
    forwardConeAbs_smul d (n + m) ε hε
      (canonicalForwardConeDirection (d := d) (n + m)) hη_abs
  convert hscaled using 1
  ext k μ
  by_cases hshift : (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤ k.val ∧
      μ = (0 : Fin (d + 1))
  · simp [xiShift, hshift]
  · simp [xiShift, hshift]

/-- The fixed-time canonical shell map is an affine smooth map on the real
configuration space. This is the domain-side smoothness input for any later
attempt to package the restricted shell coefficient as a temperate-growth
function. -/
private theorem contDiff_canonicalXiShift
    {n m : ℕ} (hm : 0 < m)
    (t ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : NPointDomain d (n + m) =>
        xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) := by
  rw [contDiff_pi]
  intro k
  rw [contDiff_pi]
  intro μ
  have hcoord :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : NPointDomain d (n + m) => ((y k μ : ℝ) : ℂ)) := by
    simpa using (Complex.ofRealCLM.contDiff.comp
      (contDiff_apply_apply (𝕜 := ℝ) (ι := Fin (n + m)) (ι' := Fin (d + 1)) (E := ℝ)
        (n := (⊤ : ℕ∞)) (i := k) (j := μ) :
        ContDiff ℝ (⊤ : ℕ∞) (fun y : NPointDomain d (n + m) => y k μ)))
  by_cases hshift : (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤ k.val ∧
      μ = (0 : Fin (d + 1))
  · simp [xiShift, hshift]
    have hcoord0 :
        ContDiff ℝ (⊤ : ℕ∞) (fun y : NPointDomain d (n + m) => ((y k 0 : ℝ) : ℂ)) := by
      simpa [hshift.2] using hcoord
    simpa [add_assoc] using hcoord0.add (contDiff_const.add contDiff_const)
  · simp [xiShift, hshift]
    exact hcoord.add contDiff_const

/-- Pointwise real differentiability of the affine fixed-time canonical shell
map. This is the exact local bridge from `contDiff_canonicalXiShift` needed at
the shell-derivative insertion point. -/
private theorem differentiableAt_canonicalXiShift
    {n m : ℕ} (hm : 0 < m)
    (t ε : ℝ) (y : NPointDomain d (n + m)) :
    DifferentiableAt ℝ
      (fun y : NPointDomain d (n + m) =>
        xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) y := by
  let hdiff : Differentiable ℝ
      (fun y : NPointDomain d (n + m) =>
        xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) :=
    (contDiff_canonicalXiShift (d := d) hm t ε).differentiable (by simp)
  exact hdiff y

/-- Pointwise real Fréchet derivative bridge for the affine fixed-time
canonical shell map. This packages the already-landed differentiability result
at the exact domain-side shell surface needed by the next chain-rule step. -/
private theorem hasFDerivAt_canonicalXiShift
    {n m : ℕ} (hm : 0 < m)
    (t ε : ℝ) (y : NPointDomain d (n + m)) :
    HasFDerivAt
      (fun y : NPointDomain d (n + m) =>
        xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ))
      (fderiv ℝ
        (fun y : NPointDomain d (n + m) =>
          xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) y)
      y := by
  exact (differentiableAt_canonicalXiShift (d := d) hm t ε y).hasFDerivAt

/-- Continuity of the fixed-radius Paley-Wiener Schwartz family along the
flattened finite-height canonical shell. This is the continuity side condition
for the shell-side `schwartz_clm_fubini_exchange` packet. -/
private theorem continuous_canonicalShellPsiZExtFamily
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε)
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m))) :
    Continuous (fun yflat : Fin ((n + m) * (d + 1)) → ℝ =>
      multiDimPsiZExt
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m))
        hCflat_open hCflat_conv hCflat_cone hCflat_salient
        (flattenCLEquiv (n + m) (d + 1)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)))) := by
  let Cflat : Set (Fin ((n + m) * (d + 1)) → ℝ) :=
    (flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m)
  let zMap : (Fin ((n + m) * (d + 1)) → ℝ) → Fin ((n + m) * (d + 1)) → ℂ :=
    fun yflat =>
      flattenCLEquiv (n + m) (d + 1)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ))
  have hz_cont : Continuous zMap := by
    dsimp [zMap]
    apply continuous_pi
    intro a
    by_cases hshift : (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤
        (finProdFinEquiv.symm a).1.val ∧ (finProdFinEquiv.symm a).2 = (0 : Fin (d + 1))
    · simp [flattenCLEquiv_apply, xiShift]
      continuity
    · simp [flattenCLEquiv_apply, xiShift]
      continuity
  have hz_mem : ∀ yflat, zMap yflat ∈ SCV.TubeDomain Cflat := by
    intro yflat
    dsimp [zMap, Cflat]
    apply flattenCLEquiv_mem_tubeDomain_image
    exact canonicalXiShift_mem_forwardTube (d := d) hm hε
      ((flattenCLEquivReal (n + m) (d + 1)).symm yflat)
  simpa [Cflat, zMap] using
    continuous_multiDimPsiZExt_comp_of_mem_tube
      Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient zMap hz_cont hz_mem

/-- Polynomial seminorm growth of the fixed-radius Paley-Wiener Schwartz family
along the flattened finite-height canonical shell. This is the growth side
condition for the shell-side `schwartz_clm_fubini_exchange` packet. -/
private theorem seminorm_canonicalShellPsiZExtFamily_bound
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε)
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m))) :
    ∀ (k l : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧
      ∀ yflat : Fin ((n + m) * (d + 1)) → ℝ,
        SchwartzMap.seminorm ℝ k l
          (multiDimPsiZExt
            ((flattenCLEquivReal (n + m) (d + 1)) ''
              ForwardConeAbs d (n + m))
            hCflat_open hCflat_conv hCflat_cone hCflat_salient
            (flattenCLEquiv (n + m) (d + 1)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)))) ≤
          C * (1 + ‖yflat‖) ^ N := by
  intro k l
  let Cflat : Set (Fin ((n + m) * (d + 1)) → ℝ) :=
    (flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m)
  let ηShell : Fin ((n + m) * (d + 1)) → ℝ :=
    flattenCLEquivReal (n + m) (d + 1)
      (ε • canonicalForwardConeDirection (d := d) (n + m))
  let zMap : (Fin ((n + m) * (d + 1)) → ℝ) → Fin ((n + m) * (d + 1)) → ℂ :=
    fun yflat =>
      flattenCLEquiv (n + m) (d + 1)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ))
  let xShell : (Fin ((n + m) * (d + 1)) → ℝ) → Fin ((n + m) * (d + 1)) → ℝ :=
    fun yflat a => (zMap yflat a).re
  have hη_abs :
      canonicalForwardConeDirection (d := d) (n + m) ∈ ForwardConeAbs d (n + m) :=
    (inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n + m)
      (canonicalForwardConeDirection (d := d) (n + m))).mp
      (canonicalForwardConeDirection_mem (d := d) (n + m))
  have hη_scaled :
      ε • canonicalForwardConeDirection (d := d) (n + m) ∈ ForwardConeAbs d (n + m) :=
    forwardConeAbs_smul d (n + m) ε hε
      (canonicalForwardConeDirection (d := d) (n + m)) hη_abs
  have hηShell_mem : ηShell ∈ Cflat := by
    exact ⟨ε • canonicalForwardConeDirection (d := d) (n + m), hη_scaled, rfl⟩
  obtain ⟨B, N, hB, hBbound⟩ :=
    multiDimPsiZExt_fixedImaginary_seminorm_bound
      Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient hηShell_mem k l
  let A : ℝ := 1 + |t|
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hxShell_norm :
      ∀ yflat : Fin ((n + m) * (d + 1)) → ℝ,
        ‖xShell yflat‖ ≤ A * (1 + ‖yflat‖) := by
    intro yflat
    have hsymm_norm :
        ‖(flattenCLEquivReal (n + m) (d + 1)).symm yflat‖ = ‖yflat‖ := by
      simpa using
        (flattenCLEquivReal_norm_eq (n + m) (d + 1)
          ((flattenCLEquivReal (n + m) (d + 1)).symm yflat)).symm
    have hcoord :
        ∀ a : Fin ((n + m) * (d + 1)),
          |((flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2)| ≤ ‖yflat‖ := by
      intro a
      calc
        |((flattenCLEquivReal (n + m) (d + 1)).symm yflat
            (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2)|
            = ‖((flattenCLEquivReal (n + m) (d + 1)).symm yflat
                (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2)‖ := by
                rw [Real.norm_eq_abs]
        _ ≤ ‖(flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1‖ :=
            norm_le_pi_norm _ (finProdFinEquiv.symm a).2
        _ ≤ ‖(flattenCLEquivReal (n + m) (d + 1)).symm yflat‖ :=
            norm_le_pi_norm _ (finProdFinEquiv.symm a).1
        _ = ‖yflat‖ := hsymm_norm
    have hnonneg : 0 ≤ A * (1 + ‖yflat‖) := by positivity
    apply (pi_norm_le_iff_of_nonneg hnonneg).2
    intro a
    by_cases hshift : (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤
        (finProdFinEquiv.symm a).1.val ∧ (finProdFinEquiv.symm a).2 = (0 : Fin (d + 1))
    · have hre :
          xShell yflat a =
            (flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 + t := by
        have hshift' : n ≤ a.val / (d + 1) ∧ a.modNat = (0 : Fin (d + 1)) := by
          simpa using hshift
        simp [xShell, zMap, flattenCLEquiv_apply, xiShift, hshift']
      calc
        ‖xShell yflat a‖ = |xShell yflat a| := Real.norm_eq_abs _
        _ = |(flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 + t| := by rw [hre]
        _ ≤ |(flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2| + |t| :=
            abs_add_le _ _
        _ ≤ ‖yflat‖ + |t| := by
            gcongr
            exact hcoord a
        _ ≤ A * (1 + ‖yflat‖) := by
            dsimp [A]
            nlinarith [norm_nonneg yflat, abs_nonneg t]
    · have hre :
          xShell yflat a =
            (flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 := by
        have hshift' : ¬ (n ≤ a.val / (d + 1) ∧ a.modNat = (0 : Fin (d + 1))) := by
          simpa using hshift
        simp [xShell, zMap, flattenCLEquiv_apply, xiShift, hshift']
      calc
        ‖xShell yflat a‖ = |xShell yflat a| := Real.norm_eq_abs _
        _ = |(flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2| := by rw [hre]
        _ ≤ ‖yflat‖ := hcoord a
        _ ≤ A * (1 + ‖yflat‖) := by
            dsimp [A]
            nlinarith [norm_nonneg yflat, abs_nonneg t]
  let C : ℝ := B * (1 + A) ^ N
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, N, hC_pos, ?_⟩
  intro yflat
  have hz_decomp :
      zMap yflat =
        fun a => ((xShell yflat a : ℝ) : ℂ) + (ηShell a : ℂ) * Complex.I := by
    ext a
    apply Complex.ext
    · simp [xShell]
    · have him : (zMap yflat a).im = ηShell a := by
        by_cases hshift : (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤
            (finProdFinEquiv.symm a).1.val ∧
              (finProdFinEquiv.symm a).2 = (0 : Fin (d + 1))
        · have hshift' : n ≤ a.val / (d + 1) ∧ a.modNat = (0 : Fin (d + 1)) := by
            simpa using hshift
          simp [zMap, ηShell, flattenCLEquiv_apply, flattenCLEquivReal_apply, xiShift, hshift']
        · have hshift' : ¬ (n ≤ a.val / (d + 1) ∧ a.modNat = (0 : Fin (d + 1))) := by
            simpa using hshift
          simp [zMap, ηShell, flattenCLEquiv_apply, flattenCLEquivReal_apply, xiShift, hshift']
      simp [him]
  have hbase :
      SchwartzMap.seminorm ℝ k l
        (multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
          (zMap yflat)) ≤
        B * (1 + ‖xShell yflat‖) ^ N := by
    rw [hz_decomp]
    exact hBbound (xShell yflat)
  have hpoly :
      (1 + ‖xShell yflat‖) ^ N ≤ (1 + A) ^ N * (1 + ‖yflat‖) ^ N := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by linarith [norm_nonneg (xShell yflat)])
    calc
      1 + ‖xShell yflat‖ ≤ 1 + A * (1 + ‖yflat‖) := by
        linarith [hxShell_norm yflat]
      _ ≤ (1 + A) * (1 + ‖yflat‖) := by
        have hy_nonneg : 0 ≤ ‖yflat‖ := norm_nonneg yflat
        nlinarith [hA_pos.le, hy_nonneg]
  have hfinal :
      SchwartzMap.seminorm ℝ k l
        (multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
          (zMap yflat)) ≤
        C * (1 + ‖yflat‖) ^ N := by
    calc
      SchwartzMap.seminorm ℝ k l
          (multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
            (zMap yflat))
          ≤ B * (1 + ‖xShell yflat‖) ^ N := hbase
      _ ≤ B * ((1 + A) ^ N * (1 + ‖yflat‖) ^ N) := by
          gcongr
      _ = C * (1 + ‖yflat‖) ^ N := by
          dsimp [C]
          ring
  simpa [Cflat, zMap] using hfinal

/-- Flat Fubini packet for the fixed-radius Paley-Wiener Schwartz family along
the finite-height canonical shell. This packages the `KShell` produced by
`schwartz_clm_fubini_exchange`; boundary-value rewriting is kept for the next
lemma. -/
private theorem canonicalShellPsiZExtFamily_pairing
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε)
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (fFlat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ) :
    ∃ KShell : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      (∀ ξ : Fin ((n + m) * (d + 1)) → ℝ,
        KShell ξ =
          ∫ yflat : Fin ((n + m) * (d + 1)) → ℝ,
            (multiDimPsiZExt
              ((flattenCLEquivReal (n + m) (d + 1)) ''
                ForwardConeAbs d (n + m))
              hCflat_open hCflat_conv hCflat_cone hCflat_salient
              (flattenCLEquiv (n + m) (d + 1)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)))) ξ *
              fFlat yflat) ∧
      (∫ yflat : Fin ((n + m) * (d + 1)) → ℝ,
        Tflat
          (multiDimPsiZExt
            ((flattenCLEquivReal (n + m) (d + 1)) ''
              ForwardConeAbs d (n + m))
            hCflat_open hCflat_conv hCflat_cone hCflat_salient
            (flattenCLEquiv (n + m) (d + 1)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)))) *
          fFlat yflat) =
        Tflat KShell := by
  let Cflat : Set (Fin ((n + m) * (d + 1)) → ℝ) :=
    (flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m)
  let gFamily : (Fin ((n + m) * (d + 1)) → ℝ) →
      SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ :=
    fun yflat =>
      multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
        (flattenCLEquiv (n + m) (d + 1)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)))
  have hg_cont : Continuous gFamily := by
    simpa [Cflat, gFamily] using
      continuous_canonicalShellPsiZExtFamily (d := d) hm hε
        hCflat_open hCflat_conv hCflat_cone hCflat_salient
  have hg_bound :
      ∀ (k l : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
        ∀ yflat : Fin ((n + m) * (d + 1)) → ℝ,
          SchwartzMap.seminorm ℝ k l (gFamily yflat) ≤ C * (1 + ‖yflat‖) ^ N := by
    simpa [Cflat, gFamily] using
      seminorm_canonicalShellPsiZExtFamily_bound (d := d) hm hε
        hCflat_open hCflat_conv hCflat_cone hCflat_salient
  obtain ⟨KShell, _hKShell_eval, hKShell_pair⟩ :=
    schwartz_clm_fubini_exchange Tflat gFamily fFlat hg_cont hg_bound
  refine ⟨KShell, ?_, ?_⟩
  · intro ξ
    simpa [Cflat, gFamily] using _hKShell_eval ξ
  · simpa [Cflat, gFamily] using hKShell_pair.symm

/-- Shell-side boundary-value integral as a flattened Paley-Wiener/Fubini
kernel pairing. This combines the `bvt_F` Fourier-Laplace representation with
the flat shell Fubini packet. -/
private theorem exists_shellKernel_pairing_canonicalXiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    {t ε : ℝ} (hε : 0 < ε)
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hFL :
      ∀ z : Fin (n + m) → Fin (d + 1) → ℂ,
        z ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) →
          bvt_F OS lgc (n + m) z =
            fourierLaplaceExtMultiDim
              ((flattenCLEquivReal (n + m) (d + 1)) ''
                ForwardConeAbs d (n + m))
              hCflat_open hCflat_conv hCflat_cone hCflat_salient
              Tflat (flattenCLEquiv (n + m) (d + 1) z)) :
    ∃ KShell : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      (∀ ξ : Fin ((n + m) * (d + 1)) → ℝ,
        KShell ξ =
          ∫ yflat : Fin ((n + m) * (d + 1)) → ℝ,
            (multiDimPsiZExt
              ((flattenCLEquivReal (n + m) (d + 1)) ''
                ForwardConeAbs d (n + m))
              hCflat_open hCflat_conv hCflat_cone hCflat_salient
              (flattenCLEquiv (n + m) (d + 1)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)))) ξ *
              _root_.flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ) yflat) ∧
      (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) =
        Tflat KShell := by
  let Cflat : Set (Fin ((n + m) * (d + 1)) → ℝ) :=
    (flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m)
  let zShell :
      (Fin ((n + m) * (d + 1)) → ℝ) → Fin (n + m) → Fin (d + 1) → ℂ :=
    fun yflat =>
      xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun k μ =>
          (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I)
        (t : ℂ)
  let gFlat : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ :=
    fun yflat =>
      Tflat
        (multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
          (flattenCLEquiv (n + m) (d + 1) (zShell yflat))) *
        _root_.flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ) yflat
  obtain ⟨KShell, hKShell_eval, hKShell⟩ :=
    canonicalShellPsiZExtFamily_pairing (d := d) hm hε
      hCflat_open hCflat_conv hCflat_cone hCflat_salient Tflat
      (_root_.flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ))
  refine ⟨KShell, ?_, ?_⟩
  · simpa [Cflat, zShell] using hKShell_eval
  have hflat_cv :
      ∫ yflat : Fin ((n + m) * (d + 1)) → ℝ, gFlat yflat =
        ∫ y : NPointDomain d (n + m),
          gFlat (flattenCLEquivReal (n + m) (d + 1) y) :=
    integral_flatten_change_of_variables (n + m) (d + 1) gFlat
  have htarget_to_flat :
      (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) =
        ∫ y : NPointDomain d (n + m),
          gFlat (flattenCLEquivReal (n + m) (d + 1) y) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    let shellY : Fin (n + m) → Fin (d + 1) → ℂ :=
      xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I)
        (t : ℂ)
    have hzShell_flat :
        zShell (flattenCLEquivReal (n + m) (d + 1) y) = shellY := by
      ext k μ
      simp [zShell, shellY]
    have hshell_mem : shellY ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) := by
      simpa [shellY] using canonicalXiShift_mem_forwardTube (d := d) hm hε y
    have hbvt :
        bvt_F OS lgc (n + m) shellY =
          Tflat
            (multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
              (flattenCLEquiv (n + m) (d + 1) shellY)) := by
      calc
        bvt_F OS lgc (n + m) shellY
            = fourierLaplaceExtMultiDim Cflat hCflat_open hCflat_conv hCflat_cone
                hCflat_salient Tflat (flattenCLEquiv (n + m) (d + 1) shellY) :=
              hFL shellY hshell_mem
        _ = Tflat
              (multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
                (flattenCLEquiv (n + m) (d + 1) shellY)) := by
              rw [fourierLaplaceExtMultiDim_eq_ext]
    simp [gFlat, Cflat, hzShell_flat, hbvt, shellY, _root_.flattenSchwartzNPoint_apply]
  calc
    (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y)
        = ∫ y : NPointDomain d (n + m),
            gFlat (flattenCLEquivReal (n + m) (d + 1) y) := htarget_to_flat
    _ = ∫ yflat : Fin ((n + m) * (d + 1)) → ℝ, gFlat yflat := hflat_cv.symm
    _ = Tflat KShell := by
      simpa [gFlat, Cflat, zShell] using hKShell

/-- The chosen boundary-value continuation `bvt_F` inherits the global forward-
tube polynomial-growth package from
`full_analytic_continuation_with_symmetry_growth`. This keeps the current
Stage-5 shell work on the theorem-based OS continuation rather than routing
through any extra placeholder witness. -/
private theorem bvt_F_hasGlobalForwardTubeGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (C_bd : ℝ) (N : ℕ),
      0 < C_bd ∧
      ∀ z ∈ ForwardTube d k,
        ‖bvt_F OS lgc k z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
  rcases (full_analytic_continuation_with_symmetry_growth OS lgc k).choose_spec with
    ⟨_hhol, hrest⟩
  rcases hrest with ⟨_hEuclid, hrest⟩
  rcases hrest with ⟨_hPerm, hrest⟩
  rcases hrest with ⟨_hTrans, hrest⟩
  exact hrest.2

/-- Shell-specialized zeroth-order polynomial growth for the fixed-time
canonical `ξ`-shift coefficient. This is the precise shell-level consequence
already available from the current forward-tube growth package; higher
iterated real derivative bounds remain the first missing step toward
`Function.HasTemperateGrowth`. -/
private theorem bvt_F_canonicalXiShift_hasPolynomialGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε) :
    ∃ (C_bd : ℝ) (N : ℕ),
      0 < C_bd ∧
      ∀ y : NPointDomain d (n + m),
        ‖bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ))‖ ≤
          C_bd * (1 + ‖y‖) ^ N := by
  obtain ⟨C0, N, hC0_pos, hgrowth⟩ :=
    bvt_F_hasGlobalForwardTubeGrowth (d := d) OS lgc (n + m)
  let shift :
      Fin (n + m) → Fin (d + 1) → ℂ :=
    fun k μ =>
      (if (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤ k.val ∧
            μ = (0 : Fin (d + 1)) then
          (t : ℂ)
        else
          0) +
        ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I
  have hreal_norm :
      ∀ y : NPointDomain d (n + m),
        ‖(fun k μ => ((y k μ : ℝ) : ℂ))‖ ≤ ‖y‖ := by
    intro y
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 ?_
    intro k
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 ?_
    intro μ
    calc
      ‖(((y k μ : ℝ) : ℂ))‖ = |y k μ| := by simp
      _ = ‖y k μ‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖y k‖ := norm_le_pi_norm _ μ
      _ ≤ ‖y‖ := norm_le_pi_norm _ k
  let C_bd : ℝ := C0 * (1 + ‖shift‖) ^ N
  have hC_bd_pos : 0 < C_bd := by
    dsimp [C_bd]
    positivity
  refine ⟨C_bd, N, hC_bd_pos, ?_⟩
  intro y
  let shellY : Fin (n + m) → Fin (d + 1) → ℂ :=
    xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun k μ =>
        ↑(y k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
            Complex.I)
      (t : ℂ)
  have hshell_mem : shellY ∈ ForwardTube d (n + m) := by
    simpa [forwardTube_eq_imPreimage] using
      canonicalXiShift_mem_forwardTube (d := d) hm hε y
  have hshell_decomp :
      shellY = fun k μ => (((y k μ : ℝ) : ℂ)) + shift k μ := by
    ext k μ
    by_cases hshift : (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤ k.val ∧
        μ = (0 : Fin (d + 1))
    · simp [shellY, shift, xiShift, hshift]
      ring_nf
    · simp [shellY, shift, xiShift, hshift]
  have hshell_norm :
      ‖shellY‖ ≤ ‖y‖ + ‖shift‖ := by
    rw [hshell_decomp]
    calc
      ‖fun k μ => (((y k μ : ℝ) : ℂ)) + shift k μ‖
          ≤ ‖fun k μ => (((y k μ : ℝ) : ℂ))‖ + ‖shift‖ := norm_add_le _ _
      _ ≤ ‖y‖ + ‖shift‖ := by
          gcongr
          exact hreal_norm y
  have hshell_growth :
      1 + ‖shellY‖ ≤ (1 + ‖shift‖) * (1 + ‖y‖) := by
    have hstep : 1 + ‖shellY‖ ≤ 1 + (‖y‖ + ‖shift‖) := by
      linarith
    have hprod : 1 + (‖y‖ + ‖shift‖) ≤ (1 + ‖shift‖) * (1 + ‖y‖) := by
      nlinarith [norm_nonneg y, norm_nonneg shift]
    exact hstep.trans hprod
  calc
    ‖bvt_F OS lgc (n + m) shellY‖ ≤ C0 * (1 + ‖shellY‖) ^ N := hgrowth shellY hshell_mem
    _ ≤ C0 * ((1 + ‖shift‖) * (1 + ‖y‖)) ^ N := by
        gcongr
    _ = C_bd * (1 + ‖y‖) ^ N := by
        dsimp [C_bd]
        rw [mul_pow]
        ring

/-- The raw ambient fixed-time shell functional at positive imaginary height,
packaged as a continuous linear functional on the full ambient Schwartz space
before any Section 4.3 kernel or quotient descent. -/
private noncomputable def section43_fixedTimeShellRawCLM
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t ε : ℝ) (hε : 0 < ε) :
    SchwartzNPoint d (n + m) →L[ℂ] ℂ := by
  set coeff : NPointDomain d (n + m) → ℂ := fun y =>
    bvt_F OS lgc (n + m)
      (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I)
        (t : ℂ))
  have hcoeff_cont : Continuous coeff := by
    rw [continuous_iff_continuousAt]
    intro y
    let shellMap : NPointDomain d (n + m) → Fin (n + m) → Fin (d + 1) → ℂ :=
      fun y =>
        xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)
    have hshell_mem : shellMap y ∈ ForwardTube d (n + m) := by
      simpa [shellMap, forwardTube_eq_imPreimage] using
        canonicalXiShift_mem_forwardTube (d := d) hm hε y
    have houter_cont : ContinuousAt (bvt_F OS lgc (n + m)) (shellMap y) := by
      let hft_open :
          IsOpen (ForwardTube d (n + m)) := by
        simpa [BHW_forwardTube_eq (d := d) (n := n + m)] using
          (BHW.isOpen_forwardTube (d := d) (n := n + m))
      have houter_diff :
          DifferentiableAt ℂ (bvt_F OS lgc (n + m)) (shellMap y) :=
        (bvt_F_holomorphic (d := d) OS lgc (n + m)).differentiableAt
          (hft_open.mem_nhds hshell_mem)
      exact houter_diff.continuousAt
    have hinner_cont : ContinuousAt shellMap y :=
      (contDiff_canonicalXiShift (d := d) hm t ε).continuous.continuousAt
    simpa [coeff, shellMap] using houter_cont.comp hinner_cont
  have hcoeff_meas :
      MeasureTheory.AEStronglyMeasurable coeff MeasureTheory.volume :=
    hcoeff_cont.aestronglyMeasurable
  let growth :=
    bvt_F_canonicalXiShift_hasPolynomialGrowth
      (d := d) (n := n) (m := m) OS lgc hm (t := t) (ε := ε) hε
  let C_bd : ℝ := Classical.choose growth
  let N : ℕ := Classical.choose (Classical.choose_spec growth)
  have hC_bd : 0 < C_bd := by
    exact (Classical.choose_spec (Classical.choose_spec growth)).1
  have hcoeff_bound :
      ∀ y : NPointDomain d (n + m), ‖coeff y‖ ≤ C_bd * (1 + ‖y‖) ^ N := by
    exact (Classical.choose_spec (Classical.choose_spec growth)).2
  letI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d (n + m))) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  letI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d (n + m))).HasTemperateGrowth :=
    MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
  have h_binom_ineq : ∀ s : ℝ, 0 ≤ s → (1 + s) ^ N ≤ 2 ^ N * (1 + s ^ N) := by
    intro s hs
    have h2s : 1 + s ≤ 2 * max 1 s := by
      calc
        1 + s ≤ max 1 s + max 1 s := add_le_add (le_max_left _ _) (le_max_right _ _)
        _ = 2 * max 1 s := by ring
    calc
      (1 + s) ^ N ≤ (2 * max 1 s) ^ N := pow_le_pow_left₀ (by positivity) h2s N
      _ = 2 ^ N * (max 1 s) ^ N := by rw [mul_pow]
      _ ≤ 2 ^ N * (1 + s ^ N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases le_total s 1 with h | h
          · rw [max_eq_left h]
            simp [one_pow]
            linarith [pow_nonneg hs N]
          · rw [max_eq_right h]
            linarith [show (1 : ℝ) ^ N = 1 from one_pow N]
  have hcoeff_mul_integrable :
      ∀ h : SchwartzNPoint d (n + m),
        MeasureTheory.Integrable
          (fun y : NPointDomain d (n + m) => coeff y * h y) MeasureTheory.volume := by
    intro h
    have hh_int : MeasureTheory.Integrable (fun y : NPointDomain d (n + m) => ‖h y‖)
        MeasureTheory.volume := by
      simpa using h.integrable.norm
    have hh_pow_int :
        MeasureTheory.Integrable
          (fun y : NPointDomain d (n + m) => ‖y‖ ^ N * ‖h y‖) MeasureTheory.volume := by
      simpa using h.integrable_pow_mul (μ := MeasureTheory.volume) N
    have hmajorant_int :
        MeasureTheory.Integrable
          (fun y : NPointDomain d (n + m) =>
            C_bd * 2 ^ N * (‖h y‖ + ‖y‖ ^ N * ‖h y‖))
          MeasureTheory.volume :=
      (hh_int.add hh_pow_int).const_mul (C_bd * 2 ^ N)
    apply hmajorant_int.mono' (hcoeff_meas.mul h.integrable.aestronglyMeasurable)
    filter_upwards [Filter.Eventually.of_forall hcoeff_bound] with y hy
    change ‖coeff y * h y‖ ≤ C_bd * 2 ^ N * (‖h y‖ + ‖y‖ ^ N * ‖h y‖)
    rw [norm_mul]
    calc
      ‖coeff y‖ * ‖h y‖ ≤ C_bd * (1 + ‖y‖) ^ N * ‖h y‖ :=
        mul_le_mul_of_nonneg_right hy (norm_nonneg _)
      _ ≤ C_bd * (2 ^ N * (1 + ‖y‖ ^ N)) * ‖h y‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left
            (h_binom_ineq ‖y‖ (norm_nonneg _)) (le_of_lt hC_bd)
      _ = C_bd * 2 ^ N * (‖h y‖ + ‖y‖ ^ N * ‖h y‖) := by ring
  refine ContinuousLinearMap.mk
    { toFun := fun h => ∫ y : NPointDomain d (n + m), coeff y * h y
      map_add' := by
        intro h1 h2
        simpa [Pi.add_apply, mul_add] using
          (MeasureTheory.integral_add
            (hcoeff_mul_integrable h1) (hcoeff_mul_integrable h2))
      map_smul' := by
        intro a h
        calc
          ∫ y : NPointDomain d (n + m), coeff y * (a • h) y
              = ∫ y : NPointDomain d (n + m), a * (coeff y * h y) := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with y
                  simp [Pi.smul_apply, smul_eq_mul]
                  ring
          _ = a * ∫ y : NPointDomain d (n + m), coeff y * h y := by
                  exact MeasureTheory.integral_const_mul a _ } ?_
  exact schwartz_continuous_of_polynomial_bound (d := d) coeff hcoeff_meas
    C_bd N hC_bd (Filter.Eventually.of_forall hcoeff_bound)

/-- Fixed-time branch normalization for the translated shell:
`xiShift` at the theorem-3 shell index is the ambient configuration plus the
single real-time indicator shift on the zero-th coordinate. This is the exact
local affine form needed for the next translated-shell growth comparison. -/
private theorem section43_fixedTime_xiShift_zero_eq_add_indicator
    {n m : ℕ} (hm : 0 < m) (t : ℝ)
    (z : Fin (n + m) → Fin (d + 1) → ℂ) :
    xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ) =
      fun k μ =>
        z k μ +
          if (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤ k.val ∧
              μ = (0 : Fin (d + 1)) then
            (t : ℂ)
          else
            0 := by
  ext k μ
  by_cases hshift : (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤ k.val ∧
      μ = (0 : Fin (d + 1))
  · simp [xiShift, hshift]
  · simp [xiShift, hshift]

/-- Global forward-tube polynomial growth for the fixed-time translated shell
continuation obtained by shifting the theorem-3 shell index in the real time
direction. This is the exact growth transfer needed before applying the generic
boundary-value constructor at the first fixed-time shell insertion surface. -/
private theorem section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m) (t : ℝ) :
    ∃ (C_bd : ℝ) (N : ℕ),
      0 < C_bd ∧
      ∀ z ∈ ForwardTube d (n + m),
        ‖bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))‖ ≤
          C_bd * (1 + ‖z‖) ^ N := by
  obtain ⟨C0, N, hC0_pos, hgrowth⟩ :=
    bvt_F_hasGlobalForwardTubeGrowth (d := d) OS lgc (n + m)
  let shift :
      Fin (n + m) → Fin (d + 1) → ℂ :=
    fun k μ =>
      if (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤ k.val ∧
          μ = (0 : Fin (d + 1)) then
        (t : ℂ)
      else
        0
  let C_bd : ℝ := C0 * (1 + ‖shift‖) ^ N
  have hC_bd_pos : 0 < C_bd := by
    dsimp [C_bd]
    positivity
  refine ⟨C_bd, N, hC_bd_pos, ?_⟩
  intro z hz
  have hz_shift_mem :
      xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ) ∈ ForwardTube d (n + m) := by
    rw [forwardTube_eq_imPreimage] at hz ⊢
    have him :
        (fun k μ =>
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ) k μ).im) =
          fun k μ => (z k μ).im := by
      ext k μ
      by_cases hshift : (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤ k.val ∧
          μ = (0 : Fin (d + 1))
      · simp [xiShift, hshift]
      · simp [xiShift, hshift]
    simpa [Set.mem_setOf_eq, him] using hz
  have hshift_decomp :
      xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ) =
        fun k μ => z k μ + shift k μ := by
    simpa [shift] using
      section43_fixedTime_xiShift_zero_eq_add_indicator (d := d) hm t z
  have hshift_norm :
      ‖xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ)‖ ≤ ‖z‖ + ‖shift‖ := by
    rw [hshift_decomp]
    exact norm_add_le _ _
  have hshift_growth :
      1 + ‖xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ)‖ ≤
        (1 + ‖shift‖) * (1 + ‖z‖) := by
    have hstep : 1 + ‖xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ)‖ ≤
        1 + (‖z‖ + ‖shift‖) := by
      linarith
    have hprod : 1 + (‖z‖ + ‖shift‖) ≤ (1 + ‖shift‖) * (1 + ‖z‖) := by
      nlinarith [norm_nonneg z, norm_nonneg shift]
    exact hstep.trans hprod
  calc
    ‖bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))‖
        ≤ C0 * (1 + ‖xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ)‖) ^ N := by
            exact hgrowth _ hz_shift_mem
    _ ≤ C0 * ((1 + ‖shift‖) * (1 + ‖z‖)) ^ N := by
          gcongr
    _ = C_bd * (1 + ‖z‖) ^ N := by
          dsimp [C_bd]
          rw [mul_pow]
          ring

/-- Fixed-time shell-local uniform polynomial growth for the raw theorem-3
kernel on heights `0 < ε < 1`.

This is the smaller shell-side bridge directly beneath the eventual
finite-seminorm bound on `section43_fixedTimeShellRawCLM`: before integrating
against Schwartz tests, the translated shell coefficient already admits one
common polynomial-growth bound independent of the shell height. -/
private theorem section43_fixedTimeShellRaw_uniformPolyGrowth_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m) (t : ℝ) :
    ∃ (C_shell : ℝ) (N : ℕ), 0 < C_shell ∧
      ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ hε_lt : ε < 1,
      ∀ y : NPointDomain d (n + m),
        ‖bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ))‖ ≤
          C_shell * (1 + ‖y‖) ^ N := by
  obtain ⟨C_bd, N, hC_bd_pos, hgrowth⟩ :=
    section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth
      (d := d) OS lgc hm t
  let η : Fin (n + m) → Fin (d + 1) → ℝ :=
    canonicalForwardConeDirection (d := d) (n + m)
  refine ⟨C_bd * (1 + ‖η‖) ^ N, N, mul_pos hC_bd_pos (pow_pos (by positivity) _), ?_⟩
  intro ε hε hε_lt y
  let z : Fin (n + m) → Fin (d + 1) → ℂ :=
    fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I
  have hz : z ∈ ForwardTube d (n + m) := by
    have hη_abs : η ∈ ForwardConeAbs d (n + m) :=
      (inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n + m) η).mp
        (canonicalForwardConeDirection_mem (d := d) (n + m))
    have hscaled : ε • η ∈ ForwardConeAbs d (n + m) :=
      forwardConeAbs_smul d (n + m) ε hε η hη_abs
    simpa [forwardTube_eq_imPreimage, z, η] using hscaled
  have hgrow := hgrowth z hz
  have hnorm :
      ‖z‖ ≤ ‖y‖ + ‖ε • η‖ := by
    have hz_eq :
        z = (fun k μ => (y k μ : ℂ)) + (fun k μ => ((ε * η k μ : ℝ) : ℂ) * Complex.I) := by
      ext k μ
      simp [z]
    rw [hz_eq]
    have hyC :
        ‖(fun k μ => (y k μ : ℂ))‖ ≤ ‖y‖ := by
      change ‖(fun k : Fin (n + m) => fun μ : Fin (d + 1) => ((y k μ : ℝ) : ℂ))‖ ≤ ‖y‖
      refine (pi_norm_le_iff_of_nonneg
        (x := (fun k : Fin (n + m) => fun μ : Fin (d + 1) => ((y k μ : ℝ) : ℂ)))
        (r := ‖y‖)
        (show 0 ≤ ‖y‖ by exact norm_nonneg _)).2 ?_
      intro k
      have hyCk : ‖fun μ => ((y k μ : ℝ) : ℂ)‖ ≤ ‖y k‖ := by
        change ‖(fun μ : Fin (d + 1) => ((y k μ : ℝ) : ℂ))‖ ≤ ‖y k‖
        refine (pi_norm_le_iff_of_nonneg
          (x := (fun μ : Fin (d + 1) => ((y k μ : ℝ) : ℂ)))
          (r := ‖y k‖)
          (show 0 ≤ ‖y k‖ by exact norm_nonneg _)).2 ?_
        intro μ
        calc
          ‖((y k μ : ℝ) : ℂ)‖ = ‖y k μ‖ := by simp
          _ ≤ ‖y k‖ := norm_le_pi_norm (f := y k) μ
      exact le_trans hyCk (norm_le_pi_norm (f := y) k)
    have hηI :
        ‖fun k μ => ((ε * η k μ : ℝ) : ℂ) * Complex.I‖ ≤ ‖ε • η‖ := by
      change
        ‖(fun k : Fin (n + m) => fun μ : Fin (d + 1) =>
          (((ε * η k μ : ℝ) : ℂ) * Complex.I))‖ ≤ ‖ε • η‖
      refine (pi_norm_le_iff_of_nonneg
        (x := (fun k : Fin (n + m) => fun μ : Fin (d + 1) =>
          (((ε * η k μ : ℝ) : ℂ) * Complex.I)))
        (r := ‖ε • η‖)
        (show 0 ≤ ‖ε • η‖ by exact norm_nonneg _)).2 ?_
      intro k
      have hηIk : ‖fun μ => (((ε * η k μ : ℝ) : ℂ) * Complex.I)‖ ≤ ‖(ε • η) k‖ := by
        change
          ‖(fun μ : Fin (d + 1) =>
            (((ε * η k μ : ℝ) : ℂ) * Complex.I))‖ ≤ ‖(ε • η) k‖
        refine (pi_norm_le_iff_of_nonneg
          (x := (fun μ : Fin (d + 1) =>
            (((ε * η k μ : ℝ) : ℂ) * Complex.I)))
          (r := ‖(ε • η) k‖)
          (show 0 ≤ ‖(ε • η) k‖ by exact norm_nonneg _)).2 ?_
        intro μ
        calc
          ‖(((ε * η k μ : ℝ) : ℂ) * Complex.I)‖ = ‖ε * η k μ‖ := by simp
          _ = ‖(ε • η) k μ‖ := by simp [Pi.smul_apply]
          _ ≤ ‖(ε • η) k‖ := norm_le_pi_norm (f := (ε • η) k) μ
      exact le_trans hηIk (norm_le_pi_norm (f := ε • η) k)
    calc
      ‖(fun k μ => (y k μ : ℂ)) + (fun k μ => ((ε * η k μ : ℝ) : ℂ) * Complex.I)‖
          ≤ ‖fun k μ => (y k μ : ℂ)‖ + ‖fun k μ => ((ε * η k μ : ℝ) : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ ≤ ‖y‖ + ‖ε • η‖ := add_le_add hyC hηI
  have hone :
      1 + ‖z‖ ≤ (1 + ‖ε • η‖) * (1 + ‖y‖) := by
    have htmp : 1 + ‖z‖ ≤ 1 + (‖y‖ + ‖ε • η‖) := by
      linarith [hnorm]
    have hprod : 1 + (‖y‖ + ‖ε • η‖) ≤ (1 + ‖ε • η‖) * (1 + ‖y‖) := by
      nlinarith [norm_nonneg y, norm_nonneg (ε • η)]
    exact le_trans htmp hprod
  have hε_norm_le_one : ‖ε‖ ≤ (1 : ℝ) := by
    rw [Real.norm_of_nonneg (le_of_lt hε)]
    linarith
  have hεη_norm_le : ‖ε • η‖ ≤ ‖η‖ := by
    calc
      ‖ε • η‖ = ‖ε‖ * ‖η‖ := norm_smul ε η
      _ ≤ 1 * ‖η‖ := by
        gcongr
      _ = ‖η‖ := by ring
  have hscale_le :
      (1 + ‖ε • η‖) * (1 + ‖y‖) ≤ (1 + ‖η‖) * (1 + ‖y‖) := by
    apply mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith
  calc
    ‖bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ))‖
        = ‖bvt_F OS lgc (n + m) (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))‖ := by
            simp [z, η]
    _ ≤ C_bd * (1 + ‖z‖) ^ N := hgrow
    _ ≤ C_bd * ((1 + ‖ε • η‖) * (1 + ‖y‖)) ^ N := by
          gcongr
    _ ≤ C_bd * ((1 + ‖η‖) * (1 + ‖y‖)) ^ N := by
          apply mul_le_mul_of_nonneg_left ?_ (le_of_lt hC_bd_pos)
          exact pow_le_pow_left₀ (by positivity) hscale_le N
    _ = (C_bd * (1 + ‖η‖) ^ N) * (1 + ‖y‖) ^ N := by
          rw [mul_pow]
          ring

/-- Fixed-test-function shell-local boundedness on `0 < ε < 1`.

This is the first honest shell-side step strictly above
`section43_fixedTimeShellRaw_uniformPolyGrowth_fixedTime`: for each ambient
Schwartz test, the fixed-time raw shell CLMs stay pointwise bounded as the
imaginary shell height runs through `(0,1)`. The remaining upgrade to one
common finite Schwartz seminorm is then a Banach-Steinhaus step, not another
shell-integral estimate. -/
private theorem section43_fixedTimeShellRawCLM_pointwiseBounded_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m) (t : ℝ) :
    ∀ φ : SchwartzNPoint d (n + m),
      ∃ Cφ : ℝ, 0 ≤ Cφ ∧
        ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ hε_lt : ε < 1,
          ‖section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε φ‖ ≤ Cφ := by
  obtain ⟨C_shell, N, hC_shell_pos, hcoeff_bound⟩ :=
    section43_fixedTimeShellRaw_uniformPolyGrowth_fixedTime
      (d := d) OS lgc hm t
  intro φ
  set D_fin : ℕ := Module.finrank ℝ (NPointDomain d (n + m))
  set M : ℕ := N + D_fin + 1
  set I_D : ℝ :=
    ∫ y : NPointDomain d (n + m), (1 + ‖y‖) ^ (-(↑(D_fin + 1) : ℝ))
  set sem : ℝ :=
    (Finset.Iic (M, 0)).sup
      (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ) φ
  let Cφ : ℝ := C_shell * 2 ^ M * sem * I_D
  refine ⟨Cφ, ?_, ?_⟩
  · dsimp [Cφ, sem, I_D]
    apply mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC_shell_pos) (by positivity))
      (apply_nonneg _ _))
    apply MeasureTheory.integral_nonneg
    intro y
    apply Real.rpow_nonneg
    linarith [norm_nonneg y]
  · intro ε hε hε_lt
    have hsem_bound :
        ∀ y : NPointDomain d (n + m),
          (1 + ‖y‖) ^ M * ‖φ y‖ ≤ 2 ^ M * sem := by
      intro y
      have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, 0))
        (le_refl M) (le_refl 0) φ y
      rwa [norm_iteratedFDeriv_zero] at h
    have hcoeff_cont :
        Continuous
          (fun y : NPointDomain d (n + m) =>
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ))) := by
      rw [continuous_iff_continuousAt]
      intro y
      let shellMap : NPointDomain d (n + m) → Fin (n + m) → Fin (d + 1) → ℂ :=
        fun y =>
          xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)
      have hshell_mem : shellMap y ∈ ForwardTube d (n + m) := by
        simpa [shellMap, forwardTube_eq_imPreimage] using
          canonicalXiShift_mem_forwardTube (d := d) hm hε y
      have houter_cont : ContinuousAt (bvt_F OS lgc (n + m)) (shellMap y) := by
        let hft_open :
            IsOpen (ForwardTube d (n + m)) := by
          simpa [BHW_forwardTube_eq (d := d) (n := n + m)] using
            (BHW.isOpen_forwardTube (d := d) (n := n + m))
        have houter_diff :
            DifferentiableAt ℂ (bvt_F OS lgc (n + m)) (shellMap y) :=
          (bvt_F_holomorphic (d := d) OS lgc (n + m)).differentiableAt
            (hft_open.mem_nhds hshell_mem)
        exact houter_diff.continuousAt
      have hinner_cont : ContinuousAt shellMap y :=
        (contDiff_canonicalXiShift (d := d) hm t ε).continuous.continuousAt
      simpa [shellMap] using houter_cont.comp hinner_cont
    have hpointwise :
        ∀ᵐ y : NPointDomain d (n + m) ∂MeasureTheory.volume,
          ‖bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
            φ y‖ ≤
              C_shell * 2 ^ M * sem *
                (1 + ‖y‖) ^ (-(↑(D_fin + 1) : ℝ)) := by
      filter_upwards with y
      have h1y_pos : (0 : ℝ) < 1 + ‖y‖ := by
        linarith [norm_nonneg y]
      have h1yD1_pos : (0 : ℝ) < (1 + ‖y‖) ^ (D_fin + 1) := pow_pos h1y_pos _
      rw [Real.rpow_neg (le_of_lt h1y_pos), Real.rpow_natCast, norm_mul]
      have step1 :
          ‖bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ))‖ * ‖φ y‖ ≤
            C_shell * (1 + ‖y‖) ^ N * ‖φ y‖ :=
        mul_le_mul_of_nonneg_right (hcoeff_bound ε hε hε_lt y) (norm_nonneg _)
      have step2 :
          (1 + ‖y‖) ^ N * ‖φ y‖ ≤
            2 ^ M * sem * ((1 + ‖y‖) ^ (D_fin + 1))⁻¹ := by
        rw [le_mul_inv_iff₀ h1yD1_pos]
        have hM : N + (D_fin + 1) = M := by
          omega
        calc
          (1 + ‖y‖) ^ N * ‖φ y‖ * (1 + ‖y‖) ^ (D_fin + 1)
              = (1 + ‖y‖) ^ (N + (D_fin + 1)) * ‖φ y‖ := by
                  rw [pow_add]
                  ring
          _ = (1 + ‖y‖) ^ M * ‖φ y‖ := by rw [hM]
          _ ≤ 2 ^ M * sem := hsem_bound y
      calc
        ‖bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ))‖ * ‖φ y‖
            ≤ C_shell * (1 + ‖y‖) ^ N * ‖φ y‖ := step1
        _ = C_shell * ((1 + ‖y‖) ^ N * ‖φ y‖) := by ring
        _ ≤ C_shell * (2 ^ M * sem * ((1 + ‖y‖) ^ (D_fin + 1))⁻¹) :=
          mul_le_mul_of_nonneg_left step2 (le_of_lt hC_shell_pos)
        _ = C_shell * 2 ^ M * sem * ((1 + ‖y‖) ^ (D_fin + 1))⁻¹ := by ring
    have hInt_kernel :
        MeasureTheory.Integrable
          (fun y : NPointDomain d (n + m) =>
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
            φ y)
          MeasureTheory.volume := by
      refine ((integrable_one_add_norm (show (D_fin : ℝ) < ↑(D_fin + 1) by
          push_cast
          linarith)).const_mul (C_shell * 2 ^ M * sem)).mono' ?_ ?_
      · exact hcoeff_cont.aestronglyMeasurable.mul φ.continuous.aestronglyMeasurable
      · exact hpointwise
    calc
      ‖section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε φ‖
          = ‖∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    ↑(y k μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)) *
                φ y‖ := by
              simp [section43_fixedTimeShellRawCLM]
      _ ≤ ∫ y : NPointDomain d (n + m),
            ‖bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    ↑(y k μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)) *
              φ y‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ y : NPointDomain d (n + m),
            C_shell * 2 ^ M * sem *
              (1 + ‖y‖) ^ (-(↑(D_fin + 1) : ℝ)) :=
        MeasureTheory.integral_mono_ae
          hInt_kernel.norm
          ((integrable_one_add_norm (show (D_fin : ℝ) < ↑(D_fin + 1) by
              push_cast
              linarith)).const_mul (C_shell * 2 ^ M * sem))
          hpointwise
      _ = C_shell * 2 ^ M * sem * I_D := by
            rw [MeasureTheory.integral_const_mul]
      _ = Cφ := by
            simp [Cφ, I_D]

/-- First honest fixed-time shell boundary-distribution step beneath
`hlimit_os`: for each fixed `t > 0`, the positive-height raw shell family
admits some limit in the ambient Schwartz dual.

This all-directions version matches the hypothesis surface expected later by
the SCV Fourier-support and Fourier-Laplace representation seams.

It still only lands the existence half of the shell boundary-distribution
package. It is not yet enough for the outside-region branch in `hlimit_os`,
because the later quotient-kernel theorem for the resulting limit functional is
still missing. -/
private theorem section43_fixedTimeShellRawCLM_boundaryValueData_allDirections_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ) :
    ∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      (∀ h : SchwartzNPoint d (n + m),
        Filter.Tendsto
          (fun ε : ℝ =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
            else
              0)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (T_t h))) ∧
      (let F_analytic :
          (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ :=
          fun z =>
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))
       ∀ (η : Fin (n + m) → Fin (d + 1) → ℝ), η ∈ ForwardConeAbs d (n + m) →
         ∀ h : SchwartzNPoint d (n + m),
          Filter.Tendsto
            (fun ε : ℝ =>
              ∫ x : Fin (n + m) → Fin (d + 1) → ℝ,
                F_analytic (fun k μ =>
                  ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * h x)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (T_t h))) := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let F_analytic :
      (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ :=
    fun z => bvt_F OS lgc (n + m) (xiShift j 0 z (t : ℂ))
  have hF_hol :
      DifferentiableOn ℂ F_analytic (TubeDomainSetPi (ForwardConeAbs d (n + m))) := by
    intro z hz
    have hz_shift_mem :
        xiShift j 0 z (t : ℂ) ∈ ForwardTube d (n + m) := by
      rw [forwardTube_eq_imPreimage]
      change (fun k μ => (z k μ).im) ∈ ForwardConeAbs d (n + m) at hz
      have him :
          (fun k μ => (xiShift j 0 z (t : ℂ) k μ).im) =
            fun k μ => (z k μ).im := by
        ext k μ
        by_cases hshift : j.val ≤ k.val ∧ μ = (0 : Fin (d + 1))
        · have hshift' : j ≤ k ∧ μ = (0 : Fin (d + 1)) := by simpa using hshift
          simp [xiShift, hshift']
        · have hshift' : ¬ (j ≤ k ∧ μ = (0 : Fin (d + 1))) := by simpa using hshift
          simp [xiShift, hshift']
      simpa [him] using hz
    have hft_open : IsOpen (ForwardTube d (n + m)) := by
      simpa [BHW_forwardTube_eq (d := d) (n := n + m)] using
        (BHW.isOpen_forwardTube (d := d) (n := n + m))
    have houter :
        DifferentiableAt ℂ (bvt_F OS lgc (n + m)) (xiShift j 0 z (t : ℂ)) :=
      (bvt_F_holomorphic (d := d) OS lgc (n + m)).differentiableAt
        (hft_open.mem_nhds hz_shift_mem)
    let shift : Fin (n + m) → Fin (d + 1) → ℂ :=
      fun k μ =>
        if j.val ≤ k.val ∧ μ = (0 : Fin (d + 1)) then
          (t : ℂ)
        else
          0
    have hinner :
        DifferentiableAt ℂ
          (fun z : Fin (n + m) → Fin (d + 1) → ℂ => xiShift j 0 z (t : ℂ)) z := by
      convert (differentiableAt_id.add_const shift : DifferentiableAt ℂ
        (fun z : Fin (n + m) → Fin (d + 1) → ℂ => z + shift) z) using 1
      ext w k μ
      by_cases hshift : j.val ≤ k.val ∧ μ = (0 : Fin (d + 1))
      · have hshift' : j ≤ k ∧ μ = (0 : Fin (d + 1)) := by simpa using hshift
        simp [shift, xiShift, hshift']
      · have hshift' : ¬ (j ≤ k ∧ μ = (0 : Fin (d + 1))) := by simpa using hshift
        simp [shift, xiShift, hshift']
    exact (houter.comp z hinner).differentiableWithinAt
  let growth :=
    section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth
      (d := d) (n := n) OS lgc hm t
  let C_bd : ℝ := Classical.choose growth
  let N : ℕ := Classical.choose (Classical.choose_spec growth)
  have hC_bd_pos : 0 < C_bd := by
    exact (Classical.choose_spec (Classical.choose_spec growth)).1
  have hF_growth :
      ∀ (z : Fin (n + m) → Fin (d + 1) → ℂ), z ∈ ForwardTube d (n + m) →
        ‖bvt_F OS lgc (n + m) (xiShift j 0 z (t : ℂ))‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
    exact (Classical.choose_spec (Classical.choose_spec growth)).2
  obtain ⟨T_t, hT_t⟩ :=
    SCV.tube_boundaryValueData_of_polyGrowth
      (C := ForwardConeAbs d (n + m))
      (hC_open := forwardConeAbs_isOpen d (n + m))
      (hC_conv := forwardConeAbs_convex d (n + m))
      (hC_cone := by
        intro y hy s hs
        exact forwardConeAbs_smul d (n + m) s hs y hy)
      (hC_salient := forwardConeAbs_salient d (n + m))
      (F := F_analytic)
      (hF_hol := by
        simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using hF_hol)
      C_bd N hC_bd_pos
      (hF_growth := by
        intro z hz
        exact hF_growth z (by simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using hz))
  refine ⟨T_t, ?_, ?_⟩
  · intro h
    have hη :
        canonicalForwardConeDirection (d := d) (n + m) ∈ ForwardConeAbs d (n + m) :=
      (inForwardCone_iff_mem_forwardConeAbs
        (d := d) (n := n + m)
        (canonicalForwardConeDirection (d := d) (n + m))).mp
        (canonicalForwardConeDirection_mem (d := d) (n + m))
    have hmain :=
      hT_t h (canonicalForwardConeDirection (d := d) (n + m)) hη
    have hEq :
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun ε : ℝ =>
          ∫ x : Fin (n + m) → Fin (d + 1) → ℝ,
            F_analytic (fun k μ =>
              ↑(x k μ) +
                (ε : ℂ) * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I) *
              h x) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hpos : 0 < ε := hε
      simp [F_analytic, section43_fixedTimeShellRawCLM, j, hpos]
    exact Filter.Tendsto.congr' hEq.symm hmain
  · dsimp
    intro η hη h
    simpa [F_analytic] using (hT_t h η hη)

/-- Canonical-ray corollary of the fixed-time all-directions shell
boundary-distribution package. -/
private theorem section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ) :
    ∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      ∀ h : SchwartzNPoint d (n + m),
        Filter.Tendsto
          (fun ε : ℝ =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
            else
              0)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (T_t h)) := by
  obtain ⟨T_t, hcanon, _hall⟩ :=
    section43_fixedTimeShellRawCLM_boundaryValueData_allDirections_fixedTime
      (d := d) OS lgc hm t
  exact ⟨T_t, hcanon⟩

/-- Fixed-time spectral-support supplier obtained by specializing
`SCV.bv_implies_fourier_support` to the shifted continuation
`F_analytic z = bvt_F OS lgc (n + m) (xiShift ... z (t : ℂ))` and the
boundary functional `T_t` produced on the shell seam. -/
private theorem section43_fixedTimeShellRawCLM_bv_implies_fourier_support_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ) :
    ∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      (∀ h : SchwartzNPoint d (n + m),
        Filter.Tendsto
          (fun ε : ℝ =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
            else
              0)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (T_t h))) ∧
      ∃ Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ,
        HasFourierSupportInDualCone
          ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))
          Tflat ∧
        ∀ φ : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
          T_t.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (flattenCLEquivReal (n + m) (d + 1))) φ =
            Tflat (physicsFourierFlatCLM φ) := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let F_analytic :
      (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ :=
    fun z => bvt_F OS lgc (n + m) (xiShift j 0 z (t : ℂ))
  have hF_holo :
      DifferentiableOn ℂ F_analytic (TubeDomainSetPi (ForwardConeAbs d (n + m))) := by
    intro z hz
    have hz_shift_mem :
        xiShift j 0 z (t : ℂ) ∈ ForwardTube d (n + m) := by
      rw [forwardTube_eq_imPreimage]
      change (fun k μ => (z k μ).im) ∈ ForwardConeAbs d (n + m) at hz
      have him :
          (fun k μ => (xiShift j 0 z (t : ℂ) k μ).im) =
            fun k μ => (z k μ).im := by
        ext k μ
        by_cases hshift : j.val ≤ k.val ∧ μ = (0 : Fin (d + 1))
        · have hshift' : j ≤ k ∧ μ = (0 : Fin (d + 1)) := by simpa using hshift
          simp [xiShift, hshift']
        · have hshift' : ¬ (j ≤ k ∧ μ = (0 : Fin (d + 1))) := by simpa using hshift
          simp [xiShift, hshift']
      simpa [him] using hz
    have hft_open : IsOpen (ForwardTube d (n + m)) := by
      simpa [BHW_forwardTube_eq (d := d) (n := n + m)] using
        (BHW.isOpen_forwardTube (d := d) (n := n + m))
    have houter :
        DifferentiableAt ℂ (bvt_F OS lgc (n + m)) (xiShift j 0 z (t : ℂ)) :=
      (bvt_F_holomorphic (d := d) OS lgc (n + m)).differentiableAt
        (hft_open.mem_nhds hz_shift_mem)
    let shift : Fin (n + m) → Fin (d + 1) → ℂ :=
      fun k μ =>
        if j.val ≤ k.val ∧ μ = (0 : Fin (d + 1)) then
          (t : ℂ)
        else
          0
    have hinner :
        DifferentiableAt ℂ
          (fun z : Fin (n + m) → Fin (d + 1) → ℂ => xiShift j 0 z (t : ℂ)) z := by
      convert (differentiableAt_id.add_const shift : DifferentiableAt ℂ
        (fun z : Fin (n + m) → Fin (d + 1) → ℂ => z + shift) z) using 1
      ext w k μ
      by_cases hshift : j.val ≤ k.val ∧ μ = (0 : Fin (d + 1))
      · have hshift' : j ≤ k ∧ μ = (0 : Fin (d + 1)) := by simpa using hshift
        simp [shift, xiShift, hshift']
      · have hshift' : ¬ (j ≤ k ∧ μ = (0 : Fin (d + 1))) := by simpa using hshift
        simp [shift, xiShift, hshift']
    exact (houter.comp z hinner).differentiableWithinAt
  let growth :=
    section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth
      (d := d) (n := n) OS lgc hm t
  let C_bd : ℝ := Classical.choose growth
  let N : ℕ := Classical.choose (Classical.choose_spec growth)
  have hC_bd_pos : 0 < C_bd := by
    exact (Classical.choose_spec (Classical.choose_spec growth)).1
  have hF_growth :
      ∀ (z : Fin (n + m) → Fin (d + 1) → ℂ), z ∈ ForwardTube d (n + m) →
        ‖bvt_F OS lgc (n + m) (xiShift j 0 z (t : ℂ))‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
    exact (Classical.choose_spec (Classical.choose_spec growth)).2
  have hF_growth_tube :
      ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ (z : Fin (n + m) → Fin (d + 1) → ℂ), z ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) →
          ‖F_analytic z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
    refine ⟨C_bd, N, hC_bd_pos, ?_⟩
    intro z hz
    exact hF_growth z (by simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using hz)
  obtain ⟨T_t, hcanon, hall⟩ :=
    section43_fixedTimeShellRawCLM_boundaryValueData_allDirections_fixedTime
      (d := d) OS lgc hm t
  have hTflat_data :=
    bv_implies_fourier_support
      (C := ForwardConeAbs d (n + m))
      (hC_open := forwardConeAbs_isOpen d (n + m))
      (hC_conv := forwardConeAbs_convex d (n + m))
      (hC_cone := by
        intro y hy s hs
        exact forwardConeAbs_smul d (n + m) s hs y hy)
      (hC_salient := forwardConeAbs_salient d (n + m))
      (F := F_analytic)
      (hF_holo := by
        simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using hF_holo)
      (hF_growth := hF_growth_tube)
      (W := T_t)
      (hF_bv := hall)
  dsimp only at hTflat_data
  obtain ⟨Tflat, hTflat_support, hTflat_eq⟩ := hTflat_data
  exact ⟨T_t, hcanon, Tflat, hTflat_support, hTflat_eq⟩

/-- Fixed-time Fourier-Laplace representation on the shifted tube, obtained by
combining the fixed-time all-directions boundary-value package with the SCV
supplier/comparison axioms. This is the first consumer seam above
`section43_fixedTimeShellRawCLM_boundaryValueData_allDirections_fixedTime`. -/
private theorem section43_fixedTimeShellRawCLM_fl_representation_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ) :
    ∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      (∀ h : SchwartzNPoint d (n + m),
        Filter.Tendsto
          (fun ε : ℝ =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
            else
              0)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (T_t h))) ∧
      ∃ Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ,
        HasFourierSupportInDualCone (ForwardConeFlat d (n + m)) Tflat ∧
        (∀ φ : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
          T_t.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (flattenCLEquivReal (n + m) (d + 1))) φ =
            Tflat (physicsFourierFlatCLM φ)) ∧
        ∃ hCflat_cone : IsCone (ForwardConeFlat d (n + m)),
          ∃ hCflat_salient : IsSalientCone (ForwardConeFlat d (n + m)),
            let F_analytic :
                (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ :=
                fun z =>
                  bvt_F OS lgc (n + m)
                    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))
            ∀ z, z ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) →
              F_analytic z =
                fourierLaplaceExtMultiDim
                  (ForwardConeFlat d (n + m))
                  (forwardConeFlat_isOpen d (n + m))
                  (forwardConeFlat_convex d (n + m))
                  hCflat_cone hCflat_salient Tflat
                  ((flattenCLEquiv (n + m) (d + 1)) z) := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let F_analytic :
      (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ :=
    fun z => bvt_F OS lgc (n + m) (xiShift j 0 z (t : ℂ))
  have hF_holo :
      DifferentiableOn ℂ F_analytic (TubeDomainSetPi (ForwardConeAbs d (n + m))) := by
    intro z hz
    have hz_shift_mem :
        xiShift j 0 z (t : ℂ) ∈ ForwardTube d (n + m) := by
      rw [forwardTube_eq_imPreimage]
      change (fun k μ => (z k μ).im) ∈ ForwardConeAbs d (n + m) at hz
      have him :
          (fun k μ => (xiShift j 0 z (t : ℂ) k μ).im) =
            fun k μ => (z k μ).im := by
        ext k μ
        by_cases hshift : j.val ≤ k.val ∧ μ = (0 : Fin (d + 1))
        · have hshift' : j ≤ k ∧ μ = (0 : Fin (d + 1)) := by simpa using hshift
          simp [xiShift, hshift']
        · have hshift' : ¬ (j ≤ k ∧ μ = (0 : Fin (d + 1))) := by simpa using hshift
          simp [xiShift, hshift']
      simpa [him] using hz
    have hft_open : IsOpen (ForwardTube d (n + m)) := by
      simpa [BHW_forwardTube_eq (d := d) (n := n + m)] using
        (BHW.isOpen_forwardTube (d := d) (n := n + m))
    have houter :
        DifferentiableAt ℂ (bvt_F OS lgc (n + m)) (xiShift j 0 z (t : ℂ)) :=
      (bvt_F_holomorphic (d := d) OS lgc (n + m)).differentiableAt
        (hft_open.mem_nhds hz_shift_mem)
    let shift : Fin (n + m) → Fin (d + 1) → ℂ :=
      fun k μ =>
        if j.val ≤ k.val ∧ μ = (0 : Fin (d + 1)) then
          (t : ℂ)
        else
          0
    have hinner :
        DifferentiableAt ℂ
          (fun z : Fin (n + m) → Fin (d + 1) → ℂ => xiShift j 0 z (t : ℂ)) z := by
      convert (differentiableAt_id.add_const shift : DifferentiableAt ℂ
        (fun z : Fin (n + m) → Fin (d + 1) → ℂ => z + shift) z) using 1
      ext w k μ
      by_cases hshift : j.val ≤ k.val ∧ μ = (0 : Fin (d + 1))
      · have hshift' : j ≤ k ∧ μ = (0 : Fin (d + 1)) := by simpa using hshift
        simp [shift, xiShift, hshift']
      · have hshift' : ¬ (j ≤ k ∧ μ = (0 : Fin (d + 1))) := by simpa using hshift
        simp [shift, xiShift, hshift']
    exact (houter.comp z hinner).differentiableWithinAt
  let growth :=
    section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth
      (d := d) (n := n) OS lgc hm t
  let C_bd : ℝ := Classical.choose growth
  let N : ℕ := Classical.choose (Classical.choose_spec growth)
  have hC_bd_pos : 0 < C_bd := by
    exact (Classical.choose_spec (Classical.choose_spec growth)).1
  have hF_growth :
      ∀ (z : Fin (n + m) → Fin (d + 1) → ℂ), z ∈ ForwardTube d (n + m) →
        ‖bvt_F OS lgc (n + m) (xiShift j 0 z (t : ℂ))‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
    exact (Classical.choose_spec (Classical.choose_spec growth)).2
  have hF_growth_tube :
      ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ (z : Fin (n + m) → Fin (d + 1) → ℂ), z ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) →
          ‖F_analytic z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
    refine ⟨C_bd, N, hC_bd_pos, ?_⟩
    intro z hz
    exact hF_growth z (by simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using hz)
  obtain ⟨T_t, hcanon, hall⟩ :=
    section43_fixedTimeShellRawCLM_boundaryValueData_allDirections_fixedTime
      (d := d) OS lgc hm t
  have hTflat_data :=
    bv_implies_fourier_support
      (C := ForwardConeAbs d (n + m))
      (hC_open := forwardConeAbs_isOpen d (n + m))
      (hC_conv := forwardConeAbs_convex d (n + m))
      (hC_cone := by
        intro y hy s hs
        exact forwardConeAbs_smul d (n + m) s hs y hy)
      (hC_salient := forwardConeAbs_salient d (n + m))
      (F := F_analytic)
      (hF_holo := by
        simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using hF_holo)
      (hF_growth := hF_growth_tube)
      (W := T_t)
      (hF_bv := hall)
  dsimp only at hTflat_data
  obtain ⟨Tflat, hTflat_support_raw, hTflat_eq⟩ := hTflat_data
  have hTflat_support :
      HasFourierSupportInDualCone (ForwardConeFlat d (n + m)) Tflat := by
    simpa [ForwardConeFlat] using hTflat_support_raw
  have hCflat_cone : IsCone (ForwardConeFlat d (n + m)) := by
    intro y hy s hs
    exact forwardConeFlat_isCone d (n + m) s hs y hy
  have hCflat_salient : IsSalientCone (ForwardConeFlat d (n + m)) := by
    let eR := flattenCLEquivReal (n + m) (d + 1)
    change IsSalientCone (eR '' ForwardConeAbs d (n + m))
    intro y hy hy_neg
    rw [show closure (eR '' ForwardConeAbs d (n + m)) = eR '' closure (ForwardConeAbs d (n + m)) from
      (eR.toHomeomorph.image_closure (ForwardConeAbs d (n + m))).symm] at hy hy_neg
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨y'', hy'', hyw⟩ := hy_neg
    have h_neg : y'' = -y' := eR.injective (by rw [hyw, map_neg])
    subst h_neg
    exact show eR y' = 0 from by
      rw [forwardConeAbs_salient d (n + m) y' hy' hy'', map_zero]
  have hFL_repr :
      ∀ z, z ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) →
        F_analytic z =
          fourierLaplaceExtMultiDim
            (ForwardConeFlat d (n + m))
            (forwardConeFlat_isOpen d (n + m))
            (forwardConeFlat_convex d (n + m))
            hCflat_cone hCflat_salient Tflat
            ((flattenCLEquiv (n + m) (d + 1)) z) := by
    simpa [F_analytic, ForwardConeFlat] using
      (fl_representation_from_bv
        (C := ForwardConeAbs d (n + m))
        (hC_open := forwardConeAbs_isOpen d (n + m))
        (hC_conv := forwardConeAbs_convex d (n + m))
        (hC_cone := by
          intro y hy s hs
          exact forwardConeAbs_smul d (n + m) s hs y hy)
        (hC_salient := forwardConeAbs_salient d (n + m))
        (F := F_analytic)
        (hF_holo := by
          simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using hF_holo)
        (W := T_t)
        (hF_bv := hall)
        (Cflat := ForwardConeFlat d (n + m))
        (hCflat_eq := rfl)
        (hCflat_open := forwardConeFlat_isOpen d (n + m))
        (hCflat_conv := forwardConeFlat_convex d (n + m))
        (hCflat_cone := hCflat_cone)
        (hCflat_salient := hCflat_salient)
        (Tflat := Tflat)
        (hTflat_support := by simpa [ForwardConeFlat] using hTflat_support_raw)
        (hTflat_eq := hTflat_eq))
  exact
    ⟨T_t, hcanon, Tflat, hTflat_support, hTflat_eq, hCflat_cone, hCflat_salient, hFL_repr⟩

/-- Fixed-time tempered Fourier-Laplace package for the flattened shifted
continuation. This is the exact lower supplier already source-ready beneath the
missing local-trace continuity bridge: it packages the landed all-directions
distributional boundary-value data and global tube growth for `G_t`, but makes
no pointwise boundary-continuity claim. -/
private def section43_fixedTimeShellRaw_temperedRepr_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ) :
    SCV.HasFourierLaplaceReprTempered
      (ForwardConeFlat d (n + m))
      (fun zflat =>
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))) := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let F_analytic :
      (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ :=
    fun z => bvt_F OS lgc (n + m) (xiShift j 0 z (t : ℂ))
  have hF_holo :
      DifferentiableOn ℂ F_analytic (TubeDomainSetPi (ForwardConeAbs d (n + m))) := by
    intro z hz
    have hz_shift_mem :
        xiShift j 0 z (t : ℂ) ∈ ForwardTube d (n + m) := by
      rw [forwardTube_eq_imPreimage]
      change (fun k μ => (z k μ).im) ∈ ForwardConeAbs d (n + m) at hz
      have him :
          (fun k μ => (xiShift j 0 z (t : ℂ) k μ).im) =
            fun k μ => (z k μ).im := by
        ext k μ
        by_cases hshift : j.val ≤ k.val ∧ μ = (0 : Fin (d + 1))
        · have hshift' : j ≤ k ∧ μ = (0 : Fin (d + 1)) := by simpa using hshift
          simp [xiShift, hshift']
        · have hshift' : ¬ (j ≤ k ∧ μ = (0 : Fin (d + 1))) := by simpa using hshift
          simp [xiShift, hshift']
      simpa [him] using hz
    have hft_open : IsOpen (ForwardTube d (n + m)) := by
      simpa [BHW_forwardTube_eq (d := d) (n := n + m)] using
        (BHW.isOpen_forwardTube (d := d) (n := n + m))
    have houter :
        DifferentiableAt ℂ (bvt_F OS lgc (n + m)) (xiShift j 0 z (t : ℂ)) :=
      (bvt_F_holomorphic (d := d) OS lgc (n + m)).differentiableAt
        (hft_open.mem_nhds hz_shift_mem)
    let shift : Fin (n + m) → Fin (d + 1) → ℂ :=
      fun k μ =>
        if j.val ≤ k.val ∧ μ = (0 : Fin (d + 1)) then
          (t : ℂ)
        else
          0
    have hinner :
        DifferentiableAt ℂ
          (fun z : Fin (n + m) → Fin (d + 1) → ℂ => xiShift j 0 z (t : ℂ)) z := by
      convert (differentiableAt_id.add_const shift : DifferentiableAt ℂ
        (fun z : Fin (n + m) → Fin (d + 1) → ℂ => z + shift) z) using 1
      ext w k μ
      by_cases hshift : j.val ≤ k.val ∧ μ = (0 : Fin (d + 1))
      · have hshift' : j ≤ k ∧ μ = (0 : Fin (d + 1)) := by simpa using hshift
        simp [shift, xiShift, hshift']
      · have hshift' : ¬ (j ≤ k ∧ μ = (0 : Fin (d + 1))) := by simpa using hshift
        simp [shift, xiShift, hshift']
    exact (houter.comp z hinner).differentiableWithinAt
  let growth :=
    section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth
      (d := d) (n := n) OS lgc hm t
  let C_bd : ℝ := Classical.choose growth
  let N : ℕ := Classical.choose (Classical.choose_spec growth)
  have hC_bd_pos : 0 < C_bd := by
    exact (Classical.choose_spec (Classical.choose_spec growth)).1
  have hF_growth :
      ∀ (z : Fin (n + m) → Fin (d + 1) → ℂ), z ∈ ForwardTube d (n + m) →
        ‖bvt_F OS lgc (n + m) (xiShift j 0 z (t : ℂ))‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
    exact (Classical.choose_spec (Classical.choose_spec growth)).2
  have hF_growth_tube :
      ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ (z : Fin (n + m) → Fin (d + 1) → ℂ), z ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) →
          ‖F_analytic z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
    refine ⟨C_bd, N, hC_bd_pos, ?_⟩
    intro z hz
    exact hF_growth z (by simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using hz)
  let boundaryData :=
    section43_fixedTimeShellRawCLM_boundaryValueData_allDirections_fixedTime
      (d := d) (n := n) OS lgc hm t
  let T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ := Classical.choose boundaryData
  have hall :
      ∀ (η : Fin (n + m) → Fin (d + 1) → ℝ), η ∈ ForwardConeAbs d (n + m) →
        ∀ (h : SchwartzNPoint d (n + m)),
          Filter.Tendsto
            (fun ε : ℝ =>
              ∫ x : Fin (n + m) → Fin (d + 1) → ℝ,
                F_analytic (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * Complex.I) * h x)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (T_t h)) := by
    exact (Classical.choose_spec boundaryData).2
  let hTempered :
      SCV.HasFourierLaplaceReprTempered (ForwardConeFlat d (n + m))
        (F_analytic ∘ (flattenCLEquiv (n + m) (d + 1)).symm) :=
    vladimirov_tillmann_hasFourierLaplaceReprTempered
      (ForwardConeAbs d (n + m))
      (forwardConeAbs_isOpen d (n + m))
      (forwardConeAbs_convex d (n + m))
      (fun y hy s hs => forwardConeAbs_smul d (n + m) s hs y hy)
      (forwardConeAbs_salient d (n + m))
      F_analytic hF_holo hF_growth_tube T_t hall
  simpa [F_analytic] using hTempered

private theorem section43_fixedTimeShellRawCLM_uniformSeminormBound_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m) (t : ℝ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C_sem : ℝ, 0 ≤ C_sem ∧
      ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ hε_lt : ε < 1,
      ∀ φ : SchwartzNPoint d (n + m),
        ‖section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε φ‖ ≤
          C_sem *
            (s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)) φ := by
  let T : {ε : ℝ // 0 < ε ∧ ε < 1} → SchwartzNPoint d (n + m) →L[ℝ] ℂ :=
    fun ε =>
      { toLinearMap :=
          { toFun := fun φ =>
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε.1 ε.2.1 φ
            map_add' := by
              intro φ ψ
              simp
            map_smul' := by
              intro c φ
              simpa [smul_eq_mul] using
                (section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε.1 ε.2.1).map_smul
                  (c : ℂ) φ }
        cont := (section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε.1 ε.2.1).continuous }
  have hT :
      ∀ φ : SchwartzNPoint d (n + m),
        ∃ Cφ : ℝ, ∀ ε : {ε : ℝ // 0 < ε ∧ ε < 1}, ‖T ε φ‖ ≤ Cφ := by
    intro φ
    obtain ⟨Cφ, _hCφ_nonneg, hCφ⟩ :=
      section43_fixedTimeShellRawCLM_pointwiseBounded_fixedTime
        (d := d) OS lgc hm t φ
    refine ⟨Cφ, ?_⟩
    intro ε
    simpa [T] using hCφ ε.1 ε.2.1 ε.2.2
  obtain ⟨s, C, hCne, hbound⟩ := SchwartzMap.tempered_uniform_schwartz_bound hT
  have hsup_eq :
      ∀ I : Finset (ℕ × ℕ), ∀ f : SchwartzMap (NPointDomain d (n + m)) ℂ,
        (I.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)) f =
          (I.sup (schwartzSeminormFamily ℝ (NPointDomain d (n + m)) ℂ)) f := by
    intro I f
    induction I using Finset.cons_induction with
    | empty =>
        simp [Finset.sup_empty]
    | @cons a I ha hI =>
        simp [hI, schwartzSeminormFamily, SchwartzMap.seminorm_apply]
  refine ⟨s, C, NNReal.coe_nonneg C, ?_⟩
  intro ε hε hε_lt φ
  have hmain := hbound ⟨ε, hε, hε_lt⟩ φ
  simpa [T, hsup_eq s, smul_eq_mul] using hmain

private theorem section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) :
    ∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      Filter.Tendsto
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε
          else
            0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds T_t) := by
  obtain ⟨T_t, hT_t⟩ :=
    section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime
      (d := d) OS lgc hm t
  obtain ⟨s, C_sem, hC_sem, hbound⟩ :=
    section43_fixedTimeShellRawCLM_uniformSeminormBound_fixedTime
      (d := d) OS lgc hm t
  have hsup_eq :
      ∀ I : Finset (ℕ × ℕ), ∀ f : SchwartzNPoint d (n + m),
        (I.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)) f =
          (I.sup (schwartzSeminormFamily ℝ (NPointDomain d (n + m)) ℂ)) f := by
    intro I f
    induction I using Finset.cons_induction with
    | empty =>
        simp [Finset.sup_empty]
    | @cons a I ha hI =>
        simp [hI, schwartzSeminormFamily, SchwartzMap.seminorm_apply]
  haveI := IsScalarTower.restrictScalars ℝ ℂ (SchwartzNPoint d (n + m))
  let pR : Seminorm ℝ (SchwartzNPoint d (n + m)) :=
    s.sup (schwartzSeminormFamily ℝ (NPointDomain d (n + m)) ℂ)
  let T0R : SchwartzNPoint d (n + m) →L[ℝ] ℂ :=
    { toLinearMap :=
        { toFun := fun φ => T_t φ
          map_add' := by
            intro φ ψ
            simp
          map_smul' := by
            intro c φ
            simpa [smul_eq_mul] using T_t.map_smul (c : ℂ) φ }
      cont := T_t.continuous }
  let familyR : ℝ → SchwartzNPoint d (n + m) →L[ℝ] ℂ := fun ε =>
    if hε : 0 < ε then
      { toLinearMap :=
          { toFun := fun φ =>
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε φ
            map_add' := by
              intro φ ψ
              simp
            map_smul' := by
              intro c φ
              simpa [smul_eq_mul] using
                (section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε).map_smul
                  (c : ℂ) φ }
        cont := (section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε).continuous }
    else
      0
  have hpointwiseR :
      ∀ φ : SchwartzNPoint d (n + m),
        Filter.Tendsto (fun ε : ℝ => familyR ε φ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (T0R φ)) := by
    intro φ
    have hEq :
        (fun ε : ℝ => familyR ε φ) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
          (fun ε : ℝ =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε φ
            else
              0) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hval :
          familyR ε φ =
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε φ := by
        simp [familyR, show 0 < ε from hε]
      simpa [show 0 < ε from hε] using hval
    exact Filter.Tendsto.congr' hEq.symm (by simpa [T0R] using hT_t φ)
  have hlt1 :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < 1 := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with
      ε hε hlt
    exact hlt
  have hfamily_bound :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ φ : SchwartzNPoint d (n + m), ‖familyR ε φ‖ ≤ C_sem * pR φ := by
    filter_upwards [self_mem_nhdsWithin, hlt1] with ε hε hε_lt φ
    have hmain := hbound ε hε hε_lt φ
    simpa [familyR, show 0 < ε from hε, pR, hsup_eq s φ] using hmain
  have hT0_bound :
      ∀ φ : SchwartzNPoint d (n + m), ‖T0R φ‖ ≤ C_sem * pR φ := by
    intro φ
    exact le_of_tendsto (hpointwiseR φ).norm <| (hfamily_bound.mono fun ε hε => hε φ)
  have hsub_bound :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ φ : SchwartzNPoint d (n + m), ‖(familyR ε - T0R) φ‖ ≤ (2 * C_sem) * pR φ := by
    filter_upwards [hfamily_bound] with ε hε φ
    calc
      ‖(familyR ε - T0R) φ‖ = ‖familyR ε φ - T0R φ‖ := by
        simp [ContinuousLinearMap.sub_apply]
      _ ≤ ‖familyR ε φ‖ + ‖T0R φ‖ := norm_sub_le _ _
      _ ≤ C_sem * pR φ + C_sem * pR φ := add_le_add (hε φ) (hT0_bound φ)
      _ = (2 * C_sem) * pR φ := by ring
  have hMapsTo :
      ∀ {B : Set (SchwartzNPoint d (n + m))} {U : Set ℂ},
        Bornology.IsVonNBounded ℝ B →
        U ∈ nhds (0 : ℂ) →
        ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          Set.MapsTo (fun φ => (familyR ε - T0R) φ) B U := by
    intro B U hB hU
    apply SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net
      (E := NPointDomain d (n + m)) (F := ℂ) (G := ℂ) (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (T := familyR) (L := T0R) pR (C := 2 * C_sem)
    · positivity
    · exact hU
    · exact hsub_bound
    · exact hpointwiseR
    · intro ε hε
      obtain ⟨t, htB, hcover⟩ :=
        NuclearSpace.finite_net_of_schwartz_seminorm_of_isVonNBounded
          (E := NPointDomain d (n + m)) s hB ε hε
      refine ⟨t, ?_⟩
      intro φ hφ
      rcases hcover φ hφ with ⟨ψ, hψt, hψB, hφψ⟩
      refine ⟨ψ, hψt, ?_⟩
      simpa [pR] using hφψ
  refine ⟨T_t, ?_⟩
  have hzero :
      Filter.Tendsto (fun ε : ℝ => familyR ε - T0R)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (0 : SchwartzNPoint d (n + m) →L[ℝ] ℂ)) := by
    rw [ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff]
    intro SV hSV
    rcases hSV with ⟨hB, hU⟩
    simpa [Set.MapsTo] using (hMapsTo hB hU)
  have hT0R_eq : T0R = T_t.restrictScalars ℝ := by
    ext φ
    rfl
  have hfamilyR_eq :
      familyR = fun ε : ℝ =>
        (((if hε : 0 < ε then
          section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε
        else
          0) : SchwartzNPoint d (n + m) →L[ℂ] ℂ).restrictScalars ℝ) := by
    funext ε
    by_cases hε : 0 < ε
    · ext φ
      simp [familyR, hε]
    · ext φ
      simp [familyR, hε]
  have hrestrict :
      Filter.Tendsto
        (fun ε : ℝ =>
          (((if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε
          else
            0) : SchwartzNPoint d (n + m) →L[ℂ] ℂ).restrictScalars ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (T_t.restrictScalars ℝ)) := by
    have hadd := hzero.const_add T0R
    simpa [hfamilyR_eq, hT0R_eq, familyR, T0R, sub_eq_add_neg, Pi.add_apply,
      add_comm, add_left_comm, add_assoc] using hadd
  have hEmb :=
      ContinuousLinearMap.isEmbedding_restrictScalars
        (𝕜 := ℂ) (E := SchwartzNPoint d (n + m)) (F := ℂ) ℝ
  rw [show nhds T_t =
      Filter.comap (ContinuousLinearMap.restrictScalars ℝ)
        (nhds (T_t.restrictScalars ℝ)) by
      simpa using hEmb.nhds_eq_comap T_t]
  rw [Filter.tendsto_iff_comap] at hrestrict ⊢
  simpa [Filter.comap_comap, Function.comp] using hrestrict

/-- Dominated-convergence supplier for the actual ambient fixed-time shell.
This is the exact theorem-sized contract exposed beneath `hlimit_os`: if the
live shell integrand against a fixed ambient test `h` is pointwise driven to
zero and uniformly dominated by an integrable ambient bound near `ε = 0+`, then
the corresponding raw shell integral tends to `0`. -/
private theorem
    section43_fixedTimeShellRaw_on_section43PositiveEnergyRegion_compl_eventually_bounded
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ)
    (h : SchwartzNPoint d (n + m)) :
    ∃ bound : NPointDomain d (n + m) → ℝ,
      MeasureTheory.Integrable bound MeasureTheory.volume ∧
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ y : NPointDomain d (n + m),
          ‖Set.indicator ((section43PositiveEnergyRegion d (n + m))ᶜ)
              (fun y =>
                bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun k μ =>
                      ↑(y k μ) +
                        ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                          Complex.I)
                    (t : ℂ)) *
                  h y) y‖ ≤ bound y := by
  obtain ⟨C_shell, N, hC_shell_pos, hcoeff_bound⟩ :=
    section43_fixedTimeShellRaw_uniformPolyGrowth_fixedTime
      (d := d) OS lgc hm t
  let K : NPointDomain d (n + m) → ℂ := fun y =>
    ↑(C_shell * (1 + ‖y‖) ^ N)
  have hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume := by
    have hK_cont : Continuous K := by
      exact Complex.continuous_ofReal.comp
        (continuous_const.mul ((continuous_const.add continuous_norm).pow N))
    exact hK_cont.aestronglyMeasurable
  have hK_norm (y : NPointDomain d (n + m)) :
      ‖K y‖ = C_shell * (1 + ‖y‖) ^ N := by
    have hnonneg : 0 ≤ C_shell * (1 + ‖y‖) ^ N := by
      positivity
    change ‖((C_shell * (1 + ‖y‖) ^ N : ℝ) : ℂ)‖ = C_shell * (1 + ‖y‖) ^ N
    rw [Complex.norm_real, Real.norm_of_nonneg hnonneg]
  have hK_bound :
      ∀ᵐ y : NPointDomain d (n + m) ∂MeasureTheory.volume,
        ‖K y‖ ≤ C_shell * (1 + ‖y‖) ^ N := by
    filter_upwards with y
    rw [hK_norm y]
  have hbound_int_complex :
      MeasureTheory.Integrable (fun y : NPointDomain d (n + m) => K y * h y)
        MeasureTheory.volume :=
    schwartz_polynomial_kernel_integrable
      (d := d) (n := n + m) K hK_meas C_shell N hC_shell_pos hK_bound h
  have hbound_int :
      MeasureTheory.Integrable
        (fun y : NPointDomain d (n + m) =>
          C_shell * (1 + ‖y‖) ^ N * ‖h y‖)
        MeasureTheory.volume := by
    convert hbound_int_complex.norm using 1
    ext y
    rw [norm_mul]
    rw [hK_norm y, mul_assoc]
  refine ⟨fun y => C_shell * (1 + ‖y‖) ^ N * ‖h y‖, hbound_int, ?_⟩
  have h_mem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, by simp,
      fun ε hε => Set.mem_Ioo.mpr ⟨Set.mem_Ioi.mp hε.2, Set.mem_Iio.mp hε.1⟩⟩
  apply Filter.eventually_of_mem h_mem
  intro ε hε y
  obtain ⟨hε_pos, hε_lt⟩ := Set.mem_Ioo.mp hε
  by_cases hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ
  · simp only [Set.indicator_of_mem hy]
    calc
      ‖bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          h y‖
          = ‖bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ))‖ * ‖h y‖ := by
              rw [norm_mul]
      _ ≤ (C_shell * (1 + ‖y‖) ^ N) * ‖h y‖ := by
        gcongr
        exact hcoeff_bound ε hε_pos hε_lt y
      _ = C_shell * (1 + ‖y‖) ^ N * ‖h y‖ := by ring
  · rw [Set.indicator_of_notMem hy, norm_zero]
    positivity

/-- Local flat boundary-regularity package on the complement side for the
fixed-time shell continuation. This is the exact theorem-(1) seam beneath the
coefficient limit: an open flat neighborhood inside the flattened complement
image together with `ContinuousWithinAt` of the flattened continuation at every
real boundary point of that neighborhood. -/
private theorem
    section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ)
    (y : NPointDomain d (n + m))
    (hcont_shifted :
      ContinuousWithinAt
        (bvt_F OS lgc (n + m))
        (ForwardTube d (n + m))
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ => (y k μ : ℂ)) (t : ℂ))) :
    let H_t : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ :=
      fun z =>
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))
    ContinuousWithinAt H_t
      (ForwardTube d (n + m))
      (fun k μ => (y k μ : ℂ)) := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let shift : Fin (n + m) → Fin (d + 1) → ℂ :=
    fun k μ =>
      if j.val ≤ k.val ∧ μ = (0 : Fin (d + 1)) then
        (t : ℂ)
      else
        0
  have hxi_eq :
      (fun z : Fin (n + m) → Fin (d + 1) → ℂ => xiShift j 0 z (t : ℂ)) =
        fun z => z + shift := by
    funext z
    simpa [shift] using
      section43_fixedTime_xiShift_zero_eq_add_indicator (d := d) hm t z
  have hinner :
      ContinuousWithinAt
        (fun z : Fin (n + m) → Fin (d + 1) → ℂ => xiShift j 0 z (t : ℂ))
        (ForwardTube d (n + m))
        (fun k μ => (y k μ : ℂ)) := by
    rw [hxi_eq]
    exact (continuous_id.add continuous_const).continuousAt.continuousWithinAt
  have hmap :
      Set.MapsTo
        (fun z : Fin (n + m) → Fin (d + 1) → ℂ => xiShift j 0 z (t : ℂ))
        (ForwardTube d (n + m))
        (ForwardTube d (n + m)) := by
    intro z hz
    rw [forwardTube_eq_imPreimage] at hz ⊢
    have him :
        (fun k μ => (xiShift j 0 z (t : ℂ) k μ).im) =
          fun k μ => (z k μ).im := by
      ext k μ
      by_cases hshift : j.val ≤ k.val ∧ μ = (0 : Fin (d + 1))
      · have hshift' : j ≤ k ∧ μ = (0 : Fin (d + 1)) := by simpa using hshift
        simp [xiShift, hshift']
      · have hshift' : ¬ (j ≤ k ∧ μ = (0 : Fin (d + 1))) := by simpa using hshift
        simp [xiShift, hshift']
    simpa [Set.mem_setOf_eq, him] using hz
  change
    (ContinuousWithinAt
      ((bvt_F OS lgc (n + m)) ∘
        (fun z : Fin (n + m) → Fin (d + 1) → ℂ => xiShift j 0 z (t : ℂ)))
      (ForwardTube d (n + m))
      (fun k μ => (y k μ : ℂ)))
  exact
    ContinuousWithinAt.comp
      (f := fun z : Fin (n + m) → Fin (d + 1) → ℂ => xiShift j 0 z (t : ℂ))
      (g := bvt_F OS lgc (n + m))
      (s := ForwardTube d (n + m))
      (t := ForwardTube d (n + m))
      (x := fun k μ => (y k μ : ℂ))
      hcont_shifted hinner hmap

/-- Local flat boundary-regularity package on the complement side for the
fixed-time shell continuation. After the proved `xiShift` transport lemma just
above, the only remaining content is continuity of raw `bvt_F` at the shifted
real boundary point. -/
private theorem
    section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ)
    (y : NPointDomain d (n + m))
    (hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ) :
    ContinuousWithinAt
      (bvt_F OS lgc (n + m))
      (ForwardTube d (n + m))
      (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun k μ => (y k μ : ℂ)) (t : ℂ)) := by
  sorry

/-- Local flat boundary-regularity package on the complement side for the
fixed-time shell continuation. After the proved `xiShift` transport lemma just
above, the only remaining content is continuity of raw `bvt_F` at the shifted
real boundary point. -/
private theorem
    section43_fixedTimeShellRaw_pointwiseContinuity_on_section43PositiveEnergyRegion_compl
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ)
    (y : NPointDomain d (n + m))
    (hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ) :
    let H_t : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ :=
      fun z =>
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))
    ContinuousWithinAt H_t
      (ForwardTube d (n + m))
      (fun k μ => (y k μ : ℂ)) := by
  have hcont_shifted :
      ContinuousWithinAt
        (bvt_F OS lgc (n + m))
        (ForwardTube d (n + m))
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ => (y k μ : ℂ)) (t : ℂ)) :=
    section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl
      (d := d) OS lgc hm t y hy
  simpa using
    section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point
      (d := d) OS lgc hm t y hcont_shifted

/-- Local flat boundary-regularity package on the complement side for the
fixed-time shell continuation. This is just the flattening transport of the
unflattened pointwise shell continuity theorem immediately above. -/
private theorem
    section43_fixedTimeShellRaw_pointwiseFlatContinuity_on_section43PositiveEnergyRegion_compl
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ)
    (xflat : Fin ((n + m) * (d + 1)) → ℝ)
    (hxflat : xflat ∈ (flattenCLEquivReal (n + m) (d + 1)) ''
      ((section43PositiveEnergyRegion d (n + m))ᶜ)) :
    let G_t : (Fin ((n + m) * (d + 1)) → ℂ) → ℂ :=
      fun zflat =>
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))
    ContinuousWithinAt G_t
      (SCV.TubeDomain (ForwardConeFlat d (n + m)))
      (SCV.realEmbed xflat) := by
  rcases hxflat with ⟨y, hy, rfl⟩
  let e := flattenCLEquiv (n + m) (d + 1)
  let H_t : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ :=
    fun z =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))
  set G_t : (Fin ((n + m) * (d + 1)) → ℂ) → ℂ :=
    fun zflat =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 (e.symm zflat) (t : ℂ)) with hG_t
  have hH :
      ContinuousWithinAt H_t
        (ForwardTube d (n + m))
        (fun k μ => (y k μ : ℂ)) := by
    simpa [H_t] using
      section43_fixedTimeShellRaw_pointwiseContinuity_on_section43PositiveEnergyRegion_compl
        (d := d) OS lgc hm t y hy
  have he :
      ContinuousWithinAt e.symm
        (SCV.TubeDomain (ForwardConeFlat d (n + m)))
        (SCV.realEmbed (flattenCLEquivReal (n + m) (d + 1) y)) :=
    e.symm.continuous.continuousAt.continuousWithinAt
  have hx :
      e.symm (SCV.realEmbed (flattenCLEquivReal (n + m) (d + 1) y)) =
        (fun k μ => (y k μ : ℂ)) := by
    ext k μ
    simp [e, SCV.realEmbed, flattenCLEquiv_symm_apply, flattenCLEquivReal_apply]
  have hH' :
      ContinuousWithinAt H_t
        (ForwardTube d (n + m))
        (e.symm (SCV.realEmbed (flattenCLEquivReal (n + m) (d + 1) y))) := by
    simpa [hx] using hH
  have hmap : Set.MapsTo e.symm
      (SCV.TubeDomain (ForwardConeFlat d (n + m)))
      (ForwardTube d (n + m)) := by
    intro zflat hzflat
    rw [forwardTube_eq_imPreimage]
    simpa [ForwardConeFlat] using
      flattenCLEquiv_symm_mem_tubeDomainSetPi_of_mem_tubeDomain_image
        (C := ForwardConeAbs d (n + m)) hzflat
  change
    ContinuousWithinAt G_t
      (SCV.TubeDomain (ForwardConeFlat d (n + m)))
      (SCV.realEmbed (flattenCLEquivReal (n + m) (d + 1) y))
  simpa [hG_t, H_t, e, Function.comp] using
    (ContinuousWithinAt.comp
      (f := e.symm)
      (g := H_t)
      (s := SCV.TubeDomain (ForwardConeFlat d (n + m)))
      (t := ForwardTube d (n + m))
      (x := SCV.realEmbed (flattenCLEquivReal (n + m) (d + 1) y))
      hH' he hmap)

/-- Local flat boundary-regularity package on the complement side for the
fixed-time shell continuation. This is the exact theorem-(1) seam beneath the
coefficient limit: an open flat neighborhood inside the flattened complement
image together with `ContinuousWithinAt` of the flattened continuation at every
real boundary point of that neighborhood. -/
private theorem
    section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ)
    (y : NPointDomain d (n + m))
    (hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ) :
    let G_t : (Fin ((n + m) * (d + 1)) → ℂ) → ℂ :=
      fun zflat =>
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))
    ∃ Uflat : Set (Fin ((n + m) * (d + 1)) → ℝ),
      IsOpen Uflat ∧
      flattenCLEquivReal (n + m) (d + 1) y ∈ Uflat ∧
      Uflat ⊆ (flattenCLEquivReal (n + m) (d + 1)) ''
        ((section43PositiveEnergyRegion d (n + m))ᶜ) ∧
      ∀ xflat ∈ Uflat, ContinuousWithinAt G_t
        (SCV.TubeDomain (ForwardConeFlat d (n + m)))
        (SCV.realEmbed xflat) := by
  let eR := flattenCLEquivReal (n + m) (d + 1)
  let Uflat : Set (Fin ((n + m) * (d + 1)) → ℝ) :=
    eR '' ((section43PositiveEnergyRegion d (n + m))ᶜ)
  refine ⟨Uflat, ?_, ?_, ?_, ?_⟩
  · have hComplOpen :
        IsOpen ((section43PositiveEnergyRegion d (n + m))ᶜ) := by
      have hClosed :
          IsClosed (section43PositiveEnergyRegion d (n + m)) := by
        simp only [section43PositiveEnergyRegion, Set.setOf_forall]
        exact isClosed_iInter (fun i : Fin (n + m) =>
          isClosed_le continuous_const
            (((continuous_apply (0 : Fin (d + 1))).comp (continuous_apply i)) :
              Continuous (fun q : NPointDomain d (n + m) => q i 0)))
      simpa using hClosed.isOpen_compl
    exact eR.toHomeomorph.isOpenMap _ hComplOpen
  · exact Set.mem_image_of_mem eR hy
  · intro x hx
    exact hx
  · intro xflat hxflat
    simpa [Uflat, eR] using
      section43_fixedTimeShellRaw_pointwiseFlatContinuity_on_section43PositiveEnergyRegion_compl
        (d := d) OS lgc hm t xflat hxflat

/-- Holomorphy supplier for the flattened fixed-time shell continuation. This
is the exact extra SCV input needed by the explicit local trace-object route
beneath the coefficient limit. -/
private theorem section43_fixedTimeShellRaw_differentiableOn_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ) :
    let G_t : (Fin ((n + m) * (d + 1)) → ℂ) → ℂ :=
      fun zflat =>
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))
    DifferentiableOn ℂ G_t (SCV.TubeDomain (ForwardConeFlat d (n + m))) := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let F_analytic :
      (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ :=
    fun z => bvt_F OS lgc (n + m) (xiShift j 0 z (t : ℂ))
  have hF_holo :
      DifferentiableOn ℂ F_analytic (TubeDomainSetPi (ForwardConeAbs d (n + m))) := by
    intro z hz
    have hz_shift_mem :
        xiShift j 0 z (t : ℂ) ∈ ForwardTube d (n + m) := by
      rw [forwardTube_eq_imPreimage]
      change (fun k μ => (z k μ).im) ∈ ForwardConeAbs d (n + m) at hz
      have him :
          (fun k μ => (xiShift j 0 z (t : ℂ) k μ).im) =
            fun k μ => (z k μ).im := by
        ext k μ
        by_cases hshift : j.val ≤ k.val ∧ μ = (0 : Fin (d + 1))
        · have hshift' : j ≤ k ∧ μ = (0 : Fin (d + 1)) := by simpa using hshift
          simp [xiShift, hshift']
        · have hshift' : ¬ (j ≤ k ∧ μ = (0 : Fin (d + 1))) := by simpa using hshift
          simp [xiShift, hshift']
      simpa [him] using hz
    have hft_open : IsOpen (ForwardTube d (n + m)) := by
      simpa [BHW_forwardTube_eq (d := d) (n := n + m)] using
        (BHW.isOpen_forwardTube (d := d) (n := n + m))
    have houter :
        DifferentiableAt ℂ (bvt_F OS lgc (n + m)) (xiShift j 0 z (t : ℂ)) :=
      (bvt_F_holomorphic (d := d) OS lgc (n + m)).differentiableAt
        (hft_open.mem_nhds hz_shift_mem)
    let shift : Fin (n + m) → Fin (d + 1) → ℂ :=
      fun k μ =>
        if j.val ≤ k.val ∧ μ = (0 : Fin (d + 1)) then
          (t : ℂ)
        else
          0
    have hinner :
        DifferentiableAt ℂ
          (fun z : Fin (n + m) → Fin (d + 1) → ℂ => xiShift j 0 z (t : ℂ)) z := by
      convert (differentiableAt_id.add_const shift : DifferentiableAt ℂ
        (fun z : Fin (n + m) → Fin (d + 1) → ℂ => z + shift) z) using 1
      ext w k μ
      by_cases hshift : j.val ≤ k.val ∧ μ = (0 : Fin (d + 1))
      · have hshift' : j ≤ k ∧ μ = (0 : Fin (d + 1)) := by simpa using hshift
        simp [shift, xiShift, hshift']
      · have hshift' : ¬ (j ≤ k ∧ μ = (0 : Fin (d + 1))) := by simpa using hshift
        simp [shift, xiShift, hshift']
    exact (houter.comp z hinner).differentiableWithinAt
  have hF_holo_forward :
      DifferentiableOn ℂ F_analytic (ForwardTube d (n + m)) := by
    simpa [forwardTube_eq_imPreimage] using hF_holo
  have hG_diff :
      DifferentiableOn ℂ
        (F_analytic ∘ (flattenCLEquiv (n + m) (d + 1)).symm)
        (SCV.TubeDomain (ForwardConeFlat d (n + m))) :=
    differentiableOn_flatten hF_holo_forward
  simpa [F_analytic] using hG_diff

/-- Honest coefficient-consumer split for the explicit local trace-object
route. On an open flat neighborhood `Uflat`, explicit holomorphy + tempered FL
data + a continuous trace object `B` + local annihilation of the boundary
distribution force the corresponding fixed-time shell coefficient to tend to
zero along the chosen cone ray. -/
private theorem
    section43_fixedTimeShellRaw_flat_coefficient_tendsto_zero_of_localTraceData
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ) :
    let G_t : (Fin ((n + m) * (d + 1)) → ℂ) → ℂ :=
      fun zflat =>
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))
    let hG_diff : DifferentiableOn ℂ G_t (SCV.TubeDomain (ForwardConeFlat d (n + m))) :=
      section43_fixedTimeShellRaw_differentiableOn_fixedTime
        (d := d) OS lgc hm t
    let hTempered : SCV.HasFourierLaplaceReprTempered (ForwardConeFlat d (n + m)) G_t :=
      section43_fixedTimeShellRaw_temperedRepr_fixedTime
        (d := d) OS lgc hm t
    ∀ (Uflat : Set (Fin ((n + m) * (d + 1)) → ℝ))
      (hUflat : IsOpen Uflat)
      (xflat : Fin ((n + m) * (d + 1)) → ℝ)
      (hxflat : xflat ∈ Uflat)
      {B : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ}
      (hB_contOn : ContinuousOn B Uflat)
      (ηflat : Fin ((n + m) * (d + 1)) → ℝ)
      (hηflat : ηflat ∈ ForwardConeFlat d (n + m))
      (htraceUflat : ∀ uflat ∈ Uflat,
        Filter.Tendsto
          (fun ε : ℝ => G_t (fun i => ↑(uflat i) + ↑ε * ↑(ηflat i) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (B uflat)))
      (h_dist_zero_local :
        ∀ f : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
          tsupport (f : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ) ⊆ Uflat →
            hTempered.dist f = 0),
      Filter.Tendsto
        (fun ε : ℝ => G_t (fun i => ↑(xflat i) + ↑ε * ↑(ηflat i) * Complex.I))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds 0) := by
  intro G_t hG_diff hTempered Uflat hUflat xflat hxflat B hB_contOn ηflat hηflat htraceUflat
    h_dist_zero_local
  have hB_zero_on : Set.EqOn B 0 Uflat := by
    refine SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      hUflat hB_contOn continuousOn_const ?_
    intro f hf_compact hf_supp
    have hrecov :=
      SCV.fourierLaplace_schwartz_integral_convergence_local_of_trace
        (C := ForwardConeFlat d (n + m))
        (forwardConeFlat_isOpen d (n + m))
        (forwardConeFlat_convex d (n + m))
        (forwardConeFlat_nonempty d (n + m))
        (forwardConeFlat_isCone d (n + m))
        hG_diff hTempered Uflat hUflat hB_contOn ηflat hηflat htraceUflat f hf_supp
        hf_compact
    have hdist := hTempered.boundary_value f ηflat hηflat
    have hEq : hTempered.dist f = ∫ y, B y * f y :=
      tendsto_nhds_unique hdist hrecov
    calc
      ∫ y, B y * f y = hTempered.dist f := hEq.symm
      _ = 0 := h_dist_zero_local f hf_supp
      _ = ∫ y, (0 : ℂ) * f y := by simp
  have hBxflat : B xflat = 0 := by
    simpa using hB_zero_on hxflat
  simpa [hBxflat] using htraceUflat xflat hxflat

/-- Dominated-convergence supplier for the actual ambient fixed-time shell.
This is the exact theorem-sized contract exposed beneath `hlimit_os`: if the
live shell integrand against a fixed ambient test `h` is pointwise driven to
zero and uniformly dominated by an integrable ambient bound near `ε = 0+`, then
the corresponding raw shell integral tends to `0`. -/
private theorem
    section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ)
    (y : NPointDomain d (n + m))
    (hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0) := by
  sorry

/-- Dominated-convergence supplier for the actual ambient fixed-time shell.
This is the exact theorem-sized contract exposed beneath `hlimit_os`: if the
live shell integrand against a fixed ambient test `h` is pointwise driven to
zero and uniformly dominated by an integrable ambient bound near `ε = 0+`, then
the corresponding raw shell integral tends to `0`. -/
private theorem
    section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ)
    (h : SchwartzNPoint d (n + m))
    (hq :
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          Set.indicator ((section43PositiveEnergyRegion d (n + m))ᶜ)
            (fun y =>
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    ↑(y k μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)) *
                h y) y)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0) := by
  let F : ℝ → NPointDomain d (n + m) → ℂ := fun ε y =>
    Set.indicator ((section43PositiveEnergyRegion d (n + m))ᶜ)
      (fun y =>
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          h y) y
  obtain ⟨bound, hbound_int, hbound⟩ :=
    section43_fixedTimeShellRaw_on_section43PositiveEnergyRegion_compl_eventually_bounded
      (d := d) OS lgc hm t h
  have hpointwise :
      ∀ y : NPointDomain d (n + m),
        Filter.Tendsto (fun ε : ℝ => F ε y)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    intro y
    by_cases hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ
    · simp only [F, Set.indicator_of_mem hy]
      have hcoeff :
          Filter.Tendsto
            (fun ε : ℝ =>
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    ↑(y k μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds 0) :=
        section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl
          (d := d) OS lgc hm t y hy
      simpa using hcoeff.mul tendsto_const_nhds
    · simp [F, Set.indicator_of_notMem hy]
  sorry

/-- Dominated-convergence supplier for the actual ambient fixed-time shell.
This is the exact theorem-sized contract exposed beneath `hlimit_os`: if the
live shell integrand against a fixed ambient test `h` is pointwise driven to
zero and uniformly dominated by an integrable ambient bound near `ε = 0+`, then
the corresponding raw shell integral tends to `0`. -/
private theorem section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (t : ℝ)
    (h : SchwartzNPoint d (n + m))
    (bound : NPointDomain d (n + m) → ℝ)
    (hbound :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ y : NPointDomain d (n + m),
          ‖bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              h y‖ ≤ bound y)
    (hbound_int : MeasureTheory.Integrable bound MeasureTheory.volume)
    (hlim :
      ∀ y : NPointDomain d (n + m),
        Filter.Tendsto
          (fun ε : ℝ =>
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              h y)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            h y)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0) := by
  let F : ℝ → NPointDomain d (n + m) → ℂ := fun ε y =>
    bvt_F OS lgc (n + m)
      (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I)
        (t : ℂ)) *
      h y
  have hF_meas :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        MeasureTheory.AEStronglyMeasurable (F ε) MeasureTheory.volume := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let coeff : NPointDomain d (n + m) → ℂ := fun y =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ))
    have hcoeff_cont : Continuous coeff := by
      rw [continuous_iff_continuousAt]
      intro y
      let shellMap : NPointDomain d (n + m) → Fin (n + m) → Fin (d + 1) → ℂ :=
        fun y =>
          xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)
      have hshell_mem : shellMap y ∈ ForwardTube d (n + m) := by
        simpa [shellMap, forwardTube_eq_imPreimage] using
          canonicalXiShift_mem_forwardTube (d := d) hm hε y
      have houter_cont : ContinuousAt (bvt_F OS lgc (n + m)) (shellMap y) := by
        let hft_open :
            IsOpen (ForwardTube d (n + m)) := by
          simpa [BHW_forwardTube_eq (d := d) (n := n + m)] using
            (BHW.isOpen_forwardTube (d := d) (n := n + m))
        have houter_diff :
            DifferentiableAt ℂ (bvt_F OS lgc (n + m)) (shellMap y) :=
          (bvt_F_holomorphic (d := d) OS lgc (n + m)).differentiableAt
            (hft_open.mem_nhds hshell_mem)
        exact houter_diff.continuousAt
      have hinner_cont : ContinuousAt shellMap y :=
        (contDiff_canonicalXiShift (d := d) hm t ε).continuous.continuousAt
      simpa [coeff, shellMap] using houter_cont.comp hinner_cont
    simpa [F, coeff] using (hcoeff_cont.mul h.continuous).aestronglyMeasurable
  have h_bound :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ᵐ y ∂MeasureTheory.volume, ‖F ε y‖ ≤ bound y := by
    refine hbound.mono ?_
    intro ε hε
    exact Filter.Eventually.of_forall hε
  have h_lim :
      ∀ᵐ y ∂MeasureTheory.volume,
        Filter.Tendsto (fun ε : ℝ => F ε y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    Filter.Eventually.of_forall hlim
  simpa [F] using
    (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume) (bound := bound) hF_meas h_bound hbound_int h_lim)

/-- Local real-scalar differentiability bridge for the boundary-value
coefficient on the shell codomain. This isolates the exact codomain-side
`restrictScalars` seam needed by the shell-coefficient differentiability
surface. -/
private theorem differentiableAt_bvt_F_restrictScalars
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    {z : Fin (n + m) → Fin (d + 1) → ℂ}
    (hz : DifferentiableAt ℂ (bvt_F OS lgc (n + m)) z) :
    DifferentiableAt ℝ (bvt_F OS lgc (n + m)) z := by
  letI : NormedSpace ℝ (Fin (n + m) → Fin (d + 1) → ℂ) :=
    NormedSpace.restrictScalars ℝ ℂ (Fin (n + m) → Fin (d + 1) → ℂ)
  haveI := IsScalarTower.restrictScalars ℝ ℂ (Fin (n + m) → Fin (d + 1) → ℂ)
  letI : NormedSpace ℝ ℂ := NormedSpace.restrictScalars ℝ ℂ ℂ
  haveI := IsScalarTower.restrictScalars ℝ ℂ ℂ
  exact hz.restrictScalars ℝ

/-- Real Fréchet differentiability package for the shell coefficient obtained by
composing the holomorphic `bvt_F` witness with the affine fixed-time canonical
shell map. This is the exact shell-local chain-rule bridge below the current
codomain-side `restrictScalars` seam. -/
private theorem hasFDerivAt_bvt_F_canonicalXiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε)
    (y : NPointDomain d (n + m)) :
    HasFDerivAt
      (fun y : NPointDomain d (n + m) =>
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)))
      (fderiv ℝ
        (fun y : NPointDomain d (n + m) =>
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ))) y)
      y := by
  let shellMap : NPointDomain d (n + m) → (Fin (n + m) → Fin (d + 1) → ℂ) :=
    fun y =>
      xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I)
        (t : ℂ)
  have hshell_mem : shellMap y ∈ ForwardTube d (n + m) := by
    simpa [shellMap, forwardTube_eq_imPreimage] using
      canonicalXiShift_mem_forwardTube (d := d) hm hε y
  have houter_diffC :
      DifferentiableAt ℂ (bvt_F OS lgc (n + m)) (shellMap y) := by
    have hft_open : IsOpen (ForwardTube d (n + m)) := by
      simpa [BHW_forwardTube_eq (d := d) (n := n + m)] using
        (BHW.isOpen_forwardTube (d := d) (n := n + m))
    exact
      (bvt_F_holomorphic (d := d) OS lgc (n + m)).differentiableAt
        (hft_open.mem_nhds hshell_mem)
  have houter_diffR :
      DifferentiableAt ℝ (bvt_F OS lgc (n + m)) (shellMap y) :=
    differentiableAt_bvt_F_restrictScalars (d := d) OS lgc houter_diffC
  exact
    (houter_diffR.comp y
      (differentiableAt_canonicalXiShift (d := d) hm t ε y)).hasFDerivAt

/-- Exact Step-1 Wightman-side boundary-value shell for the current
Lemma-4.2 route: the reconstructed pairing against the right-time-shifted
ambient tensor is the canonical forward-cone boundary value of the matching
`bvt_F` integral shell. This is just `bvt_boundary_values` specialized to the
current theorem surface, but naming it here keeps the remaining blocker honest:
the next missing step is the time-variable interchange on this explicit shell,
not another hidden boundary-value reduction. -/
private theorem tendsto_bvt_F_canonical_conjTensorProduct_timeShift_boundaryValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m) (t : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d (n + m),
          bvt_F OS lgc (n + m) (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)))) := by
  let η0 := canonicalForwardConeDirection (d := d) (n + m)
  have hη0 : InForwardCone d (n + m) η0 :=
    canonicalForwardConeDirection_mem (d := d) (n + m)
  simpa [η0] using
    (bvt_boundary_values OS lgc (n + m)
      (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) η0 hη0)

/-- Step-1/2 boundary-value form of the current Lemma-4.2 lane: after moving
the right-time shift from the ambient test tensor into the explicit canonical
`ξ`-shift shell, the resulting shell still has boundary value equal to the
reconstructed Wightman pairing against the right-time-shifted ambient tensor.

This is exactly the current-code replacement for the older hidden
"Wightman-side shell rewrite" slogan: the rewrite is now explicit, checked, and
still lands at the same boundary value. -/
private theorem tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m) (t : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)))) := by
  have hEq :
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d (n + m),
          bvt_F OS lgc (n + m) (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    symm
    exact bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift
      (d := d) (OS := OS) (lgc := lgc) (hm := hm) (φ := φ) (ψ := ψ) (t := t) (ε := ε)
  exact Filter.Tendsto.congr' hEq.symm <|
    tendsto_bvt_F_canonical_conjTensorProduct_timeShift_boundaryValue
      (d := d) (OS := OS) (lgc := lgc) (φ := φ) (ψ := ψ) (t := t)

/-- Step-3 reduction for the current Lemma-4.2 route: once the canonical
`ξ`-shift shell is shown to converge back to some explicit scalar `L` as
`ε → 0+`, that scalar is forced to be the reconstructed Wightman pairing
against the right-time-shifted ambient tensor.

This keeps the remaining analytic content honest. After the Step-1/2 shell
rewrite above, the next unresolved theorem is precisely the limit identification
for the explicit canonical `ξ`-shift shell, not another hidden boundary-value
argument. -/
private theorem bvt_W_eq_of_tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m) (t : ℝ)
    {L : ℂ}
    (hL :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds L)) :
    L =
      bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) := by
  have hW :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)))) :=
    tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue
      (d := d) (OS := OS) (lgc := lgc) (hm := hm) (φ := φ) (ψ := ψ) (t := t)
  exact tendsto_nhds_unique hL hW

/-- On the exact `bvt_F` shell used by the current Lemma-4.2 lane, the
positive-real OS matrix element converges back to the unshifted Euclidean term
as `t → 0+`. This is the current-code specialization of the already-proved
Schwinger-side boundary-value theorem to the explicit `bvt_F` kernel. -/
private theorem tendsto_bvt_F_osConjTensorProduct_timeShift_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    Filter.Tendsto
      (fun t : ℝ =>
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)))) := by
  have htrace :
      (fun t : ℝ =>
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact bvt_F_osConjTensorProduct_timeShift_eq_xiShift
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) (t := t) ht
  exact Filter.Tendsto.congr' htrace.symm <|
    bvt_tendsto_singleSplit_xiShift_nhdsWithin_zero_schwinger
      (d := d) (OS := OS) (lgc := lgc) n m hm
      f hf_ord hf_compact g hg_ord hg_compact

/-- Compact-support reduction of the current Stage-5 frontier: if on positive
real times the Euclidean/OS right-time-shift shell already agrees with the
reconstructed Wightman pairing against the corresponding right-time-shifted
ambient test, then the desired kernel equality at `t = 0` follows formally by
taking `t → 0+` on both sides.

This keeps the remaining live content in the exact shape the proof docs now
advertise: the unresolved theorem is the positive-real time-variable
interchange / boundary-value identification, not another shell-limit lemma. -/
private theorem kernel_eq_of_timeShift_eq_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hreal :
      ∀ t : ℝ, 0 < t →
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
          =
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ)
      =
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  have hS :
      Filter.Tendsto
        (fun t : ℝ =>
          OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)))) := by
    exact tendsto_bvt_F_osConjTensorProduct_timeShift_nhdsWithin_zero
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
  have hW :
      Filter.Tendsto
        (fun t : ℝ =>
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ))) := by
    exact tendsto_bvt_W_conjTensorProduct_timeShift_nhdsWithin_zero
      (d := d) (OS := OS) (lgc := lgc)
      (f := φ) (g := ψ) (hg_compact := hψ_compact)
  have hEq :
      (fun t : ℝ =>
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hreal t ht
  have hS_as_W :
      Filter.Tendsto
        (fun t : ℝ =>
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)))) :=
    Filter.Tendsto.congr' hEq hS
  exact tendsto_nhds_unique hW hS_as_W

/-- Equivalent current-code reduction with the OS side written on the direct
`ξ`-shift shell: if for all positive real `t` the current OS `ξ`-shift shell
already agrees with the reconstructed Wightman pairing against the right-time
shifted ambient test, then the kernel equality at `t = 0` follows.

This is just `kernel_eq_of_timeShift_eq_on_positiveReals` after rewriting the
OS side to the actual `bvt_F` `ξ`-shift shell used by the current Lemma-4.2
lane. It does not pretend the Wightman side has already been rewritten to the
same raw integral surface; that remaining boundary-value/time-interchange step
is still the live Stage-5 content. -/
private theorem kernel_eq_of_osXiShift_eq_bvt_W_timeShift_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hreal :
      ∀ t : ℝ, 0 < t →
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y) =
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ)
      =
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  refine kernel_eq_of_timeShift_eq_on_positiveReals
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (hψ_compact := hψ_compact) ?_
  intro t ht
  rw [bvt_F_osConjTensorProduct_timeShift_eq_xiShift
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) (t := t) ht]
  exact hreal t ht

/-- Honest Stage-5 reduction for the current Lemma-4.2 lane: to prove the
kernel equality at `t = 0`, it is enough to show that for every positive real
`t`, the canonical forward-cone boundary-value shell converges to the explicit
current-code `ξ`-shift shell against the positive-time preimages.

This theorem is the immediate consumer of the new Step-1/2 shell rewrite. It
shrinks the remaining live analytic content to one positive-real shell-limit
statement, without reviving any false same-shell shortcut. -/
private theorem kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_osXiShift_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hlimit :
      ∀ t : ℝ, 0 < t →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    ↑(y k μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)) *
                (φ.conjTensorProduct ψ) y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                (f.osConjTensorProduct g) y))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  refine kernel_eq_of_osXiShift_eq_bvt_W_timeShift_on_positiveReals
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (hψ_compact := hψ_compact) ?_
  intro t ht
  exact
    (bvt_W_eq_of_tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (t := t)
      (hL := hlimit t ht))

/-- Reusable one-variable right-half-plane uniqueness step for the current
Lemma-4.2 route: if a holomorphic scalar `H` agrees on positive real points
both with the explicit preimage-side `singleSplit_xiShift` shell and with the
ambient Wightman time-shift pairing, then the chosen `singleSplit_xiShift`
holomorphic trace already agrees with that ambient Wightman pairing on
positive real times.

This is the exact reusable analytic theorem slot described in the proof docs
as `one_variable_time_interchange_for_wightman_pairing`. The later concrete
Section-4.3 adapter still has to construct such an `H` from the ambient
representative / positive-time preimage hypotheses.

Exact current pre-witness seam after the source audit:
- there is no smaller honest theorem on the same explicit ambient / preimage
  inputs that lands strictly between the current slice package and the witness
  consumed here;
- the first exact assembly ingredient is already visible one level below this
  theorem: for fixed
  `hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩`
  and
  `hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩`,
  one needs a single upper-half-plane scalar assembled from the slice package,
  with theorem surface
  `∃ Hs : ℂ → ℂ,
      DifferentiableOn ℂ Hs SCV.upperHalfPlane ∧
      (∀ t : ℝ, 0 < t →
        Hs ((t : ℂ) * Complex.I) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ))`;
  this is the exact `hH_imag_os` input consumed later by
  `lemma42_matrix_element_time_interchange`, and rotating such an `Hs` is the
  first honest ingredient of the right-half-plane witness constructor used
  here;
- the exact first obstruction inside that constructor is not another generic
  holomorphic-existence step but a fixed-pair packaging/equality step:
  starting from the slice-indexed data delivered by
  `partialFourierSpatial_timeSlice_hasPaleyWienerExtension`,
  `partialFourierSpatial_timeSliceCanonicalExtension`,
  `section43_iteratedSlice_descendedPairing`,
  `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`,
  and
  `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`,
  one still needs a theorem that assembles those equalities over the Section-4.3
  slice variables into one scalar `Hs` attached to the fixed pair
  `(φ, ψ)` / `(f, g)`, and proves that this assembled scalar is exactly
  `OSInnerProductTimeShiftHolomorphicValue ...` on the positive imaginary axis;
- the source already reaches the slice-level endpoint
  `section43_iteratedSlice_descendedPairing`, together with the scalar slice
  bridge theorems
  `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
  and
  `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`;
- those theorems are still indexed by slice data `(r, t, ht, ξ, w)` and only
  compare one-variable slice pairings or their canonical upper-half-plane
  extensions along `os1TransportComponent` equalities;
- in particular, none of them performs the missing aggregation over the frozen
  slice parameters or identifies the resulting scalar with the semigroup-side
  quantity `OSInnerProductTimeShiftHolomorphicValue`; they only move ambient
  representatives to their positive-time preimages inside already chosen slice
  pairings;
- the already-landed theorem
  `section43_fixedPair_upperHalfPlaneScalarization` is not that missing
  assembly step: its proof packages only the semigroup-side scalar
  `w ↦ OSInnerProductTimeShiftHolomorphicValue ... (-I * w)` and does not use
  `φ`, `ψ`, `hφf`, or `hψg` in any mathematically active way;
- none of the current source theorems states, or can by itself recover, the
  first honest ambient fixed-pair output: a right-half-plane witness
  `H : ℂ → ℂ` whose positive-real values are simultaneously the full
  `(n + m)`-point `xiShift` shell against `f.osConjTensorProduct g` and the
  ambient Wightman pairing
  `bvt_W ... (φ.conjTensorProduct (timeShiftSchwartzNPoint ... ψ))`;
- so, after the semigroup-only scalarization has been factored out, the
  earliest honest next theorem on these inputs is the ambient witness
  constructor itself:
  from
  `hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩`
  and
  `hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩`,
  together with the existing compact-support hypotheses, produce
  `∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (f.osConjTensorProduct g) y) ∧
      (∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t ψ)))`;
- on the explicit family inputs used later in
  `exists_bounded_componentwise_onImage_supplier_data_of_preimageFamilies`,
  instantiating this theorem for each `(N, n, k)` remains exactly the missing
  supplier step before the public `hreal` payload;
- therefore no honest wrapper theorem should be inserted between the explicit
  family inputs and this witness constructor. -/
private theorem one_variable_time_interchange_for_wightman_pairing
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (H : ℂ → ℂ)
    (hH_holo : DifferentiableOn ℂ H {z : ℂ | 0 < z.re})
    (hH_real_shell :
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (f.osConjTensorProduct g) y)
    (hH_real_wightman :
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) :
    ∀ t : ℝ, 0 < t →
      bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ) =
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) := by
  have hEqOn :
      Set.EqOn H
        (bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact)
        {z : ℂ | 0 < z.re} :=
    bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
      (H := H) hH_holo hH_real_shell
  intro t ht
  have ht_mem : (t : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    simpa using ht
  calc
    bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
      = H (t : ℂ) := by
          symm
          exact hEqOn ht_mem
    _ =
      bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) :=
      hH_real_wightman t ht

/-- Internal-supplier reduction for the current Stage-5 frontier: if the
chosen one-variable `singleSplit_xiShift` holomorphic trace built from the
positive-time preimages `f, g` already agrees on positive real times with the
reconstructed Wightman pairing against the ambient representatives `φ, ψ`,
then the desired kernel equality at `t = 0` follows.

This keeps the public theorem surface on the corrected ambient
representative/preimage data while allowing the existing `singleSplit`
holomorphic trace to be used only as an internal proof supplier. -/
private theorem kernel_eq_of_singleSplit_eq_bvt_W_timeShift_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hreal :
      ∀ t : ℝ, 0 < t →
        bvt_singleSplit_xiShiftHolomorphicValue
            (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
          =
            bvt_W OS lgc (n + m)
              (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  have hW :
      Filter.Tendsto
        (fun t : ℝ =>
          bvt_singleSplit_xiShiftHolomorphicValue
            (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W OS lgc (n + m)
            (φ.conjTensorProduct ψ))) :=
    tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_ambient_conjTensorProduct_timeShift
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) hreal
  have hS :
      Filter.Tendsto
        (fun t : ℝ =>
          bvt_singleSplit_xiShiftHolomorphicValue
            (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)))) :=
    tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
  exact tendsto_nhds_unique hW hS

/-- Honest Stage-5 per-pair kernel reduction after the reusable Section-8
uniqueness step: once a holomorphic witness `H` on the right half-plane is
constructed with the correct positive-real shell values and the correct
positive-real Wightman values, the desired kernel equality at `t = 0` follows
formally.

This packages the existing kernel reduction with
`one_variable_time_interchange_for_wightman_pairing`, so the remaining live
analytic job is now exactly the construction of such an `H` from the ambient
representative / positive-time preimage data. -/
private theorem kernel_eq_of_one_variable_time_interchange_for_wightman_pairing
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (H : ℂ → ℂ)
    (hH_holo : DifferentiableOn ℂ H {z : ℂ | 0 < z.re})
    (hH_real_shell :
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (f.osConjTensorProduct g) y)
    (hH_real_wightman :
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  apply kernel_eq_of_singleSplit_eq_bvt_W_timeShift_on_positiveReals
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (hψ_compact := hψ_compact)
  exact one_variable_time_interchange_for_wightman_pairing
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (H := H) hH_holo hH_real_shell hH_real_wightman

/-- Semigroup-side variant of the same reduction: since the chosen
`singleSplit_xiShift` holomorphic trace already agrees with the OS
time-shift holomorphic matrix element on the whole right half-plane, it is
enough to identify that OS holomorphic value with the reconstructed Wightman
pairing on positive real times. -/
private theorem kernel_eq_of_osHolomorphicValue_eq_bvt_W_timeShift_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hreal :
      ∀ t : ℝ, 0 < t →
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ)
          =
            bvt_W OS lgc (n + m)
              (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  refine kernel_eq_of_singleSplit_eq_bvt_W_timeShift_on_positiveReals
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (hψ_compact := hψ_compact) ?_
  intro t ht
  rw [bvt_xiShift_eq_osInnerProduct_holomorphicValue_single
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (z := (t : ℂ)) (hz := by simpa using ht)]
  exact hreal t ht

/-- Current best Stage-5 reduction: to prove the kernel equality at `t = 0`, it
is enough to show that for every positive real `t`, the explicit canonical
forward-cone `ξ`-shift shell has boundary value equal to the OS holomorphic
matrix element for the positive-time preimages.

This is the exact theorem surface the current branch-`3b` / Section-4.3
machinery is built to attack: the Wightman side stays on the explicit canonical
shell, while the target scalar is the already-built semigroup-side holomorphic
family rather than a raw same-shell comparison. -/
private theorem kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_osHolomorphicValue_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hlimit :
      ∀ t : ℝ, 0 < t →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    ↑(y k μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)) *
                (φ.conjTensorProduct ψ) y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ)))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  refine kernel_eq_of_osHolomorphicValue_eq_bvt_W_timeShift_on_positiveReals
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (hψ_compact := hψ_compact) ?_
  intro t ht
  exact
    (bvt_W_eq_of_tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (t := t)
      (hL := hlimit t ht))

/-- Upper-half-plane witness variant of the same Stage-5 reduction: if the
canonical forward-cone shell converges for each positive real `t` to the value
of some ambient upper-half-plane witness on the positive imaginary axis, and
those imaginary-axis values are already identified with the semigroup-side
holomorphic matrix element, then the kernel equality at `t = 0` follows.

This records the honest post-Paley-Wiener theorem surface: the ambient witness
coming from `SCV.paley_wiener_half_line` naturally lives on
`SCV.upperHalfPlane`, so the immediate consumer only needs its values at
`(t : ℂ) * I` rather than a prematurely rotated right-half-plane packaging. -/
private theorem kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_upperHalfPlaneWitness_on_imagAxis
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (H : ℂ → ℂ)
    (hH_imag_os :
      ∀ t : ℝ, 0 < t →
        H ((t : ℂ) * Complex.I) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ))
    (hlimit :
      ∀ t : ℝ, 0 < t →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    ↑(y k μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)) *
                (φ.conjTensorProduct ψ) y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (H ((t : ℂ) * Complex.I)))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  refine kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_osHolomorphicValue_on_positiveReals
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (hψ_compact := hψ_compact) ?_
  intro t ht
  simpa [hH_imag_os t ht] using hlimit t ht

/-- Concrete Section-4.3 / Lemma-4.2 adapter on the current honest theorem
surface: if an upper-half-plane witness already matches the semigroup-side
holomorphic matrix element on the positive imaginary axis, and the canonical
forward-cone `ξ`-shift shell converges to those same witness values for every
positive real time, then the reconstructed Wightman matrix element equals the
OS/Schwinger matrix element.

This theorem does not hide the remaining analytic work. Its hypotheses are
exactly the current Stage-5 blocker: the positive-imaginary-axis witness
identification and the shell-specific limit theorem. Once those are proved,
this theorem is the public consumer that delivers the per-pair kernel equality
needed later for Eq. `(4.28)` and positivity. -/
/-
Exact witness-constructor assembly note after the latest source audit:

- the first honest missing theorem strictly below the eventual right-half-plane
  witness `H` is the per-pair upper-half-plane scalar assembled from the
  Section-4.3 slice package;
- inspecting the proof body shows that `lemma42_matrix_element_time_interchange`
  itself is only a direct call to
  `kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_upperHalfPlaneWitness_on_imagAxis`,
  so its local use of the witness is exactly:
  1. the positive-imaginary-axis identification `hH_imag_os`, and
  2. the matching canonical-shell limit `hlimit`;
- in particular, no local holomorphy or identity-theorem argument remains
  below `lemma42`; those belong strictly upstream in the construction of the
  fixed-pair witness, not in `lemma42` itself;
- for fixed ambient/preimage data
  `hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩`
  and
  `hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩`,
  the exact first assembly statement is
  `∃ Hs : ℂ → ℂ,
      DifferentiableOn ℂ Hs SCV.upperHalfPlane ∧
      (∀ t : ℝ, 0 < t →
        Hs ((t : ℂ) * Complex.I) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ))`;
- this is exactly the `hH_imag_os` datum consumed by
  `lemma42_matrix_element_time_interchange`;
- the source bodies above show that this fixed-pair scalarization theorem
  should quantify only
  `OS`, `lgc`, `{n m}`, `φ`, `ψ`, `f`, `g`, `hf_ord`, `hg_ord`, `hφf`, and
  `hψg`: neither compact-support hypotheses nor the later shift index
  hypothesis `hm : 0 < m` appear in the actual slice-descending theorems or in
  the target `OSInnerProductTimeShiftHolomorphicValue`, so adding them here
  would be theorem-shape drift;
- the current theorems
  `partialFourierSpatial_timeSlice_hasPaleyWienerExtension`,
  `partialFourierSpatial_timeSliceCanonicalExtension`,
  `section43_iteratedSlice_descendedPairing`,
  `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`,
  and
  `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
  stop one level earlier: they descend individual slice pairings indexed by
  `(r, t, ht, ξ, w)` but do not package those slice identities into a single
  holomorphic scalar `Hs` for the fixed pair `(φ, ψ)` / `(f, g)`;
- more sharply, no current theorem states the missing scalarization step that
  would freeze the slice parameters, combine the descended slice pairings into
  one complex-valued function of the single continuation variable, and identify
  that function on `((t : ℂ) * Complex.I)` with
  `OSInnerProductTimeShiftHolomorphicValue ...`;
- this also explains why the theorem should not be stated first on a smaller
  codomain-level Section-4.3 object: the actual downstream consumer still
  needs the ambient representatives `φ, ψ` for the canonical-shell limit and
  the positive-time preimages `f, g` for the semigroup-side target, so a
  codomain-only statement here would only hide essential data behind a wrapper;
- only after such an `Hs` is assembled can one rotate it to the right-half-
  plane witness used by
  `one_variable_time_interchange_for_wightman_pairing`,
  for example by setting `H z := Hs (z * Complex.I)` and then proving the
  positive-real shell and Wightman-value formulas consumed there.
-/
theorem lemma42_matrix_element_time_interchange
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (H : ℂ → ℂ)
    (hH_imag_os :
      ∀ t : ℝ, 0 < t →
        H ((t : ℂ) * Complex.I) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ))
    (hlimit :
      ∀ t : ℝ, 0 < t →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    ↑(y k μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)) *
                (φ.conjTensorProduct ψ) y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (H ((t : ℂ) * Complex.I)))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  exact
    kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_upperHalfPlaneWitness_on_imagAxis
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (f := f)
      (hf_ord := hf_ord) (hf_compact := hf_compact)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
      (hψ_compact := hψ_compact) (H := H) hH_imag_os hlimit

/-- Route `3b-II` uniqueness assembly: once the real-time Wightman pairing
functional and the semigroup-side spectral boundary-value functional agree on
Fourier transforms of Schwartz tests, the explicit canonical Wightman witness
and the rotated OS holomorphic matrix element agree on the entire upper
half-plane.

This does not hide the remaining mathematics. The only live hypothesis is the
boundary-value identity itself; the rest is now a checked one-variable
distributional uniqueness argument. -/
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_rotated_OS_of_boundaryValue_fourierTransform_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hBV :
      let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
      let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
      ∀ χ : SchwartzMap ℝ ℂ,
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) t =
          selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG χ) :
    Set.EqOn
      (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact)
      (fun w =>
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord)
          (-Complex.I * w))
      SCV.upperHalfPlane := by
  let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
  have hBV' :
      ∀ χ : SchwartzMap ℝ ℂ,
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) t =
          selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG χ := by
    simpa [xF, xG] using hBV
  let HΔ : ℂ → ℂ := fun w =>
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact w -
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (-Complex.I * w)
  let C : Set (Fin 1 → ℝ) := {y | 0 < y 0}
  let G : (Fin 1 → ℂ) → ℂ := fun z => HΔ (z 0)
  let eR : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  let eM : ℝ ≃ᵐ (Fin 1 → ℝ) := eR.symm.toHomeomorph.toMeasurableEquiv
  have hmp_eM : MeasureTheory.MeasurePreserving eM MeasureTheory.volume MeasureTheory.volume := by
    simpa [eM, eR] using (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm
  have hHΔ_diff : DifferentiableOn ℂ HΔ SCV.upperHalfPlane := by
    exact
      (bvt_W_conjTensorProduct_timeShiftCanonicalExtension_differentiableOn
        (d := d) (OS := OS) (lgc := lgc) f g hg_compact).sub
      (differentiableOn_rotated_OSInnerProductTimeShiftHolomorphicValue
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord))
  have hHΔ_growth :
      ∀ η : ℝ, 0 < η →
        SCV.HasPolynomialGrowthOnLine (fun x => HΔ (↑x + ↑η * Complex.I)) := by
    intro η hη
    obtain ⟨C₁, N₁, hC₁, hbound₁⟩ :=
      hasPolynomialGrowthOnLine_bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) (OS := OS) (lgc := lgc) f g hg_compact η hη
    obtain ⟨C₂, N₂, hC₂, hbound₂⟩ :=
      hasPolynomialGrowthOnLine_rotated_OSInnerProductTimeShiftHolomorphicValue
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) η hη
    refine ⟨C₁ + C₂, max N₁ N₂, add_pos hC₁ hC₂, fun x => ?_⟩
    have hbase_ge_one : 1 ≤ 1 + |x| := by
      nlinarith [abs_nonneg x]
    have hpow₁ :
        (1 + |x|) ^ N₁ ≤ (1 + |x|) ^ max N₁ N₂ := by
      exact pow_le_pow_right₀ hbase_ge_one (Nat.le_max_left _ _)
    have hpow₂ :
        (1 + |x|) ^ N₂ ≤ (1 + |x|) ^ max N₁ N₂ := by
      exact pow_le_pow_right₀ hbase_ge_one (Nat.le_max_right _ _)
    calc
      ‖HΔ (↑x + ↑η * Complex.I)‖
          ≤
        ‖bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc f g hg_compact (↑x + ↑η * Complex.I)‖ +
          ‖OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single m g hg_ord)
              (-Complex.I * (↑x + ↑η * Complex.I))‖ := by
              simp [HΔ]
              exact norm_sub_le _ _
      _ ≤ C₁ * (1 + |x|) ^ N₁ + C₂ * (1 + |x|) ^ N₂ := by
            exact add_le_add (hbound₁ x) (hbound₂ x)
      _ ≤ C₁ * (1 + |x|) ^ max N₁ N₂ + C₂ * (1 + |x|) ^ max N₁ N₂ := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hpow₁ (le_of_lt hC₁))
              (mul_le_mul_of_nonneg_left hpow₂ (le_of_lt hC₂))
      _ = (C₁ + C₂) * (1 + |x|) ^ max N₁ N₂ := by ring
  have hC_open : IsOpen C := by
    simpa [C] using isOpen_lt continuous_const (continuous_apply 0)
  have hC_conv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    dsimp [C] at hx hy ⊢
    change 0 < a * x 0 + b * y 0
    have hab_pos : 0 < a ∨ 0 < b := by
      by_cases ha0 : a = 0
      · right
        linarith
      · left
        exact lt_of_le_of_ne ha (Ne.symm ha0)
    cases hab_pos with
    | inl ha_pos =>
        exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx) (mul_nonneg hb (le_of_lt hy))
    | inr hb_pos =>
        exact add_pos_of_nonneg_of_pos (mul_nonneg ha (le_of_lt hx)) (mul_pos hb_pos hy)
  have hC_ne : C.Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    simp [C]
  have hC_cone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C := by
    intro t ht y hy
    dsimp [C] at hy ⊢
    simpa [Pi.smul_apply, smul_eq_mul] using mul_pos ht hy
  have hG_diff : DifferentiableOn ℂ G (SCV.TubeDomain C) := by
    have hmap :
        Set.MapsTo (fun z : Fin 1 → ℂ => z 0) (SCV.TubeDomain C) SCV.upperHalfPlane := by
      intro z hz
      simpa [C, SCV.TubeDomain, SCV.upperHalfPlane] using hz
    have hproj_diff :
        DifferentiableOn ℂ (fun z : Fin 1 → ℂ => z 0) (SCV.TubeDomain C) := by
      exact
        ((ContinuousLinearMap.differentiable
          (ContinuousLinearMap.proj (R := ℂ) (ι := Fin 1) (φ := fun _ => ℂ) 0)).differentiableOn)
    simpa [G] using hHΔ_diff.comp hproj_diff hmap
  have hG_int :
      ∀ y ∈ C, ∀ ψ : SchwartzMap (Fin 1 → ℝ) ℂ,
        MeasureTheory.Integrable
          (fun x : Fin 1 → ℝ =>
            G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * ψ x) := by
    intro y hy ψ
    let ψ₁ : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR.symm ψ
    let χ : SchwartzMap ℝ ℂ := FourierTransform.fourierInv ψ₁
    have hy0 : 0 < y 0 := hy
    have hInt_can :
        MeasureTheory.Integrable
          (fun t : ℝ =>
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc f g hg_compact (↑t + ↑(y 0) * Complex.I) *
            (SchwartzMap.fourierTransformCLM ℂ χ) t) := by
      exact
        integrable_mul_fourierTransform_of_bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc f g hg_compact χ hy0
    have hInt_os :
        MeasureTheory.Integrable
          (fun t : ℝ =>
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single m g hg_ord)
                (-Complex.I * ((t : ℂ) + y 0 * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) t) := by
      exact
        integrable_mul_fourierTransform_of_rotated_OSInnerProductTimeShiftHolomorphicValue
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) χ hy0
    have hInt₁ :
        MeasureTheory.Integrable
          (fun t : ℝ =>
            HΔ (↑t + ↑(y 0) * Complex.I) * (SchwartzMap.fourierTransformCLM ℂ χ) t) := by
      simpa [HΔ, sub_mul] using hInt_can.sub hInt_os
    have hInt₁' :
        MeasureTheory.Integrable
          (fun t : ℝ => HΔ (↑t + ↑(y 0) * Complex.I) * ψ₁ t) := by
      simpa [χ] using hInt₁
    let g₁ : (Fin 1 → ℝ) → ℂ := fun x =>
      G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * ψ x
    have hcomp :
        MeasureTheory.Integrable (fun t : ℝ => g₁ (eR.symm t)) := by
      simpa [g₁, G, HΔ, ψ₁, eR] using hInt₁'
    have hiff := hmp_eM.integrable_comp_emb eM.measurableEmbedding (g := g₁)
    exact hiff.1 hcomp
  have hG_bv_zero :
      ∀ (ψ : SchwartzMap (Fin 1 → ℝ) ℂ) (η : Fin 1 → ℝ), η ∈ C →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ x : Fin 1 → ℝ,
              G (fun i => (x i : ℂ) + ε * (η i : ℂ) * Complex.I) * ψ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0) := by
    intro ψ η hη
    let ψ₁ : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR.symm ψ
    let χ : SchwartzMap ℝ ℂ := FourierTransform.fourierInv ψ₁
    have hη0 : 0 < η 0 := hη
    have hbase_can :
        Filter.Tendsto
          (fun s : ℝ =>
            ∫ t : ℝ,
              bvt_W_conjTensorProduct_timeShiftCanonicalExtension
                (d := d) OS lgc f g hg_compact (↑t + ↑s * Complex.I) * ψ₁ t)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (∫ t : ℝ,
              bvt_W OS lgc (n + m)
                (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * ψ₁ t)) := by
      simpa using
        (tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_boundaryValue
          (d := d) (OS := OS) (lgc := lgc) hm f g hg_compact ψ₁)
    have hbase_os :
        Filter.Tendsto
          (fun s : ℝ =>
            ∫ t : ℝ,
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n f hf_ord)
                  (PositiveTimeBorchersSequence.single m g hg_ord)
                  (-Complex.I * ((t : ℂ) + s * Complex.I)) * ψ₁ t)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (selfAdjointSpectralBoundaryValueOffdiag
              (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
              (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
              xF xG χ)) := by
      simpa [χ, xF, xG] using
        (tendsto_rotated_OSInnerProductTimeShiftHolomorphicValue_boundaryValue_fourierTransform
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) χ)
    have hbase :
        Filter.Tendsto
          (fun s : ℝ =>
            ∫ t : ℝ, HΔ (↑t + ↑s * Complex.I) * ψ₁ t)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0) := by
      have hsub := hbase_can.sub hbase_os
      have hEq :
          (fun s : ℝ =>
            (∫ t : ℝ,
              bvt_W_conjTensorProduct_timeShiftCanonicalExtension
                (d := d) OS lgc f g hg_compact (↑t + ↑s * Complex.I) * ψ₁ t) -
              ∫ t : ℝ,
                OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n f hf_ord)
                    (PositiveTimeBorchersSequence.single m g hg_ord)
                    (-Complex.I * ((t : ℂ) + s * Complex.I)) * ψ₁ t) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          (fun s : ℝ =>
            ∫ t : ℝ, HΔ (↑t + ↑s * Complex.I) * ψ₁ t) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hInt_can_s :
            MeasureTheory.Integrable
              (fun t : ℝ =>
                bvt_W_conjTensorProduct_timeShiftCanonicalExtension
                  (d := d) OS lgc f g hg_compact (↑t + ↑s * Complex.I) * ψ₁ t) := by
          simpa [χ] using
            (integrable_mul_fourierTransform_of_bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc f g hg_compact χ hs)
        have hInt_os_s :
            MeasureTheory.Integrable
              (fun t : ℝ =>
                OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n f hf_ord)
                    (PositiveTimeBorchersSequence.single m g hg_ord)
                    (-Complex.I * ((t : ℂ) + s * Complex.I)) * ψ₁ t) := by
          simpa [χ] using
            (integrable_mul_fourierTransform_of_rotated_OSInnerProductTimeShiftHolomorphicValue
              (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single m g hg_ord) χ hs)
        rw [← MeasureTheory.integral_sub hInt_can_s hInt_os_s]
        simp [HΔ, sub_mul]
      have htarget :
          (∫ t : ℝ,
            bvt_W OS lgc (n + m)
              (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * ψ₁ t) -
            selfAdjointSpectralBoundaryValueOffdiag
              (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
              (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
              xF xG χ = 0 := by
        have hBVχ :
            ∫ t : ℝ,
              bvt_W OS lgc (n + m)
                (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * ψ₁ t =
              selfAdjointSpectralBoundaryValueOffdiag
                (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
                (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
                xF xG χ := by
          simpa [χ] using hBV' χ
        rw [hBVχ]
        simp
      have hsub0 :
          Filter.Tendsto
            (fun s : ℝ =>
              (∫ t : ℝ,
                bvt_W_conjTensorProduct_timeShiftCanonicalExtension
                  (d := d) OS lgc f g hg_compact (↑t + ↑s * Complex.I) * ψ₁ t) -
                ∫ t : ℝ,
                  OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                      (PositiveTimeBorchersSequence.single n f hf_ord)
                      (PositiveTimeBorchersSequence.single m g hg_ord)
                      (-Complex.I * ((t : ℂ) + s * Complex.I)) * ψ₁ t)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds 0) := by
        simpa [htarget] using hsub
      exact hsub0.congr' hEq
    have hscale :
        Filter.Tendsto
          (fun ε : ℝ => ε * η 0)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_iff.mpr ?_
      constructor
      · have hcontWithin :
            ContinuousWithinAt (fun ε : ℝ => ε * η 0) (Set.Ioi 0) 0 := by
          exact (continuous_id.mul continuous_const).continuousAt.continuousWithinAt
        simpa using hcontWithin.tendsto
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simpa using mul_pos hε hη0
    have hscaled :
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ t : ℝ, HΔ (↑t + ↑(ε * η 0) * Complex.I) * ψ₁ t)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0) := hbase.comp hscale
    have hEq :
        (fun ε : ℝ =>
          ∫ x : Fin 1 → ℝ,
            G (fun i => (x i : ℂ) + ε * (η i : ℂ) * Complex.I) * ψ x) =
        (fun ε : ℝ =>
          ∫ t : ℝ,
            HΔ (↑t + ↑(ε * η 0) * Complex.I) * ψ₁ t) := by
      funext ε
      let g₁ : (Fin 1 → ℝ) → ℂ := fun x =>
        G (fun i => (x i : ℂ) + ε * (η i : ℂ) * Complex.I) * ψ x
      have hcov :
          ∫ t : ℝ, g₁ (eM t) = ∫ x : Fin 1 → ℝ, g₁ x := by
        simpa [eM] using (hmp_eM.integral_comp' (g := g₁))
      simpa [g₁, G, HΔ, ψ₁, eR, mul_assoc, mul_left_comm, mul_comm] using hcov.symm
    simpa [hEq] using hscaled
  have hzero := SCV.distributional_uniqueness_tube_of_zero_bv
    hC_open hC_conv hC_ne hC_cone hG_diff hG_int hG_bv_zero
  intro w hw
  have hw_tube : (fun _ => w) ∈ SCV.TubeDomain C := by
    simpa [C, SCV.TubeDomain] using hw
  have hzero_w := hzero (fun _ => w) hw_tube
  exact sub_eq_zero.mp (by simpa [G, HΔ] using hzero_w)

/-- Wightman-side Section-4.3 connection for the actual `ψ_{2πiη}` boundary
pairing: pairing the reconstructed real-time time-shift distribution against
`𝓕ψ_{2πiη}` is exactly the descended one-variable Section-4.3 Fourier pairing
of the canonical Wightman time-shift functional on the quotient class of
`ψ_{2πiη}`.

This is the direct flattened/time-shift functional surface needed before
comparing to the semigroup-side Section-4.3 scalar. -/
private theorem
    integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_fourierPairingDescendsToSection43PositiveEnergy1D
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    {η : ℝ} (hη : 0 < η) :
    ∫ t : ℝ,
      bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (η * Complex.I)))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) t =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc f g hg_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm f g hg_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (η * Complex.I)))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) := by
  let T : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    bvt_W_conjTensorProduct_timeShiftTemperedFunctional
      (d := d) OS lgc f g hg_compact
  let ψ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (η * Complex.I)))
      (by
        simpa [Complex.mul_im, hη.ne']
          using mul_pos Real.two_pi_pos hη)
  have hT_apply :
      T ((SchwartzMap.fourierTransformCLM ℂ) ψ) =
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ ψ) t := by
    simpa [T] using
      (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply
        (d := d) (OS := OS) (lgc := lgc) (f := f) (g := g)
        (hg_compact := hg_compact)
        ((SchwartzMap.fourierTransformCLM ℂ) ψ))
  have hDesc :
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          T
          (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
            (d := d) OS lgc hm f g hg_compact)
          (section43PositiveEnergyQuotientMap1D ψ) =
        T ((SchwartzMap.fourierTransformCLM ℂ) ψ) := by
    simpa [T, ψ] using
      (OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply
        (T := T)
        (hT_supp :=
          bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
            (d := d) OS lgc hm f g hg_compact)
        (f := ψ))
  calc
    ∫ t : ℝ,
      bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (η * Complex.I)))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) t
      = T ((SchwartzMap.fourierTransformCLM ℂ) ψ) := by
          simpa [ψ] using hT_apply.symm
    _ =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        T
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm f g hg_compact)
        (section43PositiveEnergyQuotientMap1D ψ) := hDesc.symm

/-- Wightman-side Section-4.3 connection on the actual Phase C' kernel: the
canonical ambient Stage-5 witness at `η i` is the descended one-variable
Section-4.3 Fourier pairing of the canonical Wightman time-shift functional on
the quotient class of `ψ_{2πiη}`.

This is the ambient counterpart of
`partialFourierSpatial_timeSliceCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ`:
both canonical witnesses now meet the same one-variable Section-4.3 codomain on
the same Paley-Wiener test family. -/
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    {η : ℝ} (hη : 0 < η) :
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact (η * Complex.I) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc f g hg_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm f g hg_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (η * Complex.I)))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) := by
  let T : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    bvt_W_conjTensorProduct_timeShiftTemperedFunctional
      (d := d) OS lgc f g hg_compact
  let ψ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (η * Complex.I)))
      (by
        simpa [Complex.mul_im, hη.ne']
          using mul_pos Real.two_pi_pos hη)
  have hCanonical :
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc f g hg_compact (η * Complex.I) =
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ ψ) t := by
    simpa [ψ] using
      (bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_fourierLaplaceIntegral
        (d := d) (OS := OS) (lgc := lgc) (f := f) (g := g)
        (hg_compact := hg_compact) hη)
  have hIntegral :
      ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ ψ) t =
        OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          T
          (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
            (d := d) OS lgc hm f g hg_compact)
          (section43PositiveEnergyQuotientMap1D ψ) := by
    simpa [T, ψ] using
      (integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_fourierPairingDescendsToSection43PositiveEnergy1D
        (d := d) (OS := OS) (lgc := lgc) (hm := hm) (f := f) (g := g)
        (hg_compact := hg_compact) hη)
  calc
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact (η * Complex.I)
      =
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ ψ) t := hCanonical
    _ =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        T
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm f g hg_compact)
        (section43PositiveEnergyQuotientMap1D ψ) := hIntegral


/-- Compact-support-free fixed-kernel consumer for the descended `ψ_{2πit}`
boundary-value comparison: once a one-variable witness `Tφψ` with one-sided
Fourier support is given, the only remaining input needed at this stage is the
transport-backed comparison on the single `ψ_{2πit}` family. -/
private theorem
    bvt_W_conjTensorProduct_timeShift_noCompact_psiZ_eq_osHolomorphicValue_of_ambient_descended_boundaryValue_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (Tφψ : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hTφψ_supp : SCV.HasOneSidedFourierSupport Tφψ)
    (hPsi :
      let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
      let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
      ∀ t : ℝ, ∀ ht : 0 < t,
        OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          Tφψ hTφψ_supp
          (section43PositiveEnergyQuotientMap1D
            (SCV.schwartzPsiZ
              (((2 * Real.pi : ℂ) * (t * Complex.I)))
              (by
                simpa [Complex.mul_im, ht.ne']
                  using mul_pos Real.two_pi_pos ht))) =
        selfAdjointSpectralBoundaryValueOffdiagCLM
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          xF xG
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) :
    ∀ t : ℝ, ∀ ht : 0 < t,
      Tφψ
        ((SchwartzMap.fourierTransformCLM ℂ)
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) := by
  intro t ht
  let ψZ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
  have hDesc :
      Tφψ ((SchwartzMap.fourierTransformCLM ℂ) ψZ) =
        OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          Tφψ hTφψ_supp (section43PositiveEnergyQuotientMap1D ψZ) := by
    simpa [ψZ] using
      (OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply
        (T := Tφψ) (hT_supp := hTφψ_supp) (f := ψZ)).symm
  have hPsi_t :
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        Tφψ hTφψ_supp (section43PositiveEnergyQuotientMap1D ψZ) =
      selfAdjointSpectralBoundaryValueOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        xF xG ψZ := by
    simpa [ψZ, xF, xG] using hPsi t ht
  have hOS :
      selfAdjointSpectralBoundaryValueOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          xF xG ψZ =
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) := by
    rw [selfAdjointSpectralBoundaryValueOffdiag_eq_selfAdjointSpectralLaplaceOffdiag_psiZ
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (x := xF) (y := xG) (ht := ht)]
    symm
    simpa [xF, xG] using
      (OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (t : ℂ) (by simpa using ht))
  calc
    Tφψ ((SchwartzMap.fourierTransformCLM ℂ) ψZ)
      =
        OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          Tφψ hTφψ_supp (section43PositiveEnergyQuotientMap1D ψZ) := hDesc
    _ =
        selfAdjointSpectralBoundaryValueOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          xF xG ψZ := hPsi_t
    _ =
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) := hOS

/-- Imaginary-axis corollary of the previous uniqueness assembly: once the
canonical Wightman boundary functional and the rotated OS spectral boundary
functional agree on Fourier transforms of Schwartz tests, the desired scalar
identity `canonical(t·I) = OS(t)` follows immediately. -/
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_boundaryValue_fourierTransform_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hBV :
      let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
      let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
      ∀ χ : SchwartzMap ℝ ℂ,
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) t =
          selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG χ) :
    ∀ t : ℝ, 0 < t →
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact ((t : ℂ) * Complex.I) =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) := by
  intro t ht
  have hEqOn :=
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_rotated_OS_of_boundaryValue_fourierTransform_eq
      (d := d) (OS := OS) (lgc := lgc) hm
      (f := f) (hf_ord := hf_ord)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact) hBV
  have ht_mem : ((t : ℂ) * Complex.I) ∈ SCV.upperHalfPlane := by
    simpa [SCV.upperHalfPlane] using ht
  have hEq := hEqOn ht_mem
  have hrot : -Complex.I * ((t : ℂ) * Complex.I) = (t : ℂ) := by
    ring_nf
    simp
  simpa [hrot] using hEq

/-- Route `3b-II` can be reduced one step further: if the explicit canonical
Wightman witness and the rotated OS holomorphic matrix element agree on the
positive imaginary axis, then their full one-variable boundary-value
functionals already agree on Fourier transforms of Schwartz tests.

This is a genuine blocker shrink, not a wrapper. The proof uses the
one-variable identity theorem to upgrade imag-axis equality to equality on the
entire upper half-plane, and then uniqueness of the boundary limit along
positive horizontal lines to identify the two boundary functionals. -/
private theorem
    bvt_W_conjTensorProduct_timeShift_boundaryValue_fourierTransform_eq_of_canonicalExtension_imag_eq_osHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hImag :
      ∀ t : ℝ, 0 < t →
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc f g hg_compact ((t : ℂ) * Complex.I) =
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ)) :
    ∀ χ : SchwartzMap ℝ ℂ,
      ∫ t : ℝ,
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) t =
      selfAdjointSpectralBoundaryValueOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
        χ := by
  let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
  have hEqUHP :
      ∀ z : ℂ, 0 < z.im →
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc f g hg_compact z =
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (-Complex.I * z) := by
    exact
      identity_theorem_upperHalfPlane
        (f := bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc f g hg_compact)
        (g := fun w =>
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord)
            (-Complex.I * w))
        (hf := bvt_W_conjTensorProduct_timeShiftCanonicalExtension_differentiableOn
          (d := d) (OS := OS) (lgc := lgc) f g hg_compact)
        (hg := differentiableOn_rotated_OSInnerProductTimeShiftHolomorphicValue
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord))
        (hagree := fun η hη => by
          have hrot : -Complex.I * ((η : ℂ) * Complex.I) = (η : ℂ) := by
            ring_nf
            simp
          simpa [hrot] using hImag η hη)
  have hEq :
      ∀ ψχ : SchwartzMap ℝ ℂ,
        (fun η : ℝ =>
          ∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc f g hg_compact (↑x + ↑η * Complex.I) *
              (SchwartzMap.fourierTransformCLM ℂ ψχ) x)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun η : ℝ =>
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single m g hg_ord)
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ ψχ) x) := by
    intro ψχ
    filter_upwards [self_mem_nhdsWithin] with η hη
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    have hw : 0 < ((x : ℂ) + η * Complex.I).im := by
      simpa using hη
    simpa [mul_assoc] using
      congrArg
        (fun z =>
          z * (SchwartzMap.fourierTransformCLM ℂ ψχ) x)
        (hEqUHP _ hw)
  intro ψχ
  have hCanonical :
      Filter.Tendsto
        (fun η : ℝ =>
          ∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc f g hg_compact (↑x + ↑η * Complex.I) *
              (SchwartzMap.fourierTransformCLM ℂ ψχ) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (∫ t : ℝ,
            bvt_W OS lgc (n + m)
              (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
              (SchwartzMap.fourierTransformCLM ℂ ψχ) t)) := by
    simpa using
      tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_boundaryValue
        (d := d) (OS := OS) (lgc := lgc) (hm := hm) f g hg_compact
        ((SchwartzMap.fourierTransformCLM ℂ) ψχ)
  have hOS :
      Filter.Tendsto
        (fun η : ℝ =>
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single m g hg_ord)
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ ψχ) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG ψχ)) := by
    simpa [xF, xG] using
      tendsto_rotated_OSInnerProductTimeShiftHolomorphicValue_boundaryValue_fourierTransform
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) ψχ
  have hCanonical' :
      Filter.Tendsto
        (fun η : ℝ =>
          ∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc f g hg_compact (↑x + ↑η * Complex.I) *
              (SchwartzMap.fourierTransformCLM ℂ ψχ) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG ψχ)) := by
    exact Filter.Tendsto.congr' (hEq ψχ).symm hOS
  exact tendsto_nhds_unique hCanonical hCanonical'

/-- Ambient/preimage boundary-value bridge for Phase C': if the canonical
upper-half-plane Wightman witness for ambient representatives `φ, ψ` agrees on
the positive imaginary axis with the semigroup-side OS matrix element built
from Euclidean preimages `f, g`, then the real-time Wightman boundary
functional of `φ, ψ` agrees with the OS spectral boundary functional of
`f, g` on Fourier transforms of Schwartz tests.

The proof is the same one-variable upper-half-plane identity plus uniqueness
of distributional boundary values used in the same-input bridge, but now on
the theorem surface required by the transformed-image positivity route. -/
private theorem
    bvt_W_conjTensorProduct_timeShift_boundaryValue_fourierTransform_eq_of_ambient_canonicalExtension_imag_eq_osHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hImag :
      ∀ t : ℝ, 0 < t →
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I) =
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ)) :
    ∀ χ : SchwartzMap ℝ ℂ,
      ∫ t : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) t =
      selfAdjointSpectralBoundaryValueOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
        χ := by
  let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
  have hEqUHP :
      ∀ z : ℂ, 0 < z.im →
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact z =
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (-Complex.I * z) := by
    exact
      identity_theorem_upperHalfPlane
        (f := bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact)
        (g := fun w =>
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord)
            (-Complex.I * w))
        (hf := bvt_W_conjTensorProduct_timeShiftCanonicalExtension_differentiableOn
          (d := d) (OS := OS) (lgc := lgc) φ ψ hψ_compact)
        (hg := differentiableOn_rotated_OSInnerProductTimeShiftHolomorphicValue
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord))
        (hagree := fun η hη => by
          have hrot : -Complex.I * ((η : ℂ) * Complex.I) = (η : ℂ) := by
            ring_nf
            simp
          simpa [hrot] using hImag η hη)
  have hEq :
      ∀ χ : SchwartzMap ℝ ℂ,
        (fun η : ℝ =>
          ∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact (↑x + ↑η * Complex.I) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun η : ℝ =>
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single m g hg_ord)
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x) := by
    intro χ
    filter_upwards [self_mem_nhdsWithin] with η hη
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    have hw : 0 < ((x : ℂ) + η * Complex.I).im := by
      simpa using hη
    simpa [mul_assoc] using
      congrArg
        (fun z =>
          z * (SchwartzMap.fourierTransformCLM ℂ χ) x)
        (hEqUHP _ hw)
  intro χ
  have hCanonical :
      Filter.Tendsto
        (fun η : ℝ =>
          ∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact (↑x + ↑η * Complex.I) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (∫ t : ℝ,
            bvt_W OS lgc (n + m)
              (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) *
              (SchwartzMap.fourierTransformCLM ℂ χ) t)) := by
    simpa using
      tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_boundaryValue
        (d := d) (OS := OS) (lgc := lgc) (hm := hm) φ ψ hψ_compact
        ((SchwartzMap.fourierTransformCLM ℂ) χ)
  have hOS :
      Filter.Tendsto
        (fun η : ℝ =>
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single m g hg_ord)
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG χ)) := by
    simpa [xF, xG] using
      tendsto_rotated_OSInnerProductTimeShiftHolomorphicValue_boundaryValue_fourierTransform
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) χ
  have hCanonical' :
      Filter.Tendsto
        (fun η : ℝ =>
          ∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact (↑x + ↑η * Complex.I) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG χ)) := by
    exact Filter.Tendsto.congr' (hEq χ).symm hOS
  exact tendsto_nhds_unique hCanonical hCanonical'

/-- One-dimensional horizontal Paley-Wiener kernel for the OS-route
shell-to-Laplace comparison. For any one-variable tempered functional `TW`,
the horizontal `x`-integral of `TW` applied to the Fourier-transformed
`ψ_{2π(x+εi)}` family is represented by pairing `TW` against a single
Schwartz test `χHorizontal`.

This is the genuine Fin1 Fubini packet used before applying the full flattened
time-shift theorem `exists_timeShiftKernel_pairing_fourierTest`. -/
private theorem exists_horizontalPaleyKernel_pairing_fourierTransform
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      TW χHorizontal =
        ∫ x : ℝ,
          TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
  classical
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
  let fromFin1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1.symm
  let T1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] ℂ := TW.comp fromFin1
  let f1 : SchwartzMap (Fin 1 → ℝ) ℂ :=
    toFin1 ((SchwartzMap.fourierTransformCLM ℂ) ψZt)
  let g1 : (Fin 1 → ℝ) → SchwartzMap (Fin 1 → ℝ) ℂ := fun x1 =>
    toFin1 ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε (e1 x1)))
  have hg1_cont : Continuous g1 := by
    simpa [g1, ψZxε, toFin1, e1] using
      (SCV.continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal hε)
  have hg1_bound :
      ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
        ∀ (x1 : Fin 1 → ℝ),
          SchwartzMap.seminorm ℝ k n (g1 x1) ≤ C * (1 + ‖x1‖) ^ N := by
    simpa [g1, ψZxε, toFin1, e1] using
      (SCV.seminorm_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal_growth hε)
  obtain ⟨χ1, hχ1_eval, hχ1_pair⟩ :=
    schwartz_clm_fubini_exchange T1 g1 f1 hg1_cont hg1_bound
  let χHorizontal : SchwartzMap ℝ ℂ := fromFin1 χ1
  let eM : ℝ ≃ᵐ (Fin 1 → ℝ) := e1.symm.toHomeomorph.toMeasurableEquiv
  have hmp_eM : MeasureTheory.MeasurePreserving eM MeasureTheory.volume MeasureTheory.volume := by
    simpa [eM, e1] using (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm
  have hfrom_to :
      ∀ φ : SchwartzMap ℝ ℂ, fromFin1 (toFin1 φ) = φ := by
    intro φ
    ext x
    simp [fromFin1, toFin1, e1, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  refine ⟨χHorizontal, ?_, ?_⟩
  · intro τ
    let G : (Fin 1 → ℝ) → ℂ := fun x1 => g1 x1 (e1.symm τ) * f1 x1
    have hcov :
        ∫ x : ℝ, G (eM x) = ∫ x1 : Fin 1 → ℝ, G x1 := by
      simpa [eM] using (hmp_eM.integral_comp' (g := G))
    calc
      χHorizontal τ
          = χ1 (e1.symm τ) := by
              simp [χHorizontal, fromFin1, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      _ = ∫ x1 : Fin 1 → ℝ, g1 x1 (e1.symm τ) * f1 x1 :=
            hχ1_eval (e1.symm τ)
      _ = ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
              rw [← hcov]
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp [G, g1, f1, ψZxε, ψZt, toFin1, eM, e1,
                SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  · let G : (Fin 1 → ℝ) → ℂ := fun x1 => T1 (g1 x1) * f1 x1
    have hcov :
        ∫ x : ℝ, G (eM x) = ∫ x1 : Fin 1 → ℝ, G x1 := by
      simpa [eM] using (hmp_eM.integral_comp' (g := G))
    calc
      TW χHorizontal
          = T1 χ1 := by
              rfl
      _ = ∫ x1 : Fin 1 → ℝ, T1 (g1 x1) * f1 x1 :=
            hχ1_pair
      _ = ∫ x : ℝ,
            TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
              rw [← hcov]
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp [G, T1, g1, f1, ψZxε, ψZt, hfrom_to, toFin1, fromFin1, eM, e1,
                SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

private theorem exists_horizontalPaleyKernel_universal_pairing
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      ∀ TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ,
        TW χHorizontal =
          ∫ x : ℝ,
            TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
  classical
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  obtain ⟨χHorizontal, hχ_eval, _hχ_pair_zero⟩ :=
    exists_horizontalPaleyKernel_pairing_fourierTransform
      (hε := hε) (ht := ht)
      (0 : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
  refine ⟨χHorizontal, ?_, ?_⟩
  · simpa [ψZxε, ψZt] using hχ_eval
  · intro TW
    obtain ⟨χTW, hχTW_eval, hχTW_pair⟩ :=
      exists_horizontalPaleyKernel_pairing_fourierTransform
        (hε := hε) (ht := ht) TW
    have hχTW_eq : χTW = χHorizontal := by
      ext τ
      calc
        χTW τ
            = ∫ x : ℝ,
                (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
                (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
                simpa [ψZxε, ψZt] using hχTW_eval τ
        _ = χHorizontal τ := by
                simpa [ψZxε, ψZt] using (hχ_eval τ).symm
    calc
      TW χHorizontal
          = TW χTW := by rw [hχTW_eq]
      _ = ∫ x : ℝ,
            TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            simpa [ψZxε, ψZt] using hχTW_pair

/-- The one-variable oscillatory phase used to probe the horizontal Paley
kernel at a fixed flattened frequency has temperate growth. -/
private theorem horizontalPhase_temperate (lam : ℝ) :
    (fun τ : ℝ =>
      Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ)))).HasTemperateGrowth := by
  let c : ℂ := -(Complex.I * (lam : ℂ))
  suffices htemp : (fun τ : ℝ => Complex.exp (c * (τ : ℂ))).HasTemperateGrowth by
    convert htemp using 1
    ext τ
    simp [c, mul_assoc]
  refine ⟨?_, ?_⟩
  · have hlin : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun τ : ℝ => c * (τ : ℂ)) := by
      simpa using (contDiff_const.mul Complex.ofRealCLM.contDiff)
    exact Complex.contDiff_exp.comp hlin
  · intro n
    refine ⟨0, ‖c ^ n‖, fun τ => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hiter := congr_fun (SCV.iteratedDeriv_cexp_const_mul_real n c) τ
    rw [hiter]
    have hre : (c * (τ : ℂ)).re = 0 := by
      simp [c, Complex.mul_re]
    calc
      ‖c ^ n * Complex.exp (c * (τ : ℂ))‖ = ‖c ^ n‖ := by
        rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one]
      _ ≤ ‖c ^ n‖ * (1 + ‖τ‖) ^ 0 := by simp

/-- Fixed-frequency one-variable functional for the horizontal Paley kernel.
It pairs a Schwartz test with the oscillatory phase carrying frequency `lam`,
then multiplies by the frozen full-flat base Fourier factor. -/
private noncomputable def horizontalPhasePairingCLM
    (base : ℂ) (lam : ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  base •
    ((SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)).comp
      (SchwartzMap.smulLeftCLM ℂ
        (fun τ : ℝ =>
          Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))))))

private theorem horizontalPhasePairingCLM_apply
    (base : ℂ) (lam : ℝ) (χ : SchwartzMap ℝ ℂ) :
    horizontalPhasePairingCLM base lam χ =
      base *
        ∫ τ : ℝ,
          Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) * χ τ := by
  simp [horizontalPhasePairingCLM, SchwartzMap.integralCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (horizontalPhase_temperate lam), smul_eq_mul]

private theorem horizontalPhasePairingCLM_fourierTransform
    (base : ℂ) (lam : ℝ) (χ : SchwartzMap ℝ ℂ) :
    horizontalPhasePairingCLM base lam
        ((SchwartzMap.fourierTransformCLM ℂ) χ) =
      base * χ (-lam / (2 * Real.pi)) := by
  rw [horizontalPhasePairingCLM_apply]
  rw [integral_phase_mul_fourierTransform_eq_eval]

/-- Fixed-frequency evaluation of the horizontal Paley kernel against the
oscillatory phase functional. This is the horizontal half of the finite-height
kernel comparison at a frozen flattened frequency. -/
private theorem exists_horizontalPaleyKernel_phasePairing
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (base : ℂ) (lam : ℝ) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      horizontalPhasePairingCLM base lam χHorizontal =
        ∫ x : ℝ,
          (base * (ψZxε x) (-lam / (2 * Real.pi))) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
  classical
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  obtain ⟨χHorizontal, hχ_eval, hχ_pair⟩ :=
    exists_horizontalPaleyKernel_universal_pairing (hε := hε) (ht := ht)
  refine ⟨χHorizontal, ?_, ?_⟩
  · simpa [ψZxε, ψZt] using hχ_eval
  · calc
      horizontalPhasePairingCLM base lam χHorizontal
          = ∫ x : ℝ,
              horizontalPhasePairingCLM base lam
                ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
              simpa [ψZxε, ψZt] using
                hχ_pair (horizontalPhasePairingCLM base lam)
      _ = ∫ x : ℝ,
            (base * (ψZxε x) (-lam / (2 * Real.pi))) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            rw [horizontalPhasePairingCLM_fourierTransform]

/-- Collapse the remaining one-variable horizontal Paley integral after
freezing the oscillatory frequency. The result keeps the one-sided cutoffs
explicit; they are removed later from the dual-cone inequality `lam ≤ 0`. -/
private theorem horizontalPaley_phase_xIntegral_eq
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (base : ℂ) (lam : ℝ) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∫ x : ℝ,
      (base * (ψZxε x) (-lam / (2 * Real.pi))) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x =
    base *
      ((SCV.smoothCutoff (-lam / (2 * Real.pi)) : ℂ) *
        Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
        ψZt (-lam / (2 * Real.pi))) := by
  classical
  let r : ℝ := -lam / (2 * Real.pi)
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  have hψ_inv :
      FourierTransform.fourierInv
          ((SchwartzMap.fourierTransformCLM ℂ) ψZt) = ψZt := by
    simpa [ψZt] using (FourierTransform.fourierInv_fourier_eq ψZt)
  have hpair :
      (∫ x : ℝ,
          (ψZxε x) r *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
        (SCV.smoothCutoff r : ℂ) *
          Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
          ψZt r := by
    calc
      (∫ x : ℝ,
          (ψZxε x) r *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          = ∫ x : ℝ,
              SCV.psiZ ((2 * Real.pi : ℂ) * (x + ε * Complex.I)) r *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp [ψZxε]
      _ = (SCV.smoothCutoff r : ℂ) *
            Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
            FourierTransform.fourierInv
              ((SchwartzMap.fourierTransformCLM ℂ) ψZt) r :=
            SCV.psiZ_twoPi_pairing_formula
              (φ := (SchwartzMap.fourierTransformCLM ℂ ψZt))
              (η := ε) (ξ := r)
      _ = (SCV.smoothCutoff r : ℂ) *
            Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
            ψZt r := by rw [hψ_inv]
  have hmain :
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
      base *
        ((SCV.smoothCutoff r : ℂ) *
          Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
          ψZt r) := by
    calc
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          = ∫ x : ℝ,
              base * ((ψZxε x) r *
                (SchwartzMap.fourierTransformCLM ℂ ψZt) x) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              ring
      _ = base *
            ∫ x : ℝ,
              (ψZxε x) r *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            simpa using
              (MeasureTheory.integral_const_mul
                (μ := MeasureTheory.volume) base
                (fun x : ℝ =>
                  (ψZxε x) r *
                  (SchwartzMap.fourierTransformCLM ℂ ψZt) x))
      _ = base *
            ((SCV.smoothCutoff r : ℂ) *
              Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
              ψZt r) := by rw [hpair]
  simpa [r, ψZxε, ψZt] using hmain

/-- Nonnegative-frequency form of `horizontalPaley_phase_xIntegral_eq`.
On the dual cone this applies because the tail time-shift direction pairs
nonpositively with every allowed frequency. -/
private theorem horizontalPaley_phase_xIntegral_eq_of_nonneg
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (base : ℂ) (lam : ℝ)
    (hr : 0 ≤ -lam / (2 * Real.pi)) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∫ x : ℝ,
      (base * (ψZxε x) (-lam / (2 * Real.pi))) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x =
    base *
      (Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
       Complex.exp (-(2 * Real.pi * t : ℂ) * (-lam / (2 * Real.pi)))) := by
  classical
  let r : ℝ := -lam / (2 * Real.pi)
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  have hr' : 0 ≤ r := by simpa [r] using hr
  have hcut : (SCV.smoothCutoff r : ℂ) = 1 := by
    exact_mod_cast SCV.smoothCutoff_one_of_nonneg hr'
  have hψt :
      ψZt r = Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ)) := by
    calc
      ψZt r
          = SCV.psiZ ((2 * Real.pi : ℂ) * (t * Complex.I)) r := by
              simp [ψZt]
      _ = Complex.exp
            (Complex.I * ((2 * Real.pi : ℂ) * (t * Complex.I)) * (r : ℂ)) := by
            rw [SCV.psiZ_eq_exp_of_nonneg hr']
      _ = Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ)) := by
            congr 1
            calc
              Complex.I * ((2 * Real.pi : ℂ) * (t * Complex.I)) * (r : ℂ)
                  = (Complex.I * Complex.I) *
                      ((2 * Real.pi * t : ℂ) * (r : ℂ)) := by ring
              _ = -(2 * Real.pi * t : ℂ) * (r : ℂ) := by
                    simp [Complex.I_mul_I]
  have hcollapse :=
    horizontalPaley_phase_xIntegral_eq (hε := hε) (ht := ht)
      (base := base) (lam := lam)
  have hmain :
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
      base *
        (Complex.exp (-(2 * Real.pi * ε : ℂ) * (r : ℂ)) *
         Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ))) := by
    calc
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          = base *
              ((SCV.smoothCutoff r : ℂ) *
                Complex.exp (-(2 * Real.pi * ε : ℂ) * (r : ℂ)) *
                ψZt r) := by
              simpa [r, ψZxε, ψZt] using hcollapse
      _ = base *
            (Complex.exp (-(2 * Real.pi * ε : ℂ) * (r : ℂ)) *
             Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ))) := by
            rw [hcut, hψt]
            ring
  simpa [r, ψZxε, ψZt] using hmain

/-- The frozen horizontal frequency `r = -lam/(2π)` is nonnegative on the
dual cone. This is exactly the sign input needed to remove the one-sided
Paley-Wiener cutoffs from the horizontal scalar. -/
private theorem horizontalPaley_frequency_nonneg_of_mem_dualCone
    {n m : ℕ}
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ : ξ ∈ DualConeFlat
      ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    0 ≤ -(∑ i,
      (((OSReconstruction.castFinCLE
          (Nat.add_mul n m (d + 1)).symm)
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTimeShiftDirection d m))) i) * ξ i) / (2 * Real.pi) := by
  have hlam :=
    zeroHeadBlockShift_flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone
      (d := d) (n := n) (m := m) (ξ := ξ) hξ
  have hden_nonneg : 0 ≤ 2 * Real.pi := Real.two_pi_pos.le
  refine div_nonneg ?_ hden_nonneg
  exact neg_nonneg.mpr (by simpa using hlam)

/-- Pointwise horizontal kernel scalar on the dual cone. This is the full
horizontal-side finite-height computation: the `τ`-kernel formula collapses to
the explicit Paley-Wiener damping scalar at each dual-cone frequency. -/
private theorem horizontalKernel_pointwise_eq_exp_of_mem_dualCone
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (χHorizontal : SchwartzMap ℝ ℂ)
    (KHorizontal : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ)
    (hχ_eval :
      ∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
                (by
                  have hscaled : 0 < (2 * Real.pi) *
                      (((x : ℂ) + ε * Complex.I).im) :=
                    mul_pos Real.two_pi_pos (by simpa using hε)
                  simpa [Complex.mul_im] using hscaled))) τ *
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                (((2 * Real.pi : ℂ) * (t * Complex.I)))
                (by
                  simpa [Complex.mul_im, ht.ne']
                    using mul_pos Real.two_pi_pos ht))) x)
    (hK_eval :
      ∀ ξ : Fin ((n + m) * (d + 1)) → ℝ,
        KHorizontal ξ =
          ∫ τ : ℝ,
            timeShiftFlatOrbit (d := d) φ ψ τ ξ * χHorizontal τ)
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ : ξ ∈ DualConeFlat
      ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    let base : ℂ :=
      physicsFourierFlatCLM
        (OSReconstruction.reindexSchwartzFin
          (Nat.add_mul n m (d + 1)).symm
          (((_root_.flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
            (_root_.flattenSchwartzNPoint (d := d) ψ)))) ξ
    let lam : ℝ :=
      ∑ i,
        (((OSReconstruction.castFinCLE
            (Nat.add_mul n m (d + 1)).symm)
          (OSReconstruction.zeroHeadBlockShift
            (m := n * (d + 1)) (n := m * (d + 1))
            (flatTimeShiftDirection d m))) i) * ξ i
    KHorizontal ξ =
      base *
        (Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
         Complex.exp (-(2 * Real.pi * t : ℂ) * (-lam / (2 * Real.pi)))) := by
  classical
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  let base : ℂ :=
    physicsFourierFlatCLM
      (OSReconstruction.reindexSchwartzFin
        (Nat.add_mul n m (d + 1)).symm
        (((_root_.flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
          (_root_.flattenSchwartzNPoint (d := d) ψ)))) ξ
  let lam : ℝ :=
    ∑ i,
      (((OSReconstruction.castFinCLE
          (Nat.add_mul n m (d + 1)).symm)
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTimeShiftDirection d m))) i) * ξ i
  have hχ_eval_local :
      ∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
    intro τ
    simpa [ψZxε, ψZt] using hχ_eval τ
  have hK_phase :
      KHorizontal ξ = horizontalPhasePairingCLM base lam χHorizontal := by
    calc
      KHorizontal ξ
          = ∫ τ : ℝ,
              timeShiftFlatOrbit (d := d) φ ψ τ ξ * χHorizontal τ :=
            hK_eval ξ
      _ = ∫ τ : ℝ,
            base *
              (Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) *
                χHorizontal τ) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with τ
            rw [timeShiftFlatOrbit_apply_phase]
            dsimp only [base, lam]
            ring
      _ = base *
            ∫ τ : ℝ,
              Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) *
                χHorizontal τ := by
            simpa using
              (MeasureTheory.integral_const_mul
                (μ := MeasureTheory.volume) base
                (fun τ : ℝ =>
                  Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) *
                    χHorizontal τ))
      _ = horizontalPhasePairingCLM base lam χHorizontal :=
            (horizontalPhasePairingCLM_apply base lam χHorizontal).symm
  obtain ⟨χPhase, hχPhase_eval, hχPhase_pair⟩ :=
    exists_horizontalPaleyKernel_phasePairing
      (hε := hε) (ht := ht) (base := base) (lam := lam)
  have hχPhase_eval_local :
      ∀ τ : ℝ,
        χPhase τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
    intro τ
    simpa [ψZxε, ψZt] using hχPhase_eval τ
  have hχ_eq : χHorizontal = χPhase := by
    ext τ
    rw [hχ_eval_local τ, hχPhase_eval_local τ]
  have hr :
      0 ≤ -lam / (2 * Real.pi) := by
    simpa [lam] using
      (horizontalPaley_frequency_nonneg_of_mem_dualCone
        (d := d) (n := n) (m := m) (ξ := ξ) hξ)
  have hfinal :
      KHorizontal ξ =
        base *
          (Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
           Complex.exp (-(2 * Real.pi * t : ℂ) * (-lam / (2 * Real.pi)))) := by
    calc
      KHorizontal ξ
          = horizontalPhasePairingCLM base lam χHorizontal := hK_phase
      _ = horizontalPhasePairingCLM base lam χPhase := by rw [hχ_eq]
      _ = ∫ x : ℝ,
            (base * (ψZxε x) (-lam / (2 * Real.pi))) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            simpa [ψZxε, ψZt] using hχPhase_pair
      _ = base *
            (Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
             Complex.exp (-(2 * Real.pi * t : ℂ) * (-lam / (2 * Real.pi)))) := by
            simpa [ψZxε, ψZt] using
              (horizontalPaley_phase_xIntegral_eq_of_nonneg
                (hε := hε) (ht := ht) (base := base) (lam := lam) hr)
  simpa [base, lam] using hfinal

/-- Pointwise normal form for the explicit canonical Wightman witness on a
positive horizontal line: after unfolding `fourierLaplaceExt`, its value at
`x + η i` is the real-time Wightman time-shift tempered functional applied to
the Fourier transform of the Paley-Wiener kernel
`ψ_{2π(x+η i)}`.

This is a proof-local algebraic step toward the shell-to-Laplace comparison:
it exposes the inner Wightman time-shift integral that will later be related
to the explicit canonical `ξ`-shift shell. -/
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_fourierLaplaceIntegral
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {η : ℝ} (hη : 0 < η) (x : ℝ) :
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + η * Complex.I) =
      ∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((x : ℂ) + η * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hη)
              simpa [Complex.mul_im] using hscaled))) τ := by
  have hw : 0 < (((x : ℂ) + η * Complex.I).im) := by
    simpa using hη
  rw [bvt_W_conjTensorProduct_timeShiftCanonicalExtension, dif_pos hw]
  rw [SCV.fourierLaplaceExt_eq]
  change
    bvt_W_conjTensorProduct_timeShiftTemperedFunctional
        (d := d) OS lgc φ ψ hψ_compact
      ((SchwartzMap.fourierTransformCLM ℂ)
        (SCV.schwartzPsiZ
          ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
          (by
            have hscaled : 0 < (2 * Real.pi) *
                (((x : ℂ) + η * Complex.I).im) :=
              mul_pos Real.two_pi_pos (by simpa using hη)
            simpa [Complex.mul_im] using hscaled))) =
      ∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((x : ℂ) + η * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hη)
              simpa [Complex.mul_im] using hscaled))) τ
  exact
    bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply
      (d := d) (OS := OS) (lgc := lgc) (f := φ) (g := ψ)
      (hg_compact := hψ_compact)
      ((SchwartzMap.fourierTransformCLM ℂ)
        (SCV.schwartzPsiZ
          ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
          (by
            have hscaled : 0 < (2 * Real.pi) *
                (((x : ℂ) + η * Complex.I).im) :=
              mul_pos Real.two_pi_pos (by simpa using hη)
            simpa [Complex.mul_im] using hscaled)))

/-- Horizontal full-flat `Tflat` kernel packet. For finite positive height
`ε` and positive imaginary-axis target `t`, the canonical horizontal
Fourier-Laplace scalar is represented by the same full flattened distribution
`Tflat` as a single kernel `KHorizontal`.

The proof first constructs the one-dimensional Paley-Wiener test
`χHorizontal`, then feeds it into
`exists_timeShiftKernel_pairing_fourierTest`. -/
private theorem exists_horizontalKernel_pairing_iteratedFourierLaplace
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + m) (_root_.unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      ∃ KHorizontal : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        (∀ ξ : Fin ((n + m) * (d + 1)) → ℝ,
          KHorizontal ξ =
            ∫ τ : ℝ,
              timeShiftFlatOrbit (d := d) φ ψ τ ξ * χHorizontal τ) ∧
        (∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + ε * Complex.I) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
          Tflat KHorizontal := by
  classical
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  let TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    bvt_W_conjTensorProduct_timeShiftTemperedFunctional
      (d := d) OS lgc φ ψ hψ_compact
  obtain ⟨χHorizontal, hχ_eval, hχ_pairTW⟩ :=
    exists_horizontalPaleyKernel_pairing_fourierTransform
      (hε := hε) (ht := ht) TW
  obtain ⟨KHorizontal, hK_eval, hK_pair⟩ :=
    exists_timeShiftKernel_pairing_fourierTest
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (χ := χHorizontal)
      (Tflat := Tflat) hTflat_bv
  have hTW_point :
      ∀ x : ℝ,
        TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) =
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + ε * Complex.I) := by
    intro x
    calc
      TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x))
          =
        ∫ τ : ℝ,
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ := by
            simpa [TW] using
              (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply
                (d := d) (OS := OS) (lgc := lgc)
                (f := φ) (g := ψ) (hg_compact := hψ_compact)
                ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)))
      _ =
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + ε * Complex.I) := by
            simpa [ψZxε] using
              (bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_fourierLaplaceIntegral
                (d := d) (OS := OS) (lgc := lgc)
                (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) hε x).symm
  have hTWχ_apply :
      TW χHorizontal =
        ∫ τ : ℝ,
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          χHorizontal τ := by
    simpa [TW] using
      (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply
        (d := d) (OS := OS) (lgc := lgc)
        (f := φ) (g := ψ) (hg_compact := hψ_compact) χHorizontal)
  refine ⟨χHorizontal, ?_, KHorizontal, hK_eval, ?_⟩
  · simpa [ψZxε, ψZt] using hχ_eval
  · calc
      (∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + ε * Complex.I) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          =
        ∫ x : ℝ,
          TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            rw [hTW_point x]
      _ = TW χHorizontal := by
            simpa [ψZxε, ψZt] using hχ_pairTW.symm
      _ =
        ∫ τ : ℝ,
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          χHorizontal τ := hTWχ_apply
      _ = Tflat KHorizontal := hK_pair

/-- Outer-integral normal form for the canonical horizontal Fourier-Laplace
pairing. For fixed `t > 0`, the horizontal integral of the canonical witness
against `𝓕ψ_{2πit}` can be rewritten as an iterated real-time Wightman
time-shift integral whose inner Paley-Wiener kernel is `ψ_{2π(x+ηi)}`.

This does not perform the Fubini/Fourier-inversion step. It is the exact
normal form that the next shell-to-Laplace proof has to analyze. -/
private theorem
    integral_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_iterated_fourierLaplaceIntegral
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    (∫ x : ℝ,
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + η * Complex.I) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) x)
      =
    ∫ x : ℝ,
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((x : ℂ) + η * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hη)
              simpa [Complex.mul_im] using hscaled))) τ) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) x := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  have hpt :=
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_fourierLaplaceIntegral
      (d := d) (OS := OS) (lgc := lgc)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) hη x
  exact
    congrArg
      (fun z =>
        z *
          (SchwartzMap.fourierTransformCLM ℂ
            (SCV.schwartzPsiZ
              (((2 * Real.pi : ℂ) * (t * Complex.I)))
              (by
                simpa [Complex.mul_im, ht.ne']
                  using mul_pos Real.two_pi_pos ht))) x)
      hpt

/-- Pointwise shell-minus-horizontal normal form for the shell-to-Laplace seam.
After the previous lemma rewrites the canonical horizontal witness as an
iterated real-time Wightman integral, the remaining comparison is exactly the
difference between the explicit canonical `bvt_F` `ξ`-shell and that iterated
integral.

This is deliberately not a new end-stage conditional wrapper: it is the local
algebraic rewrite that exposes the next Fubini/Fourier-inversion target. -/
private theorem
    bvt_F_canonical_xiShift_shell_sub_horizontal_eq_shell_sub_iterated_fourierLaplaceIntegral
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) -
      (∫ x : ℝ,
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + ε * Complex.I) *
          (SchwartzMap.fourierTransformCLM ℂ
            (SCV.schwartzPsiZ
              (((2 * Real.pi : ℂ) * (t * Complex.I)))
              (by
                simpa [Complex.mul_im, ht.ne']
                  using mul_pos Real.two_pi_pos ht))) x) =
    (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) -
      (∫ x : ℝ,
        (∫ τ : ℝ,
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ
            (SCV.schwartzPsiZ
              ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
              (by
                have hscaled : 0 < (2 * Real.pi) *
                    (((x : ℂ) + ε * Complex.I).im) :=
                  mul_pos Real.two_pi_pos (by simpa using hε)
                simpa [Complex.mul_im] using hscaled))) τ) *
          (SchwartzMap.fourierTransformCLM ℂ
            (SCV.schwartzPsiZ
              (((2 * Real.pi : ℂ) * (t * Complex.I)))
              (by
                simpa [Complex.mul_im, ht.ne']
                  using mul_pos Real.two_pi_pos ht))) x) := by
  rw [integral_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_iterated_fourierLaplaceIntegral
    (d := d) (OS := OS) (lgc := lgc)
    (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) ht hε]

/-- The shell-minus-horizontal comparison has an unconditional residual limit:
the explicit `bvt_F` `ξ`-shell tends to the real-time shifted Wightman pairing,
while the canonical horizontal Fourier-Laplace integral tends to the canonical
witness value at `t i`. Thus their difference tends to the difference of those
two scalar targets.

This computes the exact scalar obstruction behind the shell-to-Laplace seam. -/
private theorem
    tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_timeShift_sub_canonicalExtension
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t : ℝ} (ht : 0 < t) :
    let ψZ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y) -
        (∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) -
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I))) := by
  let ψZ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  let shell : ℝ → ℂ := fun ε =>
    ∫ y : NPointDomain d (n + m),
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
        (φ.conjTensorProduct ψ) y
  let horizontal : ℝ → ℂ := fun ε =>
    ∫ x : ℝ,
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
      (SchwartzMap.fourierTransformCLM ℂ ψZ) x
  have hShell :
      Filter.Tendsto shell
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)))) := by
    simpa [shell] using
      (tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue
        (d := d) (OS := OS) (lgc := lgc) (hm := hm)
        (φ := φ) (ψ := ψ) (t := t))
  have hHorizontal :
      Filter.Tendsto horizontal
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I))) := by
    simpa [horizontal, ψZ] using
      (tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_to_imagAxis
        (d := d) (OS := OS) (lgc := lgc) (hm := hm)
        (f := φ) (g := ψ) (hg_compact := hψ_compact) ht)
  simpa [shell, horizontal, ψZ] using hShell.sub hHorizontal

/-- Eventual guarded normal form for the actual shell-minus-horizontal limit
function. On the punctured positive neighbourhood used by the boundary-value
filter, the horizontal canonical witness can be replaced by the explicit
iterated real-time Fourier-Laplace integral.

The `if hε : 0 < ε` guard only makes the right-hand side a total function of
`ε`; it disappears under `nhdsWithin 0 (Set.Ioi 0)`. -/
private theorem
    bvt_F_canonical_xiShift_shell_sub_horizontal_eventually_eq_shell_sub_iterated_fourierLaplaceIntegral
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t : ℝ} (ht : 0 < t) :
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    (fun ε : ℝ =>
      (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) -
      (∫ x : ℝ,
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x))
    =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
    (fun ε : ℝ =>
      (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) -
      if hε : 0 < ε then
        ∫ x : ℝ,
          (∫ τ : ℝ,
            bvt_W OS lgc (n + m)
              (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
                (by
                  have hscaled : 0 < (2 * Real.pi) *
                      (((x : ℂ) + ε * Complex.I).im) :=
                    mul_pos Real.two_pi_pos (by simpa using hε)
                  simpa [Complex.mul_im] using hscaled))) τ) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x
      else
        0) := by
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  rw [dif_pos hεpos]
  simpa [ψZt] using
    bvt_F_canonical_xiShift_shell_sub_horizontal_eq_shell_sub_iterated_fourierLaplaceIntegral
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) ht hεpos

/-- The fully explicit shell-minus-iterated Fourier-Laplace expression has the
same residual limit as shell-minus-horizontal. Thus the concrete Fubini /
Fourier-inversion target is precisely to show this explicit residual tends to
zero, which is equivalent at the limit-target level to the missing scalar
time-interchange identity. -/
private theorem
    tendsto_bvt_F_canonical_xiShift_shell_sub_iterated_to_timeShift_sub_canonicalExtension
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t : ℝ} (ht : 0 < t) :
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y) -
        if hε : 0 < ε then
          ∫ x : ℝ,
            (∫ τ : ℝ,
              bvt_W OS lgc (n + m)
                (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
              (SchwartzMap.fourierTransformCLM ℂ
                (SCV.schwartzPsiZ
                  ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
                  (by
                    have hscaled : 0 < (2 * Real.pi) *
                        (((x : ℂ) + ε * Complex.I).im) :=
                      mul_pos Real.two_pi_pos (by simpa using hε)
                    simpa [Complex.mul_im] using hscaled))) τ) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x
        else
          0)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) -
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I))) := by
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  have hEq :=
    bvt_F_canonical_xiShift_shell_sub_horizontal_eventually_eq_shell_sub_iterated_fourierLaplaceIntegral
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) ht
  have hResidual :=
    tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_timeShift_sub_canonicalExtension
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) ht
  exact Filter.Tendsto.congr' hEq hResidual

/-- Exact shell-to-Laplace reduction for the ambient Phase C' witness.

For a fixed positive time `t`, the explicit canonical Wightman witness already
has a horizontal boundary-value limit against the Paley-Wiener kernel
`ψ_{2πit}`. Therefore, to prove that the concrete `bvt_F` canonical
`ξ`-shift shell converges to the same witness value, it is enough to prove that
the difference between that shell and the corresponding horizontal
Fourier-Laplace integral tends to zero.

This isolates the real remaining analytic comparison without changing the
theorem category: both terms are on the Wightman/ambient representative side
`φ, ψ`; no Schwinger/Wightman same-shell equality is asserted. -/
private theorem
    tendsto_bvt_F_canonical_xiShift_to_ambientCanonicalExtension_imagAxis_of_shell_sub_horizontal_tendsto_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t : ℝ} (ht : 0 < t)
    (hShellLaplace :
      let ψZ : SchwartzMap ℝ ℂ :=
        SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht)
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y) -
          (∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
            (SchwartzMap.fourierTransformCLM ℂ ψZ) x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I))) := by
  let ψZ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  let shell : ℝ → ℂ := fun ε =>
    ∫ y : NPointDomain d (n + m),
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
        (φ.conjTensorProduct ψ) y
  let horizontal : ℝ → ℂ := fun ε =>
    ∫ x : ℝ,
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
      (SchwartzMap.fourierTransformCLM ℂ ψZ) x
  have hShellLaplace' :
      Filter.Tendsto
        (fun ε : ℝ => shell ε - horizontal ε)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [shell, horizontal, ψZ] using hShellLaplace
  have hHorizontal :
      Filter.Tendsto horizontal
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I))) := by
    simpa [horizontal, ψZ] using
      (tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_to_imagAxis
        (d := d) (OS := OS) (lgc := lgc) (hm := hm)
        (f := φ) (g := ψ) (hg_compact := hψ_compact) ht)
  have hsum :
      Filter.Tendsto
        (fun ε : ℝ => (shell ε - horizontal ε) + horizontal ε)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (0 +
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I))) :=
    hShellLaplace'.add hHorizontal
  have hEq :
      (fun ε : ℝ => (shell ε - horizontal ε) + horizontal ε) = shell := by
    funext ε
    simp [shell, horizontal]
  simpa [hEq, shell] using hsum

/-- Equality of multivariate Section 4.3 quotient classes forces equality of
the associated one-variable slice tests on `[0,\infty)`, provided the frozen
background times are nonnegative. -/
private theorem partialFourierSpatial_timeSlice_eqOn_nonneg_of_transport_eq
    {n : ℕ}
    {f g : euclideanPositiveTimeSubmodule (d := d) n}
    (hfg : os1TransportComponent d n f = os1TransportComponent d n g)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Set.EqOn
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 r t ξ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      (Set.Ici (0 : ℝ)) := by
  have hregion :
      Set.EqOn ((f : euclideanPositiveTimeSubmodule (d := d) n) : NPointDomain d n → ℂ)
        ((g : euclideanPositiveTimeSubmodule (d := d) n) : NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n) :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq (d := d)
      (n := n) (f := (f : SchwartzNPoint d n)) (g := (g : SchwartzNPoint d n)) hfg
  intro s hs
  have hnonneg : ∀ i : Fin n, 0 ≤ Function.update t r s i := by
    intro i
    by_cases hi : i = r
    · subst hi
      simpa using hs
    · rw [Function.update_of_ne hi]
      exact ht i hi
  simpa [partialFourierSpatial_timeSliceSchwartz] using
    partialFourierSpatial_fun_eq_of_eqOn_section43PositiveEnergyRegion
      (d := d) (n := n) hregion (Function.update t r s) hnonneg ξ

/-- Therefore the one-variable quotient class of the branch-`3b` slice depends
only on the multivariate Section 4.3 quotient class. This is the concrete
slice-level descent step needed before the full iterated pairing theorem. -/
private theorem os1TransportOneVar_partialFourierSpatial_timeSlice_eq_of_transport_eq
    {n : ℕ}
    {f g : euclideanPositiveTimeSubmodule (d := d) n}
    (hfg : os1TransportComponent d n f = os1TransportComponent d n g)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    os1TransportOneVar
      (partialFourierSpatial_timeSliceTest (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ) =
    os1TransportOneVar
      (partialFourierSpatial_timeSliceTest (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ) := by
  apply section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg
  exact partialFourierSpatial_timeSlice_eqOn_nonneg_of_transport_eq
    (d := d) (n := n) hfg r t ht ξ

/-- On the current support-restricted source, equality of multivariate
Section-4.3 classes forces equality of the actual one-variable branch-`3b`
slice Schwartz functions. On `[0,∞)` this is the quotient argument above; on
`(-∞,0)` both slices vanish by positive-time support. -/
private theorem partialFourierSpatial_timeSliceSchwartz_eq_of_transport_eq
    {n : ℕ}
    {f g : euclideanPositiveTimeSubmodule (d := d) n}
    (hfg : os1TransportComponent d n f = os1TransportComponent d n g)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ =
      partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule g).1 r t ξ := by
  ext s
  by_cases hs : 0 ≤ s
  · exact partialFourierSpatial_timeSlice_eqOn_nonneg_of_transport_eq
      (d := d) (n := n) hfg r t ht ξ hs
  · have hf_zero :
      partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ s = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hsupp
      exact hs <|
        tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
          (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ hsupp
    have hg_zero :
        partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 r t ξ s = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hsupp
      exact hs <|
        tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
          (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ hsupp
    simp [hf_zero, hg_zero]

/-- First concrete Stage-5 descended-pairing theorem: on the positive imaginary
axis, the canonical Section-4.3 slice extension depends only on the multivariate
quotient class. This is the honest current-code fragment of the blueprint's
`section43_iteratedSlice_descendedPairing`. -/
theorem section43_iteratedSlice_descendedPairing_imagAxis
    {n : ℕ}
    {f g : euclideanPositiveTimeSubmodule (d := d) n}
    (hfg : os1TransportComponent d n f = os1TransportComponent d n g)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {η : ℝ} (hη : 0 < η) :
    partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ
        (η * Complex.I) =
      partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ
        (η * Complex.I) := by
  rw [partialFourierSpatial_timeSliceCanonicalExtension_eq_complexLaplaceTransform
    (d := d) (n := n) (f := EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ hη]
  rw [partialFourierSpatial_timeSliceCanonicalExtension_eq_complexLaplaceTransform
    (d := d) (n := n) (f := EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ hη]
  simpa [partialFourierSpatial_timeSliceSchwartz_eq_of_transport_eq
    (d := d) (n := n) hfg r t ht ξ]

/-- Full Stage-5 slice descent: once two multivariate positive-time inputs have
the same Section-4.3 quotient class, the canonical one-variable branch-`3b`
slice extensions agree on the entire upper half-plane. This upgrades the
previous imag-axis fragment by a one-variable identity theorem and does not use
any forbidden many-variable separate-analyticity shortcut. -/
theorem section43_iteratedSlice_descendedPairing
    {n : ℕ}
    {f g : euclideanPositiveTimeSubmodule (d := d) n}
    (hfg : os1TransportComponent d n f = os1TransportComponent d n g)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {w : ℂ} (hw : 0 < w.im) :
    partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ w =
      partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ w := by
  exact
    identity_theorem_upperHalfPlane
      (f := partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ)
      (g := partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ)
      (hf := partialFourierSpatial_timeSliceCanonicalExtension_differentiableOn
        (d := d) (n := n) (f := EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ)
      (hg := partialFourierSpatial_timeSliceCanonicalExtension_differentiableOn
        (d := d) (n := n) (f := EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ)
      (hagree := fun η hη =>
        section43_iteratedSlice_descendedPairing_imagAxis
          (d := d) (n := n) hfg r t ht ξ hη)
      w hw

/- Exact fixed-pair Section-4.3 scalarization seam.

As currently stated, this theorem only packages the semigroup-side upper-half-
plane witness with the required positive-imaginary-axis OS identification. The
ambient representatives `φ, ψ` and the transport hypotheses `hφf`, `hψg` do
not yet appear in the conclusion, so the proof below is correspondingly
semigroup-side only.

This means the live Section-4.3 assembly obstruction remains strictly
downstream: one still needs an honest theorem that uses the frozen slice
package to connect the ambient transport data to the canonical-shell limit /
Wightman-side identification consumed later by
`lemma42_matrix_element_time_interchange`.

More sharply, the present source now fixes the first payload ordering inside
that ambient witness package:

- `hH_imag_os` is not the first remaining transport-dependent payload, because
  it is already available semigroup-side from the chosen positive-time
  preimages through
  `section43_fixedPair_upperHalfPlaneScalarization`;
- after that, `rightHalfPlaneWitness_of_upperHalfPlaneScalarization` supplies
  the later witness-shape rotation without any active use of
  `(φ, ψ, hφf, hψg)`;
- so the first theorem-sized payload that still genuinely has to consume the
  ambient transport data is `hlimit`, i.e. the canonical-shell convergence to
  the witness value on the positive imaginary axis.

More sharply, source-first inspection localizes the first exact obstruction
*inside* that `hlimit` constructor:

- the shell whose limit must be proved is the ambient canonical forward-cone
  perturbation
  `ε ↦ ∫ y, bvt_F ... (xiShift ... (fun k μ => ↑(y k μ) + ε * canonical... * I)
    (t : ℂ)) * (φ.conjTensorProduct ψ) y`;
- the currently landed slice package only controls frozen one-variable objects
  indexed by `(r, t, ht, ξ, w)`, namely the canonical slice extensions and the
  descended scalar Fourier pairings attached to those slices;
- the imported canonical-witness suppliers from
  `OSToWightmanBoundaryValueLimits.lean`, including
  `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_fourierLaplaceIntegral`,
  `tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_to_imagAxis`,
  and
  `bvt_exists_singleSplit_xiShift_holomorphicValue_with_limit`,
  still do not close this seam:
  they operate only on the preimage-side data `(f, g, hg_compact)` and give
  either a canonical witness value or a preimage-side shell witness, but no
  theorem among them consumes the ambient representatives `φ, ψ` together with
  the transport equalities `hφf, hψg` to identify the ambient canonical shell
  above with that witness value;
- there is still no theorem in the present source that rewrites the above
  ambient canonical-shell integrand, for fixed positive real `t`, as an
  assembled scalar built from those frozen slice pairings, nor any theorem that
  identifies the resulting assembled scalar with the semigroup-side witness
  value on `((t : ℂ) * Complex.I)`.
- equivalently, the exact missing theorem-sized payload is still the first
  transport-backed assembly step that would take the frozen slice chain
  `section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
  -> `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
  -> `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
  -> `section43_iteratedSlice_descendedPairing`
  and package those slicewise equalities, for the fixed pair
  `(φ, ψ, hφf, hψg)`, into a single scalar value that is simultaneously:
  1. the `ε -> 0+` target of the ambient canonical `xiShift` shell, and
  2. the value of an ambient upper-half-plane witness on `((t : ℂ) * I)`;
- stated one notch earlier at fixed positive real `t`, there is still no
  current theorem whose conclusion even rewrites the ambient canonical shell
  integrand
  `ε ↦ ∫ y, bvt_F ... (xiShift ... (fun k μ =>
      ↑(y k μ) + ε * canonicalForwardConeDirection ... * I) (t : ℂ)) *
      (φ.conjTensorProduct ψ) y`
  as a single scalar assembled from that frozen slice chain before taking the
  `ε -> 0+` limit;
- equivalently, after freezing one positive real time `t`, the first missing
  source-backed theorem would have to start from the exact ambient shell
  function
  `shell_t(ε) :=
    ∫ y, bvt_F ... (xiShift ... (fun k μ =>
        ↑(y k μ) + ε * canonicalForwardConeDirection ... * I) (t : ℂ)) *
      (φ.conjTensorProduct ψ) y`
  and produce one scalar `A_t` assembled from the frozen slice package
  `section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
  ->
  `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
  ->
  `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
  ->
  `section43_iteratedSlice_descendedPairing`,
  and prove only
  `Filter.Tendsto shell_t (nhdsWithin 0 (Set.Ioi 0)) (nhds A_t)`;
- stated in exactly the currently missing fixed-`t` shell-to-slice form, there
  is still no theorem in the present source of shape
  `∀ t : ℝ, 0 < t → ∃ A_t : ℂ, ...` that rewrites the ambient canonical
  `xiShift` shell for `(φ, ψ)` into one scalar assembled from that frozen
  slice chain before any later witness-value identification;
- stated even more tightly at fixed positive real `t`, the missing source-backed
  theorem would have to start from the actual ambient shell function
  `ε ↦ ∫ y, bvt_F ... (xiShift ... (fun k μ =>
      ↑(y k μ) + ε * canonicalForwardConeDirection ... * I) (t : ℂ)) *
      (φ.conjTensorProduct ψ) y`
  and prove that its limit as `ε -> 0+` is computed by one scalar assembled
  from the frozen slice data already controlled by the four theorems above;
- the bounded fixed-`t` pass reconfirms that there is still no honest smaller
  theorem below this shell surface: once the exact ambient shell is frozen,
  any weaker statement would still leave the transport-backed shell-to-slice
  aggregation itself undone and so would only rename one frozen slice equality
  rather than perform new mathematics;
- there is still no honest smaller theorem below that fixed-`t` shell surface:
  any candidate statement that keeps the same ambient shell on the left but
  produces anything weaker than such an assembled scalar `A_t` on the right
  would merely repackage one frozen slice equality without performing the
  missing shell-to-slice aggregation, so it would be wrapper drift rather than
  a mathematically smaller source-backed prerequisite;
- no current theorem rewrites that exact ambient shell into such an assembled
  frozen-slice scalar, even after fixing `t > 0`, so the obstruction is not a
  further uniqueness theorem, not witness-shape rotation, and not any later
  closure argument: it is precisely the first transport-backed shell-to-slice
  assembly for the fixed pair `(φ, ψ)` / `(f, g)`;
- until that exact assembly exists, the current file has no source-backed way
  to build the fixed-pair witness package consumed later by
  `kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_upperHalfPlaneWitness_on_imagAxis`,
  because the landed semigroup-side scalarization and rotation theorems never
  convert the ambient transport equalities into a scalar shell-limit statement.

Readiness verdict after this bounded source-first pass:

- the already-landed theorem below,
  `section43_fixedPair_shellToSlice_limit_fixedTime`,
  remains only a boundary-value existence corollary; its chosen witness
  `A_t := bvt_W ... (φ.conjTensorProduct (timeShiftSchwartzNPoint ... t ψ))`
  is not the missing Section-4.3 shell-to-slice scalar assembled from the
  transport data `(φ, ψ, f, g, hφf, hψg)`;
- the exact first lower source-backed ingredient beneath that intended shell-
  to-slice assembly is still the frozen-slice consumer cluster already present
  in this file:
  `section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
  ->
  `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
  ->
  `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
  ->
  `section43_iteratedSlice_descendedPairing`;
- source-first inspection of the theorem bodies sharpens that one notch
  further: the first theorem strictly below that public cluster is the private
  `Set.EqOn` bridge
  `partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport`, because
  the first public edge
  `section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
  is only `section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg` applied to
  that slice equality on `[0,∞)`;
- therefore, if the fixed-time canonical-shell specialization of the public
  frozen-slice chain is still too high, the exact first lower ingredient now
  exposed by the current source is:
  1. choose the canonical frozen slice parameters `(r, tSlice, ht, ξ)` that
     realize the ambient shell as a one-variable `partialFourierSpatial` slice,
  2. then apply
     `partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport`
     at those parameters before re-descending to the quotient/pairing levels;
- no current theorem packages that fixed-`t` frozen-slice cluster into one
  scalar target for the ambient canonical shell, so there is still no honest
  smaller theorem between the live local seam `hlimit_os` and that frozen-slice
  cluster;
- if work resumes below this seam, the next honest theorem must expose the
  exact inline frozen-slice scalar assembled from that cluster, not introduce a
  fresh wrapper witness name or another existence theorem. -/

omit [NeZero d] in
private theorem tsupport_precomp_subset_local {X Y α : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Zero α]
    {f : Y → α} {h : X → Y} (hh : Continuous h) :
    tsupport (fun x => f (h x)) ⊆ h ⁻¹' tsupport f := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage hh)
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

private theorem section43_fixedPair_nonnegTimeCoords_of_mem_tsupport_conjTensorProduct
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    {y : NPointDomain d (n + m)}
    (hy : y ∈ tsupport (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
      NPointDomain d (n + m) → ℂ))) :
    ∀ i : Fin (n + m), 0 ≤ y i 0 := by
  have hsplitFirstRev_cont :
      Continuous (fun z : NPointDomain d (n + m) =>
        fun i : Fin n => splitFirst n m z (Fin.rev i)) := by
    refine continuous_pi ?_
    intro i
    simpa [splitFirst] using
      (continuous_apply (Fin.castAdd m (Fin.rev i)) :
        Continuous fun z : NPointDomain d (n + m) => z (Fin.castAdd m (Fin.rev i)))
  have hyprod :
      y ∈ tsupport (fun z : NPointDomain d (n + m) =>
        starRingEnd ℂ (f (fun i : Fin n => splitFirst n m z (Fin.rev i))) *
          g (splitLast n m z)) := by
    simpa [SchwartzMap.conjTensorProduct_apply] using hy
  have hleft :
      (fun i : Fin n => splitFirst n m y (Fin.rev i)) ∈
        tsupport (f : NPointDomain d n → ℂ) := by
    have hy_left :
        y ∈ tsupport (fun z : NPointDomain d (n + m) =>
          starRingEnd ℂ (f (fun i : Fin n => splitFirst n m z (Fin.rev i)))) :=
      (tsupport_mul_subset_left
        (f := fun z : NPointDomain d (n + m) =>
          starRingEnd ℂ (f (fun i : Fin n => splitFirst n m z (Fin.rev i))))
        (g := fun z : NPointDomain d (n + m) => g (splitLast n m z))) hyprod
    exact tsupport_precomp_subset_local
      (f := (f : NPointDomain d n → ℂ))
      (h := fun z : NPointDomain d (n + m) => fun i : Fin n =>
        splitFirst n m z (Fin.rev i))
      hsplitFirstRev_cont
      ((tsupport_comp_subset
        (g := starRingEnd ℂ)
        (map_zero _)
        (fun z : NPointDomain d (n + m) =>
          f (fun i : Fin n => splitFirst n m z (Fin.rev i)))) hy_left)
  have hright :
      splitLast n m y ∈ tsupport (g : NPointDomain d m → ℂ) := by
    exact tsupport_precomp_subset_local
      (f := (g : NPointDomain d m → ℂ))
      (h := splitLast n m)
      (splitLast_continuousLinear n m)
      ((tsupport_mul_subset_right
        (f := fun z : NPointDomain d (n + m) =>
          starRingEnd ℂ (f (fun i : Fin n => splitFirst n m z (Fin.rev i))))
        (g := fun z : NPointDomain d (n + m) => g (splitLast n m z))) hyprod)
  intro i
  by_cases hi : i.1 < n
  · have hpos :
        0 < ((fun j : Fin n => splitFirst n m y (Fin.rev j)) (Fin.rev ⟨i.1, hi⟩)) 0 :=
      (hf_ord hleft (Fin.rev ⟨i.1, hi⟩)).1
    simpa [splitFirst, hi] using le_of_lt hpos
  · have hi_ge : n ≤ i.1 := Nat.not_lt.mp hi
    let j : Fin m := ⟨i.1 - n, by omega⟩
    have hij : Fin.natAdd n j = i := by
      apply Fin.ext
      simp [j, hi_ge]
    have hpos : 0 < (splitLast n m y j) 0 := (hg_ord hright j).1
    simpa [splitLast, hij] using le_of_lt hpos

private theorem section43_fixedPair_leftBlock_reverseTimeOrder_of_mem_tsupport_conjTensorProduct
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    {y : NPointDomain d (n + m)}
    (hy : y ∈ tsupport (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
      NPointDomain d (n + m) → ℂ))) :
    ∀ {i j : Fin (n + m)}, i.1 < n → j.1 < n → i < j → y j 0 < y i 0 := by
  have hsplitFirstRev_cont :
      Continuous (fun z : NPointDomain d (n + m) =>
        fun i : Fin n => splitFirst n m z (Fin.rev i)) := by
    refine continuous_pi ?_
    intro i
    simpa [splitFirst] using
      (continuous_apply (Fin.castAdd m (Fin.rev i)) :
        Continuous fun z : NPointDomain d (n + m) => z (Fin.castAdd m (Fin.rev i)))
  have hyprod :
      y ∈ tsupport (fun z : NPointDomain d (n + m) =>
        starRingEnd ℂ (f (fun i : Fin n => splitFirst n m z (Fin.rev i))) *
          g (splitLast n m z)) := by
    simpa [SchwartzMap.conjTensorProduct_apply] using hy
  have hleft :
      (fun i : Fin n => splitFirst n m y (Fin.rev i)) ∈
        tsupport (f : NPointDomain d n → ℂ) := by
    have hy_left :
        y ∈ tsupport (fun z : NPointDomain d (n + m) =>
          starRingEnd ℂ (f (fun i : Fin n => splitFirst n m z (Fin.rev i)))) :=
      (tsupport_mul_subset_left
        (f := fun z : NPointDomain d (n + m) =>
          starRingEnd ℂ (f (fun i : Fin n => splitFirst n m z (Fin.rev i))))
        (g := fun z : NPointDomain d (n + m) => g (splitLast n m z))) hyprod
    exact tsupport_precomp_subset_local
      (f := (f : NPointDomain d n → ℂ))
      (h := fun z : NPointDomain d (n + m) => fun i : Fin n =>
        splitFirst n m z (Fin.rev i))
      hsplitFirstRev_cont
      ((tsupport_comp_subset
        (g := starRingEnd ℂ)
        (map_zero _)
        (fun z : NPointDomain d (n + m) =>
          f (fun i : Fin n => splitFirst n m z (Fin.rev i)))) hy_left)
  intro i j hi hj hij
  have hrev : Fin.rev ⟨j.1, hj⟩ < Fin.rev ⟨i.1, hi⟩ := by
    simpa using (Fin.rev_lt_rev.mpr hij)
  have htime :
      ((fun k : Fin n => splitFirst n m y (Fin.rev k)) (Fin.rev ⟨j.1, hj⟩)) 0 <
        ((fun k : Fin n => splitFirst n m y (Fin.rev k)) (Fin.rev ⟨i.1, hi⟩)) 0 :=
    (hf_ord hleft (Fin.rev ⟨j.1, hj⟩)).2 (Fin.rev ⟨i.1, hi⟩) hrev
  simpa [splitFirst] using htime

/-- Exact lower obstruction beneath the fixed-time shell-to-slice seam: a
support point of `f.conjTensorProduct g` with two left-block indices can never
lie in `OrderedPositiveTimeRegion d (n + m)`, because the left block is
reversed by `conjTensorProduct`. So the attempted whole-shell ordered-support
goal is false before any cross-block barrier is considered. -/
private theorem section43_fixedPair_conjTensorProduct_not_mem_orderedPositiveTimeRegion_of_leftBlockPair
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    {y : NPointDomain d (n + m)}
    (hy : y ∈ tsupport (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
      NPointDomain d (n + m) → ℂ)))
    {i j : Fin (n + m)}
    (hi : i.1 < n) (hj : j.1 < n) (hij : i < j) :
    y ∉ OrderedPositiveTimeRegion d (n + m) := by
  intro hy_ord
  have hrev :
      y j 0 < y i 0 :=
    section43_fixedPair_leftBlock_reverseTimeOrder_of_mem_tsupport_conjTensorProduct
      (d := d) (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord)
      (y := y) hy hi hj hij
  have hord : y i 0 < y j 0 := (hy_ord i).2 j hij
  exact (not_lt_of_gt hrev) hord

private theorem section43_fixedPair_rightBlock_forwardTimeOrder_of_mem_tsupport_conjTensorProduct
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    {y : NPointDomain d (n + m)}
    (hy : y ∈ tsupport (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
      NPointDomain d (n + m) → ℂ))) :
    ∀ {i j : Fin (n + m)}, n ≤ i.1 → n ≤ j.1 → i < j → y i 0 < y j 0 := by
  have hsplitFirstRev_cont :
      Continuous (fun z : NPointDomain d (n + m) =>
        fun i : Fin n => splitFirst n m z (Fin.rev i)) := by
    refine continuous_pi ?_
    intro i
    simpa [splitFirst] using
      (continuous_apply (Fin.castAdd m (Fin.rev i)) :
        Continuous fun z : NPointDomain d (n + m) => z (Fin.castAdd m (Fin.rev i)))
  have hyprod :
      y ∈ tsupport (fun z : NPointDomain d (n + m) =>
        starRingEnd ℂ (f (fun i : Fin n => splitFirst n m z (Fin.rev i))) *
          g (splitLast n m z)) := by
    simpa [SchwartzMap.conjTensorProduct_apply] using hy
  have hright :
      splitLast n m y ∈ tsupport (g : NPointDomain d m → ℂ) := by
    exact tsupport_precomp_subset_local
      (f := (g : NPointDomain d m → ℂ))
      (h := splitLast n m)
      (splitLast_continuousLinear n m)
      ((tsupport_mul_subset_right
        (f := fun z : NPointDomain d (n + m) =>
          starRingEnd ℂ (f (fun i : Fin n => splitFirst n m z (Fin.rev i))))
        (g := fun z : NPointDomain d (n + m) => g (splitLast n m z))) hyprod)
  intro i j hi hj hij
  let ii : Fin m := ⟨i.1 - n, by omega⟩
  let jj : Fin m := ⟨j.1 - n, by omega⟩
  have hii : Fin.natAdd n ii = i := by
    apply Fin.ext
    simp [ii, hi]
  have hjj : Fin.natAdd n jj = j := by
    apply Fin.ext
    simp [jj, hj]
  have hij' : ii < jj := by
    apply Fin.lt_iff_val_lt_val.mpr
    dsimp [ii, jj]
    omega
  have htime : (splitLast n m y ii) 0 < (splitLast n m y jj) 0 :=
    (hg_ord hright ii).2 jj hij'
  simpa [splitLast, hii, hjj] using htime

private theorem section43_fixedPair_nonnegAwayFrom_r_of_mem_tsupport_conjTensorProduct
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (y : NPointDomain d (n + m)) (t : ℝ)
    (ht : 0 ≤ t) :
    let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
    let tSlice : Fin (n + m) → ℝ :=
      fun i =>
        if hi : i.1 < n then
          y i 0
        else if hir : i = r then
          0
        else
          y i 0 + t
    y ∈ tsupport (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
      NPointDomain d (n + m) → ℂ)) →
      ∀ i : Fin (n + m), i ≠ r → 0 ≤ tSlice i := by
  dsimp
  intro hy
  have hy_nonneg :
      ∀ i : Fin (n + m), 0 ≤ y i 0 :=
    section43_fixedPair_nonnegTimeCoords_of_mem_tsupport_conjTensorProduct
      (d := d) f hf_ord g hg_ord hy
  let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let tSlice : Fin (n + m) → ℝ :=
    fun i =>
      if hi : i.1 < n then
        y i 0
      else if hir : i = r then
        0
      else
        y i 0 + t
  intro i hi
  by_cases hin : i.1 < n
  · simp [tSlice, hin, hy_nonneg i]
  · by_cases hir : i = r
    · exact (hi hir).elim
    · have htime : 0 ≤ y i 0 + t := add_nonneg (hy_nonneg i) ht
      have hir_lit : i ≠ ⟨n, Nat.lt_add_of_pos_right hm⟩ := by
        simpa [r] using hir
      simpa [hin, hir_lit] using htime

private theorem section43_fixedPair_canonicalShell_realPart_sliceRealization
    {n m : ℕ} (hm : 0 < m)
    (y : NPointDomain d (n + m)) (t ε : ℝ) :
    let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
    let tSlice : Fin (n + m) → ℝ :=
      fun i =>
        if hi : i.1 < n then
          y i 0
        else if hir : i = r then
          0
        else
          y i 0 + t
    let ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d) :=
      (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
        (fun p => y p.1 (Fin.succ p.2))
    let z : Fin (n + m) → Fin (d + 1) → ℂ :=
      xiShift r 0
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
        (t : ℂ)
    Function.update tSlice r (y r 0 + t) = (fun i => (z i 0).re) ∧
      ξ =
        (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
          (fun p => (z p.1 (Fin.succ p.2)).re) := by
  dsimp
  let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let tSlice : Fin (n + m) → ℝ :=
    fun i =>
      if hi : i.1 < n then
        y i 0
      else if hir : i = r then
        0
      else
        y i 0 + t
  let ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d) :=
    (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
      (fun p => y p.1 (Fin.succ p.2))
  let z : Fin (n + m) → Fin (d + 1) → ℂ :=
    xiShift r 0
      (fun k μ =>
        ↑(y k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
      (t : ℂ)
  refine ⟨?_, ?_⟩
  · ext i
    by_cases hir : i = r
    · subst hir
      simp [z, xiShift, r]
    · by_cases hin : i.1 < n
      · have hnot : ¬ r.val ≤ i.val := by
          simpa [r] using Nat.not_le_of_gt hin
        simp [Function.update, tSlice, z, xiShift, r, hir, hin, hnot]
      · have hr_le : r.val ≤ i.val := by
          simpa [r] using Nat.le_of_not_lt hin
        simp [Function.update, tSlice, z, xiShift, r, hir, hin, hr_le]
  · ext p
    simp [ξ, z, xiShift, canonicalForwardConeDirection]

private theorem section43_fixedPair_canonicalShell_sliceRealization
    {n m : ℕ} (hm : 0 < m)
    (Φ : SchwartzNPoint d (n + m))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (y : NPointDomain d (n + m)) (t ε : ℝ)
    (ht : 0 ≤ t)
    (hy : y ∈ tsupport (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
      NPointDomain d (n + m) → ℂ))) :
    let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
    let tSlice : Fin (n + m) → ℝ :=
      fun i =>
        if hi : i.1 < n then
          y i 0
        else if hir : i = r then
          0
        else
          y i 0 + t
    let ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d) :=
      (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
        (fun p => y p.1 (Fin.succ p.2))
    let z : Fin (n + m) → Fin (d + 1) → ℂ :=
      xiShift r 0
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
        (t : ℂ)
    (∀ i : Fin (n + m), i ≠ r → 0 ≤ tSlice i) ∧
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) Φ r tSlice ξ :
          SchwartzMap ℝ ℂ) (y r 0 + t) =
        OSReconstruction.partialFourierSpatial_fun (d := d) (n := n + m) Φ
          ((fun i => (z i 0).re),
            (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
              (fun p => (z p.1 (Fin.succ p.2)).re))) := by
  dsimp
  let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let tSlice : Fin (n + m) → ℝ :=
    fun i =>
      if hi : i.1 < n then
        y i 0
      else if hir : i = r then
        0
      else
        y i 0 + t
  let ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d) :=
    (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
      (fun p => y p.1 (Fin.succ p.2))
  let z : Fin (n + m) → Fin (d + 1) → ℂ :=
    xiShift r 0
      (fun k μ =>
        ↑(y k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
      (t : ℂ)
  have hnonneg :
      ∀ i : Fin (n + m), i ≠ r → 0 ≤ tSlice i :=
    section43_fixedPair_nonnegAwayFrom_r_of_mem_tsupport_conjTensorProduct
      (d := d) (hm := hm) f hf_ord g hg_ord y t ht hy
  have hreal :
      Function.update tSlice r (y r 0 + t) = (fun i => (z i 0).re) ∧
        ξ =
          (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
            (fun p => (z p.1 (Fin.succ p.2)).re) :=
    section43_fixedPair_canonicalShell_realPart_sliceRealization
      (d := d) (hm := hm) y t ε
  refine ⟨hnonneg, ?_⟩
  change
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n + m) Φ
      (Function.update tSlice r (y r 0 + t), ξ) =
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n + m) Φ
      ((fun i => (z i 0).re),
        (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
          (fun p => (z p.1 (Fin.succ p.2)).re))
  rw [hreal.1, hreal.2]

/-- Region-level fixed-time canonical shell realization on the actual shell used
in `hlimit_os`: once the background point lies in the Section-4.3 positive-
energy region, the canonical `xiShift` shell is already the corresponding
frozen slice, with the required nonnegativity away from the distinguished index
`r`. This is the first honest shell-domain promotion strictly below the failed
ambient shell-vanishing attempt. -/
private theorem section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion
    {n m : ℕ} (hm : 0 < m)
    (Φ : SchwartzNPoint d (n + m))
    (y : NPointDomain d (n + m)) (t ε : ℝ)
    (ht : 0 ≤ t)
    (hy_region : y ∈ section43PositiveEnergyRegion d (n + m)) :
    let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
    let tSlice : Fin (n + m) → ℝ :=
      fun i =>
        if hi : i.1 < n then
          y i 0
        else if hir : i = r then
          0
        else
          y i 0 + t
    let ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d) :=
      (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
        (fun p => y p.1 (Fin.succ p.2))
    let z : Fin (n + m) → Fin (d + 1) → ℂ :=
      xiShift r 0
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
        (t : ℂ)
    (∀ i : Fin (n + m), i ≠ r → 0 ≤ tSlice i) ∧
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) Φ r tSlice ξ :
          SchwartzMap ℝ ℂ) (y r 0 + t) =
        OSReconstruction.partialFourierSpatial_fun (d := d) (n := n + m) Φ
          ((fun i => (z i 0).re),
            (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
              (fun p => (z p.1 (Fin.succ p.2)).re))) := by
  dsimp
  let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let tSlice : Fin (n + m) → ℝ :=
    fun i =>
      if hi : i.1 < n then
        y i 0
      else if hir : i = r then
        0
      else
        y i 0 + t
  let ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d) :=
    (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
      (fun p => y p.1 (Fin.succ p.2))
  let z : Fin (n + m) → Fin (d + 1) → ℂ :=
    xiShift r 0
      (fun k μ =>
        ↑(y k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
      (t : ℂ)
  have hnonneg :
      ∀ i : Fin (n + m), i ≠ r → 0 ≤ tSlice i := by
    intro i hi
    by_cases hin : i.1 < n
    · simp [tSlice, hin, hy_region i]
    · by_cases hir : i = r
      · exact (hi hir).elim
      · have htime : 0 ≤ y i 0 + t := add_nonneg (hy_region i) ht
        simp [tSlice, hin, hir, htime]
  have hreal :
      Function.update tSlice r (y r 0 + t) = (fun i => (z i 0).re) ∧
        ξ =
          (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
            (fun p => (z p.1 (Fin.succ p.2)).re) :=
    section43_fixedPair_canonicalShell_realPart_sliceRealization
      (d := d) (hm := hm) y t ε
  refine ⟨hnonneg, ?_⟩
  change
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n + m) Φ
      (Function.update tSlice r (y r 0 + t), ξ) =
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n + m) Φ
      ((fun i => (z i 0).re),
        (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
          (fun p => (z p.1 (Fin.succ p.2)).re))
  rw [hreal.1, hreal.2]

/- Already-landed shell-limit existence corollary.

This theorem only records that the fixed-time canonical ambient shell has some
limit; on the current branch that witness is supplied by the boundary-value
target `bvt_W ... (φ.conjTensorProduct (timeShiftSchwartzNPoint ... t ψ))`.
It is therefore not the missing transport-backed Section-4.3 shell-to-slice
assembly, which would have to expose the inline frozen-slice scalar built from
the slice transport cluster listed immediately above. -/
theorem section43_fixedPair_shellToSlice_limit_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩) :
    ∀ t : ℝ, 0 < t → ∃ A_t : ℂ,
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds A_t) := by
  intro t ht
  refine ⟨
    bvt_W OS lgc (n + m)
      (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)),
    ?_⟩
  exact
    tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue
      (d := d) (OS := OS) (lgc := lgc) (hm := hm) (φ := φ) (ψ := ψ) (t := t)

/-- Total-arity ambient tensor classes agree with the explicit tensor built from
the chosen Section-4.3 preimages, at the quotient level. This is the exact
source-backed predecessor of the still-missing attempt to repackage that class
as an `os1TransportComponent` at arity `n + m`. -/
private theorem section43PositiveEnergyQuotientMap_conjTensorProduct_eq_of_repr_eq_transport
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩) :
    section43PositiveEnergyQuotientMap (d := d) (n + m) (φ.conjTensorProduct ψ) =
      section43PositiveEnergyQuotientMap (d := d) (n + m) (f.conjTensorProduct g) := by
  have hφ_region :
      Set.EqOn (φ : NPointDomain d n → ℂ) (f : NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n) := by
    have hq :
        section43PositiveEnergyQuotientMap (d := d) n φ =
          section43PositiveEnergyQuotientMap (d := d) n f := by
      simpa [os1TransportComponent_apply] using hφf
    exact eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := n) (f := φ) (g := f) hq
  have hψ_region :
      Set.EqOn (ψ : NPointDomain d m → ℂ) (g : NPointDomain d m → ℂ)
        (section43PositiveEnergyRegion d m) := by
    have hq :
        section43PositiveEnergyQuotientMap (d := d) m ψ =
          section43PositiveEnergyQuotientMap (d := d) m g := by
      simpa [os1TransportComponent_apply] using hψg
    exact eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := m) (f := ψ) (g := g) hq
  apply section43PositiveEnergyQuotientMap_eq_of_eqOn_region
  intro x hx
  have hφ_eq :
      φ (fun i : Fin n => splitFirst n m x (Fin.rev i)) =
        f (fun i : Fin n => splitFirst n m x (Fin.rev i)) := by
    apply hφ_region
    intro i
    simpa [section43PositiveEnergyRegion, splitFirst] using
      hx (Fin.castAdd m (Fin.rev i))
  have hψ_eq :
      ψ (splitLast n m x) = g (splitLast n m x) := by
    apply hψ_region
    intro i
    simpa [section43PositiveEnergyRegion, splitLast] using
      hx (Fin.natAdd n i)
  simp [SchwartzMap.conjTensorProduct_apply, hφ_eq, hψ_eq]

/-- On the actual source shell domain where the fixed-time slice theorems are
available, the ambient tensor weight already agrees pointwise with the explicit
preimage tensor weight. This is the exact lower weight-comparison fact currently
available beneath `hlimit_os`. -/
private theorem section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_section43Region
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩)
    {y : NPointDomain d (n + m)}
    (hy : y ∈ section43PositiveEnergyRegion d (n + m)) :
    (φ.conjTensorProduct ψ) y = (f.conjTensorProduct g) y := by
  have hrepr :
      section43PositiveEnergyQuotientMap (d := d) (n + m) (φ.conjTensorProduct ψ) =
        section43PositiveEnergyQuotientMap (d := d) (n + m) (f.conjTensorProduct g) := by
    exact
      section43PositiveEnergyQuotientMap_conjTensorProduct_eq_of_repr_eq_transport
        (d := d) (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
        (g := g) (hg_ord := hg_ord) (hφf := hφf) (hψg := hψg)
  exact
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := n + m) (f := φ.conjTensorProduct ψ) (g := f.conjTensorProduct g) hrepr
      hy

/-- On the Section-4.3 positive-energy region, the ambient tensor weight already
vanishes off the exact source-shell support. This is the sharpest pointwise
vanishing consequence currently available beneath `hlimit_os`. -/
private theorem section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩)
    {y : NPointDomain d (n + m)}
    (hy_region : y ∈ section43PositiveEnergyRegion d (n + m))
    (hy_not_source :
      y ∉ tsupport (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
        NPointDomain d (n + m) → ℂ))) :
    (φ.conjTensorProduct ψ) y = 0 := by
  rw [section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_section43Region
    (d := d) (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
    (g := g) (hg_ord := hg_ord) (hφf := hφf) (hψg := hψg) hy_region]
  exact image_eq_zero_of_notMem_tsupport hy_not_source

/-- On the actual source shell domain where the fixed-time slice theorems are
available, the ambient tensor weight already agrees pointwise with the explicit
preimage tensor weight. This is the exact lower weight-comparison fact currently
available beneath `hlimit_os`. -/
private theorem section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_source_tsupport
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩)
    {y : NPointDomain d (n + m)}
    (hy : y ∈ tsupport (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
      NPointDomain d (n + m) → ℂ))) :
    (φ.conjTensorProduct ψ) y = (f.conjTensorProduct g) y := by
  have hrepr :
      section43PositiveEnergyQuotientMap (d := d) (n + m) (φ.conjTensorProduct ψ) =
        section43PositiveEnergyQuotientMap (d := d) (n + m) (f.conjTensorProduct g) := by
    exact
      section43PositiveEnergyQuotientMap_conjTensorProduct_eq_of_repr_eq_transport
        (d := d) (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
        (g := g) (hg_ord := hg_ord) (hφf := hφf) (hψg := hψg)
  have hy_region : y ∈ section43PositiveEnergyRegion d (n + m) := by
    intro i
    exact
      section43_fixedPair_nonnegTimeCoords_of_mem_tsupport_conjTensorProduct
        (d := d) (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) hy i
  exact
    section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_section43Region
      (d := d) (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
      (g := g) (hg_ord := hg_ord) (hφf := hφf) (hψg := hψg) hy_region

/-- Fixed-time canonical specialization of the mixed-order frozen-slice
transport bridge: once the ambient pair `φ, ψ` and the positive-time preimages
`f, g` are fixed, every canonical shell slice value on the ambient tensor at
the evaluation point `y r 0 + t` already agrees with the corresponding
mixed-order source slice value. This is the first exact transport rewrite
needed immediately below `hshellToSlice` in the live fixed-time seam. -/
private theorem section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩)
    (y : NPointDomain d (n + m)) (t : ℝ) (ht : 0 < t)
    (hy : y ∈ tsupport (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
      NPointDomain d (n + m) → ℂ))) :
    let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
    let tSlice : Fin (n + m) → ℝ :=
      fun i =>
        if hi : i.1 < n then
          y i 0
        else if hir : i = r then
          0
        else
          y i 0 + t
    let ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d) :=
      (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
        (fun p => y p.1 (Fin.succ p.2))
    ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
        (φ.conjTensorProduct ψ) r tSlice ξ : SchwartzMap ℝ ℂ) (y r 0 + t)) =
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
        (OSReconstruction.FixedPairMixedOrderComponent.ofConjTensorProduct
          (d := d) (n := n) (m := m) f hf_ord g hg_ord).1
          r tSlice ξ : SchwartzMap ℝ ℂ) (y r 0 + t)) := by
  dsimp
  let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let tSlice : Fin (n + m) → ℝ :=
    fun i =>
      if hi : i.1 < n then
        y i 0
      else if hir : i = r then
        0
      else
        y i 0 + t
  let ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d) :=
    (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
      (fun p => y p.1 (Fin.succ p.2))
  let F :=
    OSReconstruction.FixedPairMixedOrderComponent.ofConjTensorProduct
      (d := d) (n := n) (m := m) f hf_ord g hg_ord
  have hrepr :
      section43PositiveEnergyQuotientMap (d := d) (n + m) (φ.conjTensorProduct ψ) =
        section43PositiveEnergyQuotientMap (d := d) (n + m) F.1 := by
    simpa [F] using
      section43PositiveEnergyQuotientMap_conjTensorProduct_eq_of_repr_eq_transport
        (d := d) (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
        (g := g) (hg_ord := hg_ord) (hφf := hφf) (hψg := hψg)
  have hnonnegAway :
      ∀ i : Fin (n + m), i ≠ r → 0 ≤ tSlice i := by
    simpa [r, tSlice] using
      section43_fixedPair_nonnegAwayFrom_r_of_mem_tsupport_conjTensorProduct
        (d := d) (hm := hm) (f := f) (hf_ord := hf_ord)
        (g := g) (hg_ord := hg_ord) (y := y) (t := t) (ht := le_of_lt ht) hy
  have hsliceEq :
      Set.EqOn
        ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
          (φ.conjTensorProduct ψ) r tSlice ξ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
          F.1 r tSlice ξ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        (Set.Ici (0 : ℝ)) := by
    exact
      partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_fixedPairMixedOrder
        (d := d) (n := n) (m := m) (Φ := φ.conjTensorProduct ψ) (F := F)
        hrepr r tSlice hnonnegAway ξ
  have hy_nonneg :
      0 ≤ y r 0 := by
    exact
      section43_fixedPair_nonnegTimeCoords_of_mem_tsupport_conjTensorProduct
        (d := d) (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) hy r
  have hEval_nonneg : y r 0 + t ∈ Set.Ici (0 : ℝ) := by
    exact add_nonneg hy_nonneg (le_of_lt ht)
  exact hsliceEq hEval_nonneg

/-- Region-level fixed-time canonical transport beneath the ambient shell
comparison seam: the same fixed-time slice transport identity already holds on
the entire Section-4.3 positive-energy region, not just on the explicit source
support. This is the first honest weakening strictly below the failed ambient
shell-vanishing theorem. -/
private theorem section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩)
    (y : NPointDomain d (n + m)) (t : ℝ) (ht : 0 < t)
    (hy_region : y ∈ section43PositiveEnergyRegion d (n + m)) :
    let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
    let tSlice : Fin (n + m) → ℝ :=
      fun i =>
        if hi : i.1 < n then
          y i 0
        else if hir : i = r then
          0
        else
          y i 0 + t
    let ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d) :=
      (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
        (fun p => y p.1 (Fin.succ p.2))
    ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
        (φ.conjTensorProduct ψ) r tSlice ξ : SchwartzMap ℝ ℂ) (y r 0 + t)) =
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
        (OSReconstruction.FixedPairMixedOrderComponent.ofConjTensorProduct
          (d := d) (n := n) (m := m) f hf_ord g hg_ord).1
          r tSlice ξ : SchwartzMap ℝ ℂ) (y r 0 + t)) := by
  dsimp
  let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let tSlice : Fin (n + m) → ℝ :=
    fun i =>
      if hi : i.1 < n then
        y i 0
      else if hir : i = r then
        0
      else
        y i 0 + t
  let ξ : EuclideanSpace ℝ (Fin (n + m) × Fin d) :=
    (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
      (fun p => y p.1 (Fin.succ p.2))
  let F :=
    OSReconstruction.FixedPairMixedOrderComponent.ofConjTensorProduct
      (d := d) (n := n) (m := m) f hf_ord g hg_ord
  have hrepr :
      section43PositiveEnergyQuotientMap (d := d) (n + m) (φ.conjTensorProduct ψ) =
        section43PositiveEnergyQuotientMap (d := d) (n + m) F.1 := by
    simpa [F] using
      section43PositiveEnergyQuotientMap_conjTensorProduct_eq_of_repr_eq_transport
        (d := d) (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
        (g := g) (hg_ord := hg_ord) (hφf := hφf) (hψg := hψg)
  have hnonnegAway :
      ∀ i : Fin (n + m), i ≠ r → 0 ≤ tSlice i := by
    intro i hi
    by_cases hin : i.1 < n
    · simp [tSlice, hin, hy_region i]
    · by_cases hir : i = r
      · exact (hi hir).elim
      · have htime : 0 ≤ y i 0 + t := add_nonneg (hy_region i) (le_of_lt ht)
        simp [tSlice, hin, hir, htime]
  have hsliceEq :
      Set.EqOn
        ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
          (φ.conjTensorProduct ψ) r tSlice ξ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
          F.1 r tSlice ξ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        (Set.Ici (0 : ℝ)) := by
    exact
      partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_fixedPairMixedOrder
        (d := d) (n := n) (m := m) (Φ := φ.conjTensorProduct ψ) (F := F)
        hrepr r tSlice hnonnegAway ξ
  have hy_nonneg : 0 ≤ y r 0 := hy_region r
  have hEval_nonneg : y r 0 + t ∈ Set.Ici (0 : ℝ) := by
    exact add_nonneg hy_nonneg (le_of_lt ht)
  exact hsliceEq hEval_nonneg

/-- Exact lower weighted raw scalarization contract beneath the fixed-time
shell-to-slice seam: for the actual one-variable mixed-order slice Schwartz
function, the horizontal `ψ_Z` kernel pairing at
`w = (y r 0 + t) + ε i` collapses to the raw slice value at `y r 0 + t`
multiplied by the built-in damping factor
`exp(-(2π ε)(y r 0 + t))`.

This is the first honest scalar theorem under the current seam. It does not yet
identify that kernel scalar with the descended Section-4.3 pairing; it only
lands the weighted raw slice-value contract that remains after the already-
landed opposite-pairing normalization and Fourier inversion steps. -/
private theorem section43_fixedPair_mixedOrderSlice_weightedRawScalarKernel_fixedTime
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (t ε : ℝ) (hε : 0 < ε) :
    let F :=
      OSReconstruction.FixedPairMixedOrderComponent.ofConjTensorProduct
        (d := d) (n := n) (m := m) f hf_ord g hg_ord
    let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
    let tSlice : NPointDomain d (n + m) → Fin (n + m) → ℝ := fun y i =>
      if hi : i.1 < n then
        y i 0
      else if hir : i = r then
        0
      else
        y i 0 + t
    let ξ : NPointDomain d (n + m) → EuclideanSpace ℝ (Fin (n + m) × Fin d) := fun y =>
      (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
        (fun p => y p.1 (Fin.succ p.2))
    ∀ y : NPointDomain d (n + m),
      (hs : 0 ≤ y r 0 + t) →
      (∫ x : ℝ,
        SCV.psiZ
            (((2 * Real.pi : ℂ) * ((x : ℂ) + ε * Complex.I)))
            (y r 0 + t) *
          (SchwartzMap.fourierTransformCLM ℂ
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
              F.1 r (tSlice y) (ξ y))) x) =
        Complex.exp (-(2 * Real.pi * ε : ℂ) * (y r 0 + t)) *
          ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
            F.1 r (tSlice y) (ξ y) : SchwartzMap ℝ ℂ) (y r 0 + t)) := by
  intro F r tSlice ξ y hs
  let fSlice : SchwartzMap ℝ ℂ :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m) F.1 r (tSlice y) (ξ y)
  let φ : SchwartzMap ℝ ℂ := (SchwartzMap.fourierTransformCLM ℂ) fSlice
  have hpair :
      (∫ x : ℝ,
        SCV.psiZ (((2 * Real.pi : ℂ) * ((x : ℂ) + ε * Complex.I))) (y r 0 + t) * φ x) =
        SCV.smoothCutoff (y r 0 + t) *
          Complex.exp (-(2 * Real.pi * ε : ℂ) * (y r 0 + t)) *
          FourierTransform.fourierInv φ (y r 0 + t) := by
    simpa [φ] using
      (SCV.psiZ_twoPi_pairing_formula
        (φ := (SchwartzMap.fourierTransformCLM ℂ fSlice))
        (η := ε) (ξ := y r 0 + t))
  have hcut : (SCV.smoothCutoff (y r 0 + t) : ℂ) = 1 := by
    exact_mod_cast SCV.smoothCutoff_one_of_nonneg hs
  have hInv :
      FourierTransform.fourierInv φ (y r 0 + t) = fSlice (y r 0 + t) := by
    simpa [φ, fSlice] using
      congrArg (fun ψ : SchwartzMap ℝ ℂ => ψ (y r 0 + t))
        (FourierTransform.fourierInv_fourier_eq fSlice)
  calc
    (∫ x : ℝ,
      SCV.psiZ (((2 * Real.pi : ℂ) * ((x : ℂ) + ε * Complex.I))) (y r 0 + t) * φ x)
        =
      SCV.smoothCutoff (y r 0 + t) *
        Complex.exp (-(2 * Real.pi * ε : ℂ) * (y r 0 + t)) *
        FourierTransform.fourierInv φ (y r 0 + t) := hpair
    _ =
      Complex.exp (-(2 * Real.pi * ε : ℂ) * (y r 0 + t)) * fSlice (y r 0 + t) := by
      rw [hcut, hInv]
      simp
    _ =
      Complex.exp (-(2 * Real.pi * ε : ℂ) * (y r 0 + t)) *
        ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
          F.1 r (tSlice y) (ξ y) : SchwartzMap ℝ ℂ) (y r 0 + t)) := by
      simp [fSlice]

/-- Honest lower theorem beneath the fixed-time mixed-order scalarization seam:
the mixed-order frozen slice already has the expected one-variable Section-4.3
descended `ψ_Z` scalar at the upper-half-plane point
`w = (y r 0 + t) + ε i`.

This theorem does not yet identify that descended scalar with the raw slice
evaluation at `y r 0 + t`; it only packages the part of the contract that is
actually supplied by the existing one-sided-support and quotient-descended
pairing infrastructure. -/
private theorem section43_fixedPair_mixedOrderSliceCanonicalExtension_descendedScalar_fixedTime
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (t ε : ℝ) (ht : 0 < t) (hε : 0 < ε) :
    let F :=
      OSReconstruction.FixedPairMixedOrderComponent.ofConjTensorProduct
        (d := d) (n := n) (m := m) f hf_ord g hg_ord
    let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
    let tSlice : NPointDomain d (n + m) → Fin (n + m) → ℝ := fun y i =>
      if hi : i.1 < n then
        y i 0
      else if hir : i = r then
        0
      else
        y i 0 + t
    let ξ : NPointDomain d (n + m) → EuclideanSpace ℝ (Fin (n + m) × Fin d) := fun y =>
      (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
        (fun p => y p.1 (Fin.succ p.2))
    ∀ y : NPointDomain d (n + m),
      (hnonnegAway : ∀ i : Fin (n + m), i ≠ r → 0 ≤ tSlice y i) →
      SCV.fourierLaplaceExt
          (fourierInvPairingCLM
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
              F.1 r (tSlice y) (ξ y)))
          (((2 * Real.pi : ℂ) * (((y r 0 + t : ℂ) + ε * Complex.I))))
          (by
            simpa [Complex.mul_im, add_comm, add_left_comm, add_assoc]
              using mul_pos Real.two_pi_pos hε) =
        OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          (fourierInvPairingCLM
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
              F.1 r (tSlice y) (ξ y)))
          (fourierInvPairing_hasOneSidedFourierSupport
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
              F.1 r (tSlice y) (ξ y))
            (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_fixedPairMixedOrder
              (d := d) F r (tSlice y) hnonnegAway
              (ξ y)))
          (section43PositiveEnergyQuotientMap1D
            (SCV.schwartzPsiZ
              (((2 * Real.pi : ℂ) * (((y r 0 + t : ℂ) + ε * Complex.I))))
              (by
                simpa [Complex.mul_im, add_comm, add_left_comm, add_assoc]
                  using mul_pos Real.two_pi_pos hε))) := by
  intro F r tSlice ξ y hnonnegAway
  rw [SCV.fourierLaplaceExt_eq]
  symm
  exact
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply
      (T := fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
          F.1 r (tSlice y) (ξ y)))
      (hT_supp := fourierInvPairing_hasOneSidedFourierSupport
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
          F.1 r (tSlice y) (ξ y))
        (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_fixedPairMixedOrder
          (d := d) F r (tSlice y) hnonnegAway (ξ y)))
      (f := SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (((y r 0 + t : ℂ) + ε * Complex.I))))
        (by
          simpa [Complex.mul_im, add_comm, add_left_comm, add_assoc]
            using mul_pos Real.two_pi_pos hε))

/-- Exact lower normal form immediately beneath the fixed-time descended-scalar
slice theorem: the Section-4.3 descended pairing on the actual mixed-order
slice at `w = (y r 0 + t) + ε i` is already the direct one-variable `ψ_w`
pairing against that slice itself.

This is strictly lower than the still-missing bridge to the weighted-raw
evaluation scalar. It only removes the quotient/`fourierLaplaceExt` packaging
from the descended side. -/
private theorem section43_fixedPair_mixedOrderSlice_descendedScalar_eq_directPsiIntegral_fixedTime
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (t ε : ℝ) (ht : 0 < t) (hε : 0 < ε) :
    let F :=
      OSReconstruction.FixedPairMixedOrderComponent.ofConjTensorProduct
        (d := d) (n := n) (m := m) f hf_ord g hg_ord
    let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
    let tSlice : NPointDomain d (n + m) → Fin (n + m) → ℝ := fun y i =>
      if hi : i.1 < n then
        y i 0
      else if hir : i = r then
        0
      else
        y i 0 + t
    let ξ : NPointDomain d (n + m) → EuclideanSpace ℝ (Fin (n + m) × Fin d) := fun y =>
      (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
        (fun p => y p.1 (Fin.succ p.2))
    ∀ y : NPointDomain d (n + m),
      (hnonnegAway : ∀ i : Fin (n + m), i ≠ r → 0 ≤ tSlice y i) →
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          (fourierInvPairingCLM
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
              F.1 r (tSlice y) (ξ y)))
          (fourierInvPairing_hasOneSidedFourierSupport
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
              F.1 r (tSlice y) (ξ y))
            (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_fixedPairMixedOrder
              (d := d) F r (tSlice y) hnonnegAway
              (ξ y)))
          (section43PositiveEnergyQuotientMap1D
            (SCV.schwartzPsiZ
              (((2 * Real.pi : ℂ) * (((y r 0 + t : ℂ) + ε * Complex.I))))
              (by
                simpa [Complex.mul_im, add_comm, add_left_comm, add_assoc]
                  using mul_pos Real.two_pi_pos hε))) =
        ∫ s : ℝ,
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
            F.1 r (tSlice y) (ξ y)) s *
            SCV.psiZ
              (((2 * Real.pi : ℂ) * (((y r 0 + t : ℂ) + ε * Complex.I))))
              s := by
  intro F r tSlice ξ y hnonnegAway
  let fSlice : SchwartzMap ℝ ℂ :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
      F.1 r (tSlice y) (ξ y)
  let ψw : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (((y r 0 + t : ℂ) + ε * Complex.I))))
      (by
        simpa [Complex.mul_im, add_comm, add_left_comm, add_assoc]
          using mul_pos Real.two_pi_pos hε)
  have hApply :
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          (fourierInvPairingCLM fSlice)
          (fourierInvPairing_hasOneSidedFourierSupport
            fSlice
            (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_fixedPairMixedOrder
              (d := d) F r (tSlice y) hnonnegAway (ξ y)))
          (section43PositiveEnergyQuotientMap1D ψw) =
        fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) ψw) := by
    simpa [fSlice, ψw] using
      (OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply
        (T := fourierInvPairingCLM fSlice)
        (hT_supp := fourierInvPairing_hasOneSidedFourierSupport
          fSlice
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_fixedPairMixedOrder
            (d := d) F r (tSlice y) hnonnegAway (ξ y)))
        (f := ψw))
  have hInv :
      FourierTransform.fourierInv ((SchwartzMap.fourierTransformCLM ℂ) ψw) = ψw := by
    simpa [ψw] using (FourierTransform.fourierInv_fourier_eq ψw)
  calc
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (fourierInvPairingCLM fSlice)
        (fourierInvPairing_hasOneSidedFourierSupport
          fSlice
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_fixedPairMixedOrder
            (d := d) F r (tSlice y) hnonnegAway (ξ y)))
        (section43PositiveEnergyQuotientMap1D ψw)
      = fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) ψw) := hApply
    _ = ∫ s : ℝ, fSlice s * ψw s := by
      rw [fourierInvPairingCLM_apply, SchwartzMap.integral_fourierInv_mul_eq]
      rw [hInv]
    _ = ∫ s : ℝ,
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
            F.1 r (tSlice y) (ξ y)) s *
            SCV.psiZ
              (((2 * Real.pi : ℂ) * (((y r 0 + t : ℂ) + ε * Complex.I))))
              s := by
      simp [fSlice, ψw]


/-- Exact earlier blocker beneath the fixed-time shell-limit theorem:
for fixed positive real `t`, identify the boundary-value target already
produced by the canonical ambient shell with the semigroup-side holomorphic
matrix element on the same ambient/preimage inputs.

Once this fixed-time value identification is available, the shell-limit theorem
below is immediate by rewriting the target of
`tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`. -/
/-
Bounded-pass seam note (2026-04-13).

The exact intended theorem immediately below this value equality is no longer
the whole fixed-`ε` shell assembly theorem

`section43_fixedPair_shellToSlice_assembledScalar_fixedTime`

itself. Source-first, the branch has now been sharpened one notch lower: the
first missing theorem strictly beneath this value equality is the pointwise-in-
`y` fixed-time scalarization theorem tentatively of shape

`section43_fixedPair_shellToSlice_integrand_descendedScalar_fixedTime`.

That theorem has not yet landed honestly on the current branch. Its exact
already-supported feeder chain is still the frozen-slice transport cluster:

`section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
-> `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
-> `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
-> `section43_iteratedSlice_descendedPairing`.

Those theorems are the last source-backed transport statements beneath the local
seam `hlimit_os`; none of them yet rewrites the canonical ambient shell
integrand at fixed `t > 0`, `ε > 0`, and support point `y` into the explicit
descended slice scalar evaluated at
`w = ((y r 0 + t : ℂ) + ε * Complex.I)`. Any smaller theorem inserted here
must therefore perform that genuine pointwise shell-to-slice scalarization, not
just wrap one frozen-slice equality.
-/
private theorem section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩)
    (t : ℝ) (ht : 0 < t) :
    bvt_W OS lgc (n + m)
      (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) := by
  have hlimit_w :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)))) := by
    exact
      tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue
        (d := d) (OS := OS) (lgc := lgc) (hm := hm) (φ := φ) (ψ := ψ) (t := t)
  have hlimit_os :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ))) := by
    let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
    let tSlice : NPointDomain d (n + m) → Fin (n + m) → ℝ := fun y i =>
      if hi : i.1 < n then
        y i 0
      else if hir : i = r then
        0
      else
        y i 0 + t
    let ξ : NPointDomain d (n + m) → EuclideanSpace ℝ (Fin (n + m) × Fin d) := fun y =>
      (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
        (fun p => y p.1 (Fin.succ p.2))
    have hshellToSlice :
        ∀ ε : ℝ, ∀ y : NPointDomain d (n + m),
          y ∈ tsupport
            (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
              NPointDomain d (n + m) → ℂ)) →
          (∀ i : Fin (n + m), i ≠ r → 0 ≤ tSlice y i) ∧
            ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
                (φ.conjTensorProduct ψ) r (tSlice y) (ξ y) : SchwartzMap ℝ ℂ)
                (y r 0 + t) =
              OSReconstruction.partialFourierSpatial_fun (d := d) (n := n + m)
                (φ.conjTensorProduct ψ)
                ((fun i =>
                    ((xiShift r 0
                        (fun k μ =>
                          ↑(y k μ) +
                            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                              Complex.I)
                        (t : ℂ)) i 0).re),
                  (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).symm
                    (fun p =>
                ((xiShift r 0
                    (fun k μ =>
                      ↑(y k μ) +
                        ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                          Complex.I)
                    (t : ℂ)) p.1 (Fin.succ p.2)).re))) := by
      intro ε y hy
      have hy_region : y ∈ section43PositiveEnergyRegion d (n + m) := by
        intro i
        exact
          section43_fixedPair_nonnegTimeCoords_of_mem_tsupport_conjTensorProduct
            (d := d) (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) hy i
      simpa [r, tSlice, ξ] using
        section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion
          (d := d) (hm := hm) (Φ := φ.conjTensorProduct ψ)
          (y := y) (t := t) (ε := ε) (ht := le_of_lt ht) hy_region
    have hsliceTransport :
        ∀ y : NPointDomain d (n + m),
          y ∈ tsupport
            (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
              NPointDomain d (n + m) → ℂ)) →
          ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
              (φ.conjTensorProduct ψ) r (tSlice y) (ξ y) : SchwartzMap ℝ ℂ)
              (y r 0 + t)) =
            ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n + m)
              (OSReconstruction.FixedPairMixedOrderComponent.ofConjTensorProduct
                (d := d) (n := n) (m := m) f hf_ord g hg_ord).1
                r (tSlice y) (ξ y) : SchwartzMap ℝ ℂ) (y r 0 + t)) := by
      intro y hy
      have hy_region : y ∈ section43PositiveEnergyRegion d (n + m) := by
        intro i
        exact
          section43_fixedPair_nonnegTimeCoords_of_mem_tsupport_conjTensorProduct
            (d := d) (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) hy i
      simpa [r, tSlice, ξ] using
        section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion
          (d := d) (hm := hm) (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
          (g := g) (hg_ord := hg_ord) (hφf := hφf) (hψg := hψg)
          (y := y) (t := t) (ht := ht) hy_region
    have hweightEqOnSource :
        ∀ y : NPointDomain d (n + m),
          y ∈ tsupport
            (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
              NPointDomain d (n + m) → ℂ)) →
          (φ.conjTensorProduct ψ) y = (f.conjTensorProduct g) y := by
      intro y hy
      exact
        section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_source_tsupport
          (d := d) (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
          (g := g) (hg_ord := hg_ord) (hφf := hφf) (hψg := hψg) hy
    /-
    Exact bounded-pass verdict.

    The older transport-level blocker note here is now stale on the branch.
    The mixed-order total-arity source and its first fixed-time transport
    consumers are already landed:

    `FixedPairMixedOrderTimeRegion`,
    `FixedPairMixedOrderComponent.ofConjTensorProduct`,
    `partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_fixedPairMixedOrder`,
    `section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_fixedPairMixedOrder`,
    and
    `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_fixedPairMixedOrder`.

    So the first exact lower blocker beneath `hlimit_os` is no longer the false
    whole-shell ordered-support target for `f.conjTensorProduct g`.

    The new fixed-time transport step is now consumed directly in this proof:
    after the canonical realization `hshellToSlice`, `hsliceTransport` rewrites
    the ambient frozen slice value to the mixed-order source slice value using
    `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime`.

    The older pointwise scalar-bridge note here is now too optimistic.
    After `hshellToSlice` and `hsliceTransport`, the branch still only knows a
    raw mixed-order frozen-slice value

    `(partialFourierSpatial_timeSliceSchwartz ... F.1 ...
      : SchwartzMap ℝ ℂ) (y r 0 + t)`,

    while the already-landed descended theorem

    `section43_fixedPair_mixedOrderSlice_descendedScalar_eq_directPsiIntegral_fixedTime`

    reaches the different scalar

    `∫ s : ℝ,
      (partialFourierSpatial_timeSliceSchwartz ... F.1 r (tSlice y) (ξ y)) s *
        SCV.psiZ (((2 * Real.pi : ℂ) * (((y r 0 + t : ℂ) + ε * Complex.I)))) s`.

    For generic positive-time slices these are not equal pointwise in `ε`: the
    direct `psiZ` scalar is the one-variable Fourier-Laplace value of the
    slice, while the raw value above is a weighted point evaluation. So the
    formerly advertised pointwise bridge

    `section43_fixedPair_shellToSlice_integrand_descendedScalar_fixedTime`

    is not an honest next theorem surface in this form.

    Exact current source-backed feeder chain:

    `section43_fixedPair_canonicalShell_sliceRealization`
    ->
    `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime`
    ->
    `section43PositiveEnergyQuotientMap_conjTensorProduct_eq_of_repr_eq_transport`
    ->
    `section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_fixedPairMixedOrder`
    ->
    `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_fixedPairMixedOrder`
    ->
    `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
    ->
    `section43_iteratedSlice_descendedPairing`.

    The remaining mismatch is sharper than the old scalar-only note.
    On the current branch one can now test the actual ambient-vs-source shell
    difference

    `bvt_F ... (xiShift ...) * (((φ.conjTensorProduct ψ) - (f.conjTensorProduct g)) y)`

    by the honest three-way decomposition on the live shell domain:

    1. if
       `hy : y ∈ tsupport (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
         NPointDomain d (n + m) → ℂ))`,
       then
       `section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_source_tsupport`
       kills the weight difference;
    2. if
       `hy_region : y ∈ section43PositiveEnergyRegion d (n + m)` and
       `hy_not_source : y ∉ tsupport (((f.conjTensorProduct g :
         SchwartzNPoint d (n + m)) : NPointDomain d (n + m) → ℂ))`,
       then
       `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`
       kills the ambient weight, hence the difference;
    3. but for
       `y ∉ section43PositiveEnergyRegion d (n + m)`,
       source-first inspection finds no existing theorem whose conclusion
       annihilates the live canonical-shell integrand or even rewrites that
       outside-region contribution into a controlled slice scalar.

    So the decomposition fails first in case (3), before any later direct-
    `psiZ` scalar comparison. Equivalently, the first exact remaining lower
    obligation is an honest ambient-domain fixed-time shell comparison input
    for `hlimit_os` that removes the outside-region contribution on the actual
    shell without reviving the false whole-shell ordered-support claim.

    Source-first, the next honest theorem-sized target is a limit-level
    ambient-vs-source shell comparison on the actual current shell, for
    example a theorem of the form

    `Filter.Tendsto
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift r 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (((φ.conjTensorProduct ψ) - (f.conjTensorProduct g)) y))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)`.

    Equivalently, one could prove the same shell has the same limit against
    `(φ.conjTensorProduct ψ)` and against `(f.conjTensorProduct g)`. Either
    way, that is the exact first lower theorem beneath `hlimit_os`; only after
    it lands can the genuine source-shell minus direct-`psiZ` limit be stated
    and proved on the fixed-time source inputs.
    -/
    sorry
  exact tendsto_nhds_unique hlimit_w hlimit_os

/-- Current shell-limit target after moving the blocker one theorem earlier:
for fixed positive real `t`, rewrite the already-landed canonical ambient
boundary-value limit to the semigroup-side holomorphic matrix element. -/
private theorem section43_fixedPair_shellToSlice_limit_osHolomorphicValue_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩)
    (t : ℝ) (ht : 0 < t) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ))) := by
  simpa [section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
    (g := g) (hg_ord := hg_ord) (hφf := hφf) (hψg := hψg)
    (t := t) ht] using
    (tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue
      (d := d) (OS := OS) (lgc := lgc) (hm := hm) (φ := φ) (ψ := ψ) (t := t))

private theorem section43_fixedPair_shellToSlice_limit_fixedTime_value_eq_osHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩)
    (t : ℝ) (ht : 0 < t) :
    Classical.choose
        (section43_fixedPair_shellToSlice_limit_fixedTime
          (d := d) (OS := OS) (lgc := lgc) (hm := hm)
          (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
          (g := g) (hg_ord := hg_ord) (hφf := hφf) (hψg := hψg) t ht)
      =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) := by
  exact tendsto_nhds_unique
    (Classical.choose_spec
      (section43_fixedPair_shellToSlice_limit_fixedTime
        (d := d) (OS := OS) (lgc := lgc) (hm := hm)
        (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
        (g := g) (hg_ord := hg_ord) (hφf := hφf) (hψg := hψg) t ht))
    (section43_fixedPair_shellToSlice_limit_osHolomorphicValue_fixedTime
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
      (g := g) (hg_ord := hg_ord) (hφf := hφf) (hψg := hψg)
      (t := t) ht)

theorem section43_fixedPair_shellToSlice_limit_upperHalfPlaneWitness_fixedTime
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩)
    (Hs : ℂ → ℂ)
    (hHs_imag_os :
      ∀ τ : ℝ, 0 < τ →
        Hs ((τ : ℂ) * Complex.I) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord) (τ : ℂ))
    (t : ℝ) (ht : 0 < t) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Hs ((t : ℂ) * Complex.I))) := by
  rw [hHs_imag_os t ht]
  exact
    section43_fixedPair_shellToSlice_limit_osHolomorphicValue_fixedTime
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (f := f) (hf_ord := hf_ord)
      (g := g) (hg_ord := hg_ord) (hφf := hφf) (hψg := hψg) (t := t) ht

/-- Semigroup-side fixed-pair scalarization already available above the live
fixed-time shell seam. It packages only the upper-half-plane OS matrix element;
it does not discharge the ambient transport-backed shell limit. -/
theorem section43_fixedPair_upperHalfPlaneScalarization
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n ⟨f, hf_ord⟩)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m ⟨g, hg_ord⟩) :
    ∃ Hs : ℂ → ℂ,
      DifferentiableOn ℂ Hs SCV.upperHalfPlane ∧
      (∀ τ : ℝ, 0 < τ →
        Hs ((τ : ℂ) * Complex.I) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord) (τ : ℂ)) := by
  refine ⟨fun w =>
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (-Complex.I * w),
    ?_, ?_⟩
  · exact differentiableOn_rotated_OSInnerProductTimeShiftHolomorphicValue
      (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n f hf_ord)
      (PositiveTimeBorchersSequence.single m g hg_ord)
  · intro τ hτ
    change
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (-Complex.I * ((τ : ℂ) * Complex.I)) =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (τ : ℂ)
    congr 1
    calc
      -Complex.I * ((τ : ℂ) * Complex.I)
          = ((-Complex.I) * Complex.I) * (τ : ℂ) := by ring
      _ = (1 : ℂ) * (τ : ℂ) := by simp [Complex.I_mul_I]
      _ = (τ : ℂ) := by ring

/-- Exact downstream bridge out of the fixed-pair scalarization seam: once the
Section-4.3 assembly provides an upper-half-plane scalar `Hs` with the required
positive-imaginary-axis OS identification, rotating by `z ↦ z * I` produces the
right-half-plane witness shape consumed later by
`one_variable_time_interchange_for_wightman_pairing`. -/
private theorem rightHalfPlaneWitness_of_upperHalfPlaneScalarization
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (Hs : ℂ → ℂ)
    (hHs_holo : DifferentiableOn ℂ Hs SCV.upperHalfPlane)
    (hHs_imag_os :
      ∀ τ : ℝ, 0 < τ →
        Hs ((τ : ℂ) * Complex.I) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord) (τ : ℂ)) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ)) := by
  refine ⟨fun z => Hs (z * Complex.I), ?_, ?_⟩
  · have hmap : Set.MapsTo (fun z : ℂ => z * Complex.I)
        {z : ℂ | 0 < z.re} SCV.upperHalfPlane := by
      intro z hz
      simpa [SCV.upperHalfPlane, Complex.mul_im] using hz
    have hmul :
        DifferentiableOn ℂ (fun z : ℂ => z * Complex.I) {z : ℂ | 0 < z.re} := by
      intro z hz
      simpa using
        (((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z).mul_const
          Complex.I).differentiableWithinAt)
    exact hHs_holo.comp hmul hmap
  · intro t ht
    simpa [mul_comm] using hHs_imag_os t ht

/-- The honest OS Hilbert-space vector determined by a positive-time Euclidean
Borchers sequence. Package I will later define the Minkowski-side transport map
by choosing a Euclidean preimage and landing in this existing vector. -/
noncomputable def positiveTimeBorchersVector
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    OSHilbertSpace OS :=
  (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))

@[simp] theorem positiveTimeBorchersVector_inner_eq
    (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) :
    @inner ℂ (OSHilbertSpace OS) _ (positiveTimeBorchersVector (d := d) OS F)
      (positiveTimeBorchersVector (d := d) OS G) =
      PositiveTimeBorchersSequence.osInner OS F G := by
  change @inner ℂ (OSHilbertSpace OS) _
      (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
      (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS)) =
      PositiveTimeBorchersSequence.osInner OS F G
  rw [UniformSpace.Completion.inner_coe]
  simp [OSPreHilbertSpace.inner_eq]

@[simp] theorem positiveTimeBorchersVector_norm_sq_eq
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    ‖positiveTimeBorchersVector (d := d) OS F‖ ^ 2 =
      (PositiveTimeBorchersSequence.osInner OS F F).re := by
  have hnorm :
      RCLike.re
        (@inner ℂ (OSHilbertSpace OS) _ (positiveTimeBorchersVector (d := d) OS F)
          (positiveTimeBorchersVector (d := d) OS F)) =
        ‖positiveTimeBorchersVector (d := d) OS F‖ ^ 2 := by
    simpa using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (positiveTimeBorchersVector (d := d) OS F))
  rw [← hnorm, positiveTimeBorchersVector_inner_eq]
  simp

theorem positiveTimeBorchersVector_self_nonneg
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    0 ≤ ‖positiveTimeBorchersVector (d := d) OS F‖ ^ 2 := by
  rw [positiveTimeBorchersVector_norm_sq_eq]
  exact PositiveTimeBorchersSequence.osInner_nonneg_self OS F

/-- The positive-time Borchers vectors are dense in the completed OS Hilbert
space. This is the honest density input later used in Package I: it comes
for free from the quotient-completion construction and does not rely on any
Schwartz-space density theorem. -/
theorem positiveTimeBorchersVector_dense
    (OS : OsterwalderSchraderAxioms d) :
    Dense (Set.range (positiveTimeBorchersVector (d := d) OS)) := by
  have hrange :
      Set.range (positiveTimeBorchersVector (d := d) OS) =
        Set.range ((↑) : OSPreHilbertSpace OS → OSHilbertSpace OS) := by
    ext x
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨(⟦F⟧ : OSPreHilbertSpace OS), rfl⟩
    · rintro ⟨xpre, rfl⟩
      induction xpre using Quotient.inductionOn with
      | h F =>
          exact ⟨F, rfl⟩
  rw [hrange]
  exact UniformSpace.Completion.denseRange_coe

private theorem positiveTimeBorchersVector_eq_sum_single_vectors
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    positiveTimeBorchersVector (d := d) OS F =
      ∑ k ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
        positiveTimeBorchersVector (d := d) OS
          (PositiveTimeBorchersSequence.single k
            (((F : BorchersSequence d).funcs k)) (F.ordered_tsupport k)) := by
  unfold positiveTimeBorchersVector
  suffices h : ∀ (s : Finset ℕ) (G : PositiveTimeBorchersSequence d),
      (∀ k, k ∉ s → ((G : BorchersSequence d).funcs k) = 0) →
      (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS)) =
        ∑ k ∈ s,
          (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single k
              (((G : BorchersSequence d).funcs k)) (G.ordered_tsupport k)⟧)) :
            OSHilbertSpace OS)) from
    h (Finset.range (((F : BorchersSequence d).bound) + 1)) F (fun k hk =>
      (F : BorchersSequence d).bound_spec k (by
        simp only [Finset.mem_range, not_lt] at hk
        omega))
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro G hG
      rw [Finset.sum_empty]
      have hpre :
          (⟦G⟧ : OSPreHilbertSpace OS) =
            (⟦(0 : PositiveTimeBorchersSequence d)⟧ : OSPreHilbertSpace OS) := by
        exact OSPreHilbertSpace.mk_eq_of_funcs_eq OS G 0
          (fun k => by simp [hG k (by simp)])
      simpa [UniformSpace.Completion.coe_zero] using
        congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS))) hpre
  | cons a s ha ih =>
      intro G hG
      rw [Finset.sum_cons]
      let G' : PositiveTimeBorchersSequence d := {
        toBorchersSequence := {
          funcs := fun k => if k = a then 0 else ((G : BorchersSequence d).funcs k)
          bound := max ((G : BorchersSequence d).bound) a
          bound_spec := fun k hk => by
            show (if k = a then (0 : SchwartzNPoint d k)
              else (G : BorchersSequence d).funcs k) = 0
            split
            · rfl
            · next _hka => exact (G : BorchersSequence d).bound_spec k (by omega)
        }
        ordered_tsupport := fun k => by
          by_cases hka : k = a
          · intro x hx
            simp [hka] at hx
          · simpa [hka] using G.ordered_tsupport k
      }
      have hG'supp : ∀ k, k ∉ s → ((G' : BorchersSequence d).funcs k) = 0 := by
        intro k hk
        by_cases hka : k = a
        · subst hka
          simp [G']
        · simp [G', hka]
          exact hG k (fun hmem => (Finset.mem_cons.mp hmem).elim hka hk)
      have h_split :
          (⟦G⟧ : OSPreHilbertSpace OS) =
            (⟦(G' + PositiveTimeBorchersSequence.single a
              (((G : BorchersSequence d).funcs a)) (G.ordered_tsupport a))⟧ :
              OSPreHilbertSpace OS) := by
        apply OSPreHilbertSpace.mk_eq_of_funcs_eq OS
        intro k
        simp only [PositiveTimeBorchersSequence.add_toBorchersSequence,
          BorchersSequence.add_funcs, G']
        by_cases hka : k = a
        · subst hka
          simp [BorchersSequence.single_funcs_eq]
        · simp [hka, PositiveTimeBorchersSequence.single_toBorchersSequence]
      have hG'eq :
          (((show OSPreHilbertSpace OS from (⟦G'⟧)) : OSHilbertSpace OS)) =
            ∑ k ∈ s,
              (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single k
                  (((G : BorchersSequence d).funcs k)) (G.ordered_tsupport k)⟧)) :
                OSHilbertSpace OS)) := by
        rw [show ∑ k ∈ s,
              (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single k
                  (((G : BorchersSequence d).funcs k)) (G.ordered_tsupport k)⟧)) :
                OSHilbertSpace OS)) =
            ∑ k ∈ s,
              (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single k
                  (((G' : BorchersSequence d).funcs k)) (G'.ordered_tsupport k)⟧)) :
                OSHilbertSpace OS)) from by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hka : k ≠ a := by
            intro h
            exact ha (by simpa [h] using hk)
          simp [G', hka]]
        exact ih G' hG'supp
      have hcomm :
          (⟦(G' + PositiveTimeBorchersSequence.single a
            (((G : BorchersSequence d).funcs a)) (G.ordered_tsupport a))⟧ :
            OSPreHilbertSpace OS) =
          (⟦(PositiveTimeBorchersSequence.single a
            (((G : BorchersSequence d).funcs a)) (G.ordered_tsupport a) + G')⟧ :
            OSPreHilbertSpace OS) := by
        apply OSPreHilbertSpace.mk_eq_of_funcs_eq OS
        intro k
        simp [BorchersSequence.add_funcs, add_comm]
      rw [h_split, hcomm]
      let xpre : OSPreHilbertSpace OS :=
        ⟦PositiveTimeBorchersSequence.single a
          (((G : BorchersSequence d).funcs a)) (G.ordered_tsupport a)⟧
      let ypre : OSPreHilbertSpace OS := ⟦G'⟧
      change ((xpre + ypre : OSPreHilbertSpace OS) : OSHilbertSpace OS) =
        (xpre : OSHilbertSpace OS) +
          ∑ k ∈ s,
            (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single k
                (((G : BorchersSequence d).funcs k)) (G.ordered_tsupport k)⟧)) :
              OSHilbertSpace OS))
      rw [UniformSpace.Completion.coe_add, hG'eq]

/-- The degree-`n` Section 4.3 quotient-image carrier.

Warning: with the current production definition this is only the range of
`os1TransportComponent`, i.e. positive-time data viewed in the Section-4.3
quotient codomain. Membership in this set is not, by itself, the missing
paper Fourier-Laplace transform and must not be used to prove a Wightman/OS
scalar comparison. The latter still has to pass through an explicit
normal-form/transform theorem. -/
def bvtTransportImage (d n : ℕ) [NeZero d] :
    Set (Section43PositiveEnergyComponent (d := d) n) :=
  Set.range (os1TransportComponent d n)

/-- Additive closure of the transformed image. -/
theorem bvtTransportImage_add
    {n : ℕ} {f g : Section43PositiveEnergyComponent (d := d) n}
    (hf : f ∈ bvtTransportImage (d := d) n)
    (hg : g ∈ bvtTransportImage (d := d) n) :
    f + g ∈ bvtTransportImage (d := d) n := by
  rcases hf with ⟨f₀, rfl⟩
  rcases hg with ⟨g₀, rfl⟩
  exact ⟨f₀ + g₀, by simp [bvtTransportImage]⟩

/-- Scalar closure of the transformed image. -/
theorem bvtTransportImage_smul
    {n : ℕ} {c : ℂ} {f : Section43PositiveEnergyComponent (d := d) n}
    (hf : f ∈ bvtTransportImage (d := d) n) :
    c • f ∈ bvtTransportImage (d := d) n := by
  rcases hf with ⟨f₀, rfl⟩
  exact ⟨c • f₀, by simp [bvtTransportImage]⟩

/-- Finite Borchers data whose every component lies in the Section 4.3
transformed image. This is the honest current-code carrier for the later
on-image transport and Eq. `(4.28)` stages. -/
structure BvtTransportImageSequence (d : ℕ) [NeZero d] where
  toBorchers : BorchersSequence d
  image_mem : ∀ n,
    section43PositiveEnergyQuotientMap (d := d) n (toBorchers.funcs n) ∈
      bvtTransportImage (d := d) n

def positiveTimeBorchersSequence_toBvtTransportImageSequence
    (F : PositiveTimeBorchersSequence d) :
    BvtTransportImageSequence d where
  toBorchers := (F : BorchersSequence d)
  image_mem := fun n => by
    refine ⟨⟨((F : BorchersSequence d).funcs n), F.ordered_tsupport n⟩, ?_⟩
    simp [os1TransportComponent_apply]

instance : Add (BvtTransportImageSequence d) where
  add F G :=
    { toBorchers := F.toBorchers + G.toBorchers
      image_mem := fun n => by
        have hsum :=
            bvtTransportImage_add (d := d)
              (hf := F.image_mem n) (hg := G.image_mem n)
        simpa [BorchersSequence.add_funcs, map_add] using hsum }

instance : SMul ℂ (BvtTransportImageSequence d) where
  smul c F :=
    { toBorchers := c • F.toBorchers
      image_mem := fun n => by
        have hsmul :=
            bvtTransportImage_smul (d := d) (c := c) (hf := F.image_mem n)
        simpa [BorchersSequence.smul_funcs] using hsmul }

@[simp] theorem add_toBorchers
    (F G : BvtTransportImageSequence d) :
    (F + G).toBorchers = F.toBorchers + G.toBorchers := rfl

@[simp] theorem smul_toBorchers
    (c : ℂ) (F : BvtTransportImageSequence d) :
    (c • F).toBorchers = c • F.toBorchers := rfl

noncomputable def euclideanPositiveTimeSingleVector
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n) :
    OSHilbertSpace OS :=
  positiveTimeBorchersVector (d := d) OS
    (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d) f)

@[simp] theorem euclideanPositiveTimeSingleVector_norm_sq_eq
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n) :
    ‖euclideanPositiveTimeSingleVector (d := d) OS f‖ ^ 2 =
      (PositiveTimeBorchersSequence.osInner OS
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d) f)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d) f)).re := by
  simp [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector_norm_sq_eq]

@[simp] theorem euclideanPositiveTimeSingleVector_ofSubmodule_add
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (f g : euclideanPositiveTimeSubmodule (d := d) n) :
    euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule (f + g)) =
      euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule f) +
      euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule g) := by
  have hpre :
      let xfg : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule (f + g))⟧
      let xf : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f)⟧
      let xg : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g)⟧
      xfg = xf + xg := by
    dsimp
    change (Quotient.mk (osBorchersSetoid OS)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule (f + g))) :
          OSPreHilbertSpace OS) =
      (Quotient.mk (osBorchersSetoid OS)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f) +
         EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g)) :
          OSPreHilbertSpace OS)
    apply OSPreHilbertSpace.mk_eq_of_funcs_eq
    intro m
    by_cases hm : m = n
    · subst hm
      simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule, BorchersSequence.add_funcs]
    · simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule,
        PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.add_funcs, hm]
  simpa [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector,
    UniformSpace.Completion.coe_add] using
    congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS))) hpre

@[simp] theorem euclideanPositiveTimeSingleVector_ofSubmodule_smul
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (c : ℂ) (f : euclideanPositiveTimeSubmodule (d := d) n) :
    euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule (c • f)) =
      c • euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule f) := by
  have hpre :
      let xcf : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule (c • f))⟧
      let xf : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f)⟧
      xcf = c • xf := by
    dsimp
    change (Quotient.mk (osBorchersSetoid OS)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule (c • f))) :
          OSPreHilbertSpace OS) =
      (Quotient.mk (osBorchersSetoid OS)
        (c • EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f)) :
          OSPreHilbertSpace OS)
    apply OSPreHilbertSpace.mk_eq_of_funcs_eq
    intro m
    by_cases hm : m = n
    · subst hm
      simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule, BorchersSequence.smul_funcs]
    · simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule,
        PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.smul_funcs, hm]
  simpa [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector,
    UniformSpace.Completion.coe_smul] using
    congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS))) hpre

@[simp] theorem euclideanPositiveTimeSingleVector_ofSubmodule_zero
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} :
    euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule
          (0 : euclideanPositiveTimeSubmodule (d := d) n)) = 0 := by
  have hpre :
      let x0 : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule
            (0 : euclideanPositiveTimeSubmodule (d := d) n))⟧
      x0 = 0 := by
    dsimp
    change (Quotient.mk (osBorchersSetoid OS)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule
            (0 : euclideanPositiveTimeSubmodule (d := d) n))) :
          OSPreHilbertSpace OS) =
      (0 : OSPreHilbertSpace OS)
    apply OSPreHilbertSpace.mk_eq_of_funcs_eq
    intro m
    by_cases hm : m = n
    · subst hm
      simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule]
    · simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule,
        PositiveTimeBorchersSequence.single_toBorchersSequence, hm]
  simpa [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector,
    UniformSpace.Completion.coe_zero] using
    congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS))) hpre

private noncomputable def bvtTransportImagePreimage
    (F : BvtTransportImageSequence d) (n : ℕ) :
    euclideanPositiveTimeSubmodule (d := d) n :=
  Classical.choose (F.image_mem n)

@[simp] private theorem bvtTransportImagePreimage_spec
    (F : BvtTransportImageSequence d) (n : ℕ) :
    os1TransportComponent d n (bvtTransportImagePreimage (d := d) F n) =
      section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n) :=
  Classical.choose_spec (F.image_mem n)

/-- The Section 4.3 Hilbert transport on the transformed-image core. It is
defined by choosing a positive-time Euclidean preimage degreewise and summing
the resulting OS Hilbert vectors over the finite Borchers bound. -/
noncomputable def bvt_transport_to_osHilbert_onImage
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) :
    OSHilbertSpace OS :=
  (Finset.range (F.toBorchers.bound + 1)).sum fun n =>
    euclideanPositiveTimeSingleVector (d := d) OS
      (EuclideanPositiveTimeComponent.ofSubmodule
        (bvtTransportImagePreimage (d := d) F n))

/-- The on-image transport does not depend on which positive-time Euclidean
preimage family is used to represent the transformed-image data. The proof uses
only `os1TransportComponent_injective`, not any density theorem. -/
theorem bvt_transport_to_osHilbert_onImage_wellDefined
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d)
    (g : ∀ n, euclideanPositiveTimeSubmodule (d := d) n)
    (hg : ∀ n,
      os1TransportComponent d n (g n) =
        section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n)) :
    bvt_transport_to_osHilbert_onImage OS F =
      (Finset.range (F.toBorchers.bound + 1)).sum fun n =>
        euclideanPositiveTimeSingleVector (d := d) OS
          (EuclideanPositiveTimeComponent.ofSubmodule (g n)) := by
  unfold bvt_transport_to_osHilbert_onImage
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hpre :
      bvtTransportImagePreimage (d := d) F n = g n := by
    apply os1TransportComponent_injective (d := d) (n := n)
    rw [bvtTransportImagePreimage_spec, hg]
  simp [hpre]

theorem bvt_transport_to_osHilbert_onImage_positiveTime
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    bvt_transport_to_osHilbert_onImage OS
      (positiveTimeBorchersSequence_toBvtTransportImageSequence (d := d) F) =
    positiveTimeBorchersVector (d := d) OS F := by
  let G : BvtTransportImageSequence d :=
    positiveTimeBorchersSequence_toBvtTransportImageSequence (d := d) F
  let g : ∀ n, euclideanPositiveTimeSubmodule (d := d) n :=
    fun n => ⟨((F : BorchersSequence d).funcs n), F.ordered_tsupport n⟩
  have hg : ∀ n,
      os1TransportComponent d n (g n) =
        section43PositiveEnergyQuotientMap (d := d) n (G.toBorchers.funcs n) := by
    intro n
    simp [G, g, positiveTimeBorchersSequence_toBvtTransportImageSequence,
      os1TransportComponent_apply]
  rw [bvt_transport_to_osHilbert_onImage_wellDefined (d := d) (OS := OS)
    (F := G) (g := g) hg]
  simpa [G, g, euclideanPositiveTimeSingleVector, positiveTimeBorchersVector]
    using (positiveTimeBorchersVector_eq_sum_single_vectors (d := d) OS F).symm

/-- The Section 4.3 on-image transport has dense range in the OS Hilbert space:
the positive-time Borchers vectors are dense, and every such vector is the
transport of its componentwise Section 4.3 image. -/
theorem bvt_transport_to_osHilbert_onImage_dense
    (OS : OsterwalderSchraderAxioms d) :
    Dense (Set.range (bvt_transport_to_osHilbert_onImage (d := d) OS)) := by
  refine Dense.mono ?_ (positiveTimeBorchersVector_dense (d := d) OS)
  rintro _ ⟨F, rfl⟩
  exact ⟨positiveTimeBorchersSequence_toBvtTransportImageSequence (d := d) F,
    bvt_transport_to_osHilbert_onImage_positiveTime (d := d) OS F⟩

private theorem bvt_transport_to_osHilbert_onImage_eq_padded_sum
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hm : F.toBorchers.bound ≤ m) :
    bvt_transport_to_osHilbert_onImage OS F =
      (Finset.range (m + 1)).sum fun n =>
        if h : n ≤ F.toBorchers.bound then
          euclideanPositiveTimeSingleVector (d := d) OS
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) F n))
        else 0 := by
  let v : ℕ → OSHilbertSpace OS := fun n =>
    euclideanPositiveTimeSingleVector (d := d) OS
      (EuclideanPositiveTimeComponent.ofSubmodule
        (bvtTransportImagePreimage (d := d) F n))
  unfold bvt_transport_to_osHilbert_onImage
  have hprefix :
      (Finset.range (F.toBorchers.bound + 1)).sum
          (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) =
        (Finset.range (F.toBorchers.bound + 1)).sum v := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hle : n ≤ F.toBorchers.bound := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    simp [v, hle]
  have hmdecomp : m + 1 = (F.toBorchers.bound + 1) + (m - F.toBorchers.bound) := by
    omega
  have htail :
      ((Finset.range (m - F.toBorchers.bound)).sum fun k =>
        if h : F.toBorchers.bound + 1 + k ≤ F.toBorchers.bound then
          v (F.toBorchers.bound + 1 + k)
        else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hnot : ¬ F.toBorchers.bound + 1 + k ≤ F.toBorchers.bound := by
      omega
    simp [v, hnot]
  have hpad :
      (Finset.range (m + 1)).sum
          (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) =
        (Finset.range (F.toBorchers.bound + 1)).sum
          (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) := by
    rw [hmdecomp, Finset.sum_range_add, htail, add_zero]
  calc
    (Finset.range (F.toBorchers.bound + 1)).sum v =
      (Finset.range (F.toBorchers.bound + 1)).sum
        (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) := by
          symm
          exact hprefix
    _ =
      (Finset.range (m + 1)).sum
        (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) := by
          symm
          exact hpad

theorem bvt_transport_to_osHilbert_onImage_add
    (OS : OsterwalderSchraderAxioms d)
    (F G : BvtTransportImageSequence d) :
    bvt_transport_to_osHilbert_onImage OS (F + G) =
      bvt_transport_to_osHilbert_onImage OS F +
      bvt_transport_to_osHilbert_onImage OS G := by
  let m := max F.toBorchers.bound G.toBorchers.bound
  have hfg :
      ∀ n,
        os1TransportComponent d n
            ((if h : n ≤ F.toBorchers.bound then
                bvtTransportImagePreimage (d := d) F n
              else 0) +
              (if h : n ≤ G.toBorchers.bound then
                bvtTransportImagePreimage (d := d) G n
              else 0)) =
          section43PositiveEnergyQuotientMap (d := d) n
            ((F + G).toBorchers.funcs n) := by
    intro n
    have hspecF :
        section43PositiveEnergyQuotientMap (d := d) n
            (bvtTransportImagePreimage (d := d) F n : SchwartzNPoint d n) =
          section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n) := by
      simpa [os1TransportComponent_apply] using
        (bvtTransportImagePreimage_spec (d := d) F n)
    have hspecG :
        section43PositiveEnergyQuotientMap (d := d) n
            (bvtTransportImagePreimage (d := d) G n : SchwartzNPoint d n) =
          section43PositiveEnergyQuotientMap (d := d) n (G.toBorchers.funcs n) := by
      simpa [os1TransportComponent_apply] using
        (bvtTransportImagePreimage_spec (d := d) G n)
    by_cases hF : n ≤ F.toBorchers.bound
    · by_cases hG : n ≤ G.toBorchers.bound
      · simp [hF, hG, add_toBorchers, BorchersSequence.add_funcs, map_add,
          hspecF, hspecG]
      · have hGt : G.toBorchers.bound < n := by omega
        simp [hF, hG, G.toBorchers.bound_spec n hGt, add_toBorchers,
          BorchersSequence.add_funcs, map_add, hspecF]
    · have hFt : F.toBorchers.bound < n := by omega
      by_cases hG : n ≤ G.toBorchers.bound
      · simp [hF, hG, F.toBorchers.bound_spec n hFt, add_toBorchers,
          BorchersSequence.add_funcs, map_add, hspecG]
      · have hGt : G.toBorchers.bound < n := by omega
        simp [hF, hG, F.toBorchers.bound_spec n hFt, G.toBorchers.bound_spec n hGt,
          add_toBorchers, BorchersSequence.add_funcs, map_add]
  rw [bvt_transport_to_osHilbert_onImage_wellDefined (d := d) (OS := OS)
    (F := F + G) (g := fun n =>
      (if h : n ≤ F.toBorchers.bound then
        bvtTransportImagePreimage (d := d) F n
      else 0) +
      (if h : n ≤ G.toBorchers.bound then
        bvtTransportImagePreimage (d := d) G n
      else 0)) hfg]
  rw [bvt_transport_to_osHilbert_onImage_eq_padded_sum (d := d) (OS := OS)
    (F := F) (m := m) (by
      dsimp [m]
      exact le_max_left _ _)]
  rw [bvt_transport_to_osHilbert_onImage_eq_padded_sum (d := d) (OS := OS)
    (F := G) (m := m) (by
      dsimp [m]
      exact le_max_right _ _)]
  dsimp [m]
  have hsum :
      (Finset.range (max F.toBorchers.bound G.toBorchers.bound + 1)).sum
          (fun n =>
            euclideanPositiveTimeSingleVector (d := d) OS
              (EuclideanPositiveTimeComponent.ofSubmodule
                ((if h : n ≤ F.toBorchers.bound then
                    bvtTransportImagePreimage (d := d) F n
                  else 0) +
                  if h : n ≤ G.toBorchers.bound then
                    bvtTransportImagePreimage (d := d) G n
                  else 0))) =
        (Finset.range (max F.toBorchers.bound G.toBorchers.bound + 1)).sum
            (fun n =>
              (if h : n ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n))
              else 0) +
              if h : n ≤ G.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) G n))
              else 0) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    by_cases hF : n ≤ F.toBorchers.bound
    · by_cases hG : n ≤ G.toBorchers.bound
      · simp [hF, hG, euclideanPositiveTimeSingleVector_ofSubmodule_add]
      · simp [hF, hG, euclideanPositiveTimeSingleVector_ofSubmodule_add,
          euclideanPositiveTimeSingleVector_ofSubmodule_zero]
    · by_cases hG : n ≤ G.toBorchers.bound
      · simp [hF, hG, euclideanPositiveTimeSingleVector_ofSubmodule_add,
          euclideanPositiveTimeSingleVector_ofSubmodule_zero]
      · simp [hF, hG, euclideanPositiveTimeSingleVector_ofSubmodule_add,
          euclideanPositiveTimeSingleVector_ofSubmodule_zero]
  calc
    (Finset.range (max F.toBorchers.bound G.toBorchers.bound + 1)).sum
        (fun n =>
          euclideanPositiveTimeSingleVector (d := d) OS
            (EuclideanPositiveTimeComponent.ofSubmodule
              ((if n ≤ F.toBorchers.bound then
                  bvtTransportImagePreimage (d := d) F n
                else 0) +
                if n ≤ G.toBorchers.bound then
                  bvtTransportImagePreimage (d := d) G n
                else 0))) =
      (Finset.range (max F.toBorchers.bound G.toBorchers.bound + 1)).sum
        (fun n =>
          (if h : n ≤ F.toBorchers.bound then
            euclideanPositiveTimeSingleVector (d := d) OS
              (EuclideanPositiveTimeComponent.ofSubmodule
                (bvtTransportImagePreimage (d := d) F n))
          else 0) +
          if h : n ≤ G.toBorchers.bound then
            euclideanPositiveTimeSingleVector (d := d) OS
              (EuclideanPositiveTimeComponent.ofSubmodule
                (bvtTransportImagePreimage (d := d) G n))
          else 0) := hsum
    _ = _ := by
      rw [Finset.sum_add_distrib]
      rfl

theorem bvt_transport_to_osHilbert_onImage_smul
    (OS : OsterwalderSchraderAxioms d)
    (c : ℂ) (F : BvtTransportImageSequence d) :
    bvt_transport_to_osHilbert_onImage OS (c • F) =
      c • bvt_transport_to_osHilbert_onImage OS F := by
  have hF :
      ∀ n,
        os1TransportComponent d n (c • bvtTransportImagePreimage (d := d) F n) =
          section43PositiveEnergyQuotientMap (d := d) n
            ((c • F).toBorchers.funcs n) := by
    intro n
    rw [map_smul, bvtTransportImagePreimage_spec]
    simp [smul_toBorchers, BorchersSequence.smul_funcs]
  rw [bvt_transport_to_osHilbert_onImage_wellDefined (d := d) (OS := OS)
    (F := c • F) (g := fun n => c • bvtTransportImagePreimage (d := d) F n) hF]
  simp [bvt_transport_to_osHilbert_onImage, Finset.smul_sum,
    euclideanPositiveTimeSingleVector_ofSubmodule_smul]

private theorem inner_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (OS : OsterwalderSchraderAxioms d)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m) :
    @inner ℂ (OSHilbertSpace OS) _
        (bvt_transport_to_osHilbert_onImage OS F)
        (bvt_transport_to_osHilbert_onImage OS G) =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          @inner ℂ (OSHilbertSpace OS) _
            (if h : n ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F n))
            else 0)
            (if h : k ≤ G.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) G k))
            else 0) := by
  rw [bvt_transport_to_osHilbert_onImage_eq_padded_sum (d := d) (OS := OS)
      (F := F) (m := m) hFm]
  rw [bvt_transport_to_osHilbert_onImage_eq_padded_sum (d := d) (OS := OS)
      (F := G) (m := m) hGm]
  rw [sum_inner]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [inner_sum]

private theorem norm_sq_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) :
    ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 =
      ((Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          @inner ℂ (OSHilbertSpace OS) _
            (if h : n ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F n))
            else 0)
            (if h : k ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F k))
            else 0)).re := by
  have hnorm :
      RCLike.re
        (@inner ℂ (OSHilbertSpace OS) _
          (bvt_transport_to_osHilbert_onImage OS F)
          (bvt_transport_to_osHilbert_onImage OS F)) =
        ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 := by
    simpa using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (bvt_transport_to_osHilbert_onImage OS F))
  rw [← hnorm, inner_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (d := d) (OS := OS) (F := F) (G := F) (m := m) hFm hFm]
  have houter :
      RCLike.re
          ((Finset.range (m + 1)).sum fun n =>
            (Finset.range (m + 1)).sum fun k =>
              @inner ℂ (OSHilbertSpace OS) _
                (if h : n ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F n))
                else 0)
                (if h : k ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F k))
                else 0)) =
        (Finset.range (m + 1)).sum fun n =>
          RCLike.re
            ((Finset.range (m + 1)).sum fun k =>
              @inner ℂ (OSHilbertSpace OS) _
                (if h : n ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F n))
                else 0)
                (if h : k ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F k))
                else 0)) := by
    simpa using
      (Complex.re_sum (s := Finset.range (m + 1))
        (f := fun n =>
          (Finset.range (m + 1)).sum fun k =>
            @inner ℂ (OSHilbertSpace OS) _
              (if h : n ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n))
              else 0)
              (if h : k ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F k))
              else 0)))
  rw [houter]
  have hinner :
      ∀ n,
        RCLike.re
            ((Finset.range (m + 1)).sum fun k =>
              @inner ℂ (OSHilbertSpace OS) _
                (if h : n ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F n))
                else 0)
                (if h : k ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F k))
                else 0)) =
          (Finset.range (m + 1)).sum fun k =>
            (@inner ℂ (OSHilbertSpace OS) _
              (if h : n ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n))
              else 0)
              (if h : k ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F k))
              else 0)).re := by
    intro n
    simpa using
      (Complex.re_sum (s := Finset.range (m + 1))
        (f := fun k =>
          @inner ℂ (OSHilbertSpace OS) _
            (if h : n ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F n))
            else 0)
            (if h : k ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F k))
            else 0)))
  simpa [hinner]

private theorem inner_euclideanPositiveTimeSingleVector_ofSubmodule_eq_osInner
    (OS : OsterwalderSchraderAxioms d)
    {n k : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) k) :
    @inner ℂ (OSHilbertSpace OS) _
        (euclideanPositiveTimeSingleVector (d := d) OS
          (EuclideanPositiveTimeComponent.ofSubmodule f))
        (euclideanPositiveTimeSingleVector (d := d) OS
          (EuclideanPositiveTimeComponent.ofSubmodule g)) =
      PositiveTimeBorchersSequence.osInner OS
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f))
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g)) := by
  simp [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector_inner_eq]

private theorem inner_bvt_transport_to_osHilbert_onImage_eq_osInner_padded_double_sum
    (OS : OsterwalderSchraderAxioms d)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m) :
    @inner ℂ (OSHilbertSpace OS) _
        (bvt_transport_to_osHilbert_onImage OS F)
        (bvt_transport_to_osHilbert_onImage OS G) =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ G.toBorchers.bound then
              PositiveTimeBorchersSequence.osInner OS
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n)))
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) G k)))
            else 0
          else 0 := by
  rw [inner_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (d := d) (OS := OS) (F := F) (G := G) (m := m) hFm hGm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ G.toBorchers.bound
    · simp [h₁, h₂,
        inner_euclideanPositiveTimeSingleVector_ofSubmodule_eq_osInner]
    · simp [h₁, h₂]
  · simp [h₁]

private theorem norm_sq_bvt_transport_to_osHilbert_onImage_eq_osInner_padded_double_sum
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) :
    ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 =
      ((Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              PositiveTimeBorchersSequence.osInner OS
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n)))
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F k)))
            else 0
          else 0).re := by
  rw [norm_sq_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (d := d) (OS := OS) (F := F) (m := m) hFm]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ F.toBorchers.bound
    · simp [h₁, h₂,
        inner_euclideanPositiveTimeSingleVector_ofSubmodule_eq_osInner]
    · simp [h₁, h₂]
  · simp [h₁]

private theorem bvt_wightmanInner_self_eq_padded_double_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              bvt_W OS lgc (n + k)
                ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs k))
            else 0
          else 0 := by
  have hw :
      WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers =
        WightmanInnerProductN d (bvt_W OS lgc) F.toBorchers F.toBorchers
          (m + 1) (m + 1) := by
    apply WightmanInnerProduct_eq_extended (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc)
    · exact Nat.succ_le_succ hFm
    · exact Nat.succ_le_succ hFm
  rw [hw]
  unfold WightmanInnerProductN
  refine Finset.sum_congr rfl ?_
  intro n hn
  by_cases hN : n ≤ F.toBorchers.bound
  · refine Finset.sum_congr rfl ?_
    intro k hk
    by_cases hK : k ≤ F.toBorchers.bound
    · simp [hN, hK]
    · have hkgt : F.toBorchers.bound < k := by omega
      simp [hN, hK, F.toBorchers.bound_spec k hkgt,
        (bvt_W_linear (d := d) OS lgc (n + k)).map_zero]
  · have hngt : F.toBorchers.bound < n := by omega
    simp [hN]
    apply Finset.sum_eq_zero
    intro k hk
    rw [F.toBorchers.bound_spec n hngt, SchwartzMap.conjTensorProduct_zero_left,
      (bvt_W_linear (d := d) OS lgc (n + k)).map_zero]

private theorem bvt_wightmanInner_self_eq_single_single_padded_double_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              WightmanInnerProduct d (bvt_W OS lgc)
                (BorchersSequence.single n (F.toBorchers.funcs n))
                (BorchersSequence.single k (F.toBorchers.funcs k))
            else 0
          else 0 := by
  rw [bvt_wightmanInner_self_eq_padded_double_sum
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ F.toBorchers.bound
    · have hsingle :=
        WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) (n := n) (m := k)
          (f := F.toBorchers.funcs n) (g := F.toBorchers.funcs k)
      simpa [h₁, h₂] using hsingle.symm
    · simp [h₁, h₂]
  · simp [h₁]

private theorem bvt_wightmanInner_eq_padded_double_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ G.toBorchers.bound then
              bvt_W OS lgc (n + k)
                ((F.toBorchers.funcs n).conjTensorProduct (G.toBorchers.funcs k))
            else 0
          else 0 := by
  have hw :
      WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
        WightmanInnerProductN d (bvt_W OS lgc) F.toBorchers G.toBorchers
          (m + 1) (m + 1) := by
    apply WightmanInnerProduct_eq_extended (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc)
    · exact Nat.succ_le_succ hFm
    · exact Nat.succ_le_succ hGm
  rw [hw]
  unfold WightmanInnerProductN
  refine Finset.sum_congr rfl ?_
  intro n hn
  by_cases hN : n ≤ F.toBorchers.bound
  · refine Finset.sum_congr rfl ?_
    intro k hk
    by_cases hK : k ≤ G.toBorchers.bound
    · simp [hN, hK]
    · have hkgt : G.toBorchers.bound < k := by omega
      simp [hN, hK, G.toBorchers.bound_spec k hkgt,
        (bvt_W_linear (d := d) OS lgc (n + k)).map_zero]
  · have hngt : F.toBorchers.bound < n := by omega
    simp [hN]
    apply Finset.sum_eq_zero
    intro k hk
    rw [F.toBorchers.bound_spec n hngt, SchwartzMap.conjTensorProduct_zero_left,
      (bvt_W_linear (d := d) OS lgc (n + k)).map_zero]

private theorem bvt_wightmanInner_eq_single_single_padded_double_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ G.toBorchers.bound then
              WightmanInnerProduct d (bvt_W OS lgc)
                (BorchersSequence.single n (F.toBorchers.funcs n))
                (BorchersSequence.single k (G.toBorchers.funcs k))
            else 0
          else 0 := by
  rw [bvt_wightmanInner_eq_padded_double_sum
    (d := d) (OS := OS) (lgc := lgc) (F := F) (G := G) (m := m) hFm hGm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ G.toBorchers.bound
    · have hsingle :=
        WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) (n := n) (m := k)
          (f := F.toBorchers.funcs n) (g := G.toBorchers.funcs k)
      simpa [h₁, h₂] using hsingle.symm
    · simp [h₁, h₂]
  · simp [h₁]

private theorem single_single_wightman_eq_osInner_iff_kernel_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n k : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d k)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) k) :
    WightmanInnerProduct d (bvt_W OS lgc)
        (BorchersSequence.single n φ)
        (BorchersSequence.single k ψ) =
      PositiveTimeBorchersSequence.osInner OS
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f))
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g))
      ↔
    bvt_W OS lgc (n + k) (φ.conjTensorProduct ψ) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          ((f : SchwartzNPoint d n).osConjTensorProduct
            (g : SchwartzNPoint d k))) := by
  rw [WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc) (n := n) (m := k)
      (f := φ) (g := ψ)]
  have hos :
      PositiveTimeBorchersSequence.osInner OS
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f))
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          ((f : SchwartzNPoint d n).osConjTensorProduct
            (g : SchwartzNPoint d k))) := by
    unfold PositiveTimeBorchersSequence.osInner
    simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
      EuclideanPositiveTimeComponent.ofSubmodule, OSInnerProduct_single_single,
      OS.E0_linear]
  rw [hos]

private theorem bvt_wightmanInner_eq_transport_norm_sq_onImage_of_single_single
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m)
    (hss : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ F.toBorchers.bound →
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single n (F.toBorchers.funcs n))
          (BorchersSequence.single k (F.toBorchers.funcs k)) =
        PositiveTimeBorchersSequence.osInner OS
          (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) F n)))
          (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) F k)))) :
    (WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers).re =
      ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 := by
  rw [bvt_wightmanInner_self_eq_single_single_padded_double_sum
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm]
  rw [norm_sq_bvt_transport_to_osHilbert_onImage_eq_osInner_padded_double_sum
    (d := d) (OS := OS) (F := F) (m := m) hFm]
  have hsum :
      ((Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              WightmanInnerProduct d (bvt_W OS lgc)
                (BorchersSequence.single n (F.toBorchers.funcs n))
                (BorchersSequence.single k (F.toBorchers.funcs k))
            else 0
          else 0) =
      ((Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              PositiveTimeBorchersSequence.osInner OS
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n)))
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F k)))
            else 0
          else 0) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    refine Finset.sum_congr rfl ?_
    intro k hk
    by_cases h₁ : n ≤ F.toBorchers.bound
    · by_cases h₂ : k ≤ F.toBorchers.bound
      · simp [h₁, h₂, hss n k h₁ h₂]
      · simp [h₁, h₂]
    · simp [h₁]
  exact congrArg Complex.re hsum

private theorem bvt_wightmanInner_eq_transport_inner_onImage_of_single_single
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m)
    (hss : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ G.toBorchers.bound →
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single n (F.toBorchers.funcs n))
          (BorchersSequence.single k (G.toBorchers.funcs k)) =
        PositiveTimeBorchersSequence.osInner OS
          (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) F n)))
          (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) G k)))) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
      @inner ℂ (OSHilbertSpace OS) _
        (bvt_transport_to_osHilbert_onImage OS F)
        (bvt_transport_to_osHilbert_onImage OS G) := by
  rw [bvt_wightmanInner_eq_single_single_padded_double_sum
    (d := d) (OS := OS) (lgc := lgc) (F := F) (G := G) (m := m) hFm hGm]
  rw [inner_bvt_transport_to_osHilbert_onImage_eq_osInner_padded_double_sum
    (d := d) (OS := OS) (F := F) (G := G) (m := m) hFm hGm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ G.toBorchers.bound
    · simp [h₁, h₂, hss n k h₁ h₂]
    · simp [h₁, h₂]
  · simp [h₁]

theorem bvt_wightmanInner_eq_transport_inner_onImage_of_kernel_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransportImageSequence d)
    (hkernel : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ G.toBorchers.bound →
      bvt_W OS lgc (n + k)
        ((F.toBorchers.funcs n).conjTensorProduct (G.toBorchers.funcs k)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          (((bvtTransportImagePreimage (d := d) F n : euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) G k : euclideanPositiveTimeSubmodule (d := d) k) :
              SchwartzNPoint d k)))) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
      @inner ℂ (OSHilbertSpace OS) _
        (bvt_transport_to_osHilbert_onImage OS F)
        (bvt_transport_to_osHilbert_onImage OS G) := by
  let M := max F.toBorchers.bound G.toBorchers.bound
  apply bvt_wightmanInner_eq_transport_inner_onImage_of_single_single
    (d := d) (OS := OS) (lgc := lgc) (F := F) (G := G) (m := M)
  · dsimp [M]
    exact le_max_left _ _
  · dsimp [M]
    exact le_max_right _ _
  intro n k hn hk
  exact
    (single_single_wightman_eq_osInner_iff_kernel_eq
      (d := d) (OS := OS) (lgc := lgc)
      (φ := F.toBorchers.funcs n) (ψ := G.toBorchers.funcs k)
      (f := bvtTransportImagePreimage (d := d) F n)
      (g := bvtTransportImagePreimage (d := d) G k)).2
      (hkernel n k hn hk)

theorem bvt_wightmanInner_eq_transport_norm_sq_onImage_of_kernel_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m)
    (hkernel : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + k)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs k)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          (((bvtTransportImagePreimage (d := d) F n : euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F k : euclideanPositiveTimeSubmodule (d := d) k) :
              SchwartzNPoint d k)))) :
    (WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers).re =
      ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 := by
  apply bvt_wightmanInner_eq_transport_norm_sq_onImage_of_single_single
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm
  intro n k hn hk
  exact
    (single_single_wightman_eq_osInner_iff_kernel_eq
      (d := d) (OS := OS) (lgc := lgc)
      (φ := F.toBorchers.funcs n) (ψ := F.toBorchers.funcs k)
      (f := bvtTransportImagePreimage (d := d) F n)
      (g := bvtTransportImagePreimage (d := d) F k)).2
      (hkernel n k hn hk)

/-- Once the Stage-5 matrix-element kernel equality is available on the
transformed-image carrier, positivity on that carrier is immediate: the
reconstructed Wightman quadratic form is already identified with the square
norm of the transported OS Hilbert-space vector. -/
theorem bvt_wightmanInner_self_nonneg_onImage_of_kernel_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m)
    (hkernel : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + k)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs k)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          (((bvtTransportImagePreimage (d := d) F n : euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F k : euclideanPositiveTimeSubmodule (d := d) k) :
              SchwartzNPoint d k)))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers).re := by
  rw [bvt_wightmanInner_eq_transport_norm_sq_onImage_of_kernel_eq
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm hkernel]
  exact sq_nonneg ‖bvt_transport_to_osHilbert_onImage OS F‖

/-
Package I transport note:

The old placeholder transport route has been removed. The
current live Package-I frontier is now:
1. establish the transformed-image quadratic identity,
2. then close positivity from the transformed-image core using the already-built
   Hilbert-space density of positive-time vectors.
-/

end
