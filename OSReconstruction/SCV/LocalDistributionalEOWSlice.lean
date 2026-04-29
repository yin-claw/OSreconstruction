/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.LocalDistributionalEOW
import OSReconstruction.SCV.LocalEOWSideCone

/-!
# Two-Sided Local Distributional EOW Slice Families

This file assembles the plus/minus cutoff slice continuous-linear-map families
from raw distributional boundary values on the side cones supplied by
`LocalEOWSideCone`.  The construction is deliberately small: the one-sided
analytic and integration estimates live in `LocalDistributionalEOW`, while this
file keeps the two-sided packaging and the cutoff target rewrite explicit.
-/

noncomputable section

open Complex MeasureTheory Set Filter

namespace SCV

variable {m : ℕ}

/-- Construct the plus/minus local slice CLM families from two raw
distributional boundary values and a single cutoff-compatible target
distribution. -/
theorem sliceCLM_family_from_distributionalBoundary
    {rψ : ℝ}
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    {Cplus Cminus : Set (Fin m → ℝ)}
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (Traw : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (χ : SchwartzMap (Fin m → ℝ) ℂ)
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont : ContinuousOn Fplus Ωplus)
    (hFminus_cont : ContinuousOn Fminus Ωminus)
    (hχ_compact : HasCompactSupport (χ : (Fin m → ℝ) → ℂ))
    (hTchart :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        (Tchart.restrictScalars ℝ) φ =
          Traw ((SchwartzMap.smulLeftCLM ℂ
            (χ : (Fin m → ℝ) → ℂ)) φ))
    (hplus_margin :
      ∀ y ∈ Cplus, ∀ x ∈ tsupport (χ : (Fin m → ℝ) → ℂ),
        (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) ∈ Ωplus)
    (hminus_margin :
      ∀ y ∈ Cminus, ∀ x ∈ tsupport (χ : (Fin m → ℝ) → ℂ),
        (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (hplus_cutoff_one :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dplus, ∀ x ∈
          tsupport
            (translateSchwartz (fun i => - (w i).re) ψ :
              (Fin m → ℝ) → ℂ),
          χ x = 1)
    (hminus_cutoff_one :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dminus, ∀ x ∈
          tsupport
            (translateSchwartz (fun i => - (w i).re) ψ :
              (Fin m → ℝ) → ℂ),
          χ x = 1)
    (hplus_bv_raw :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y =>
          ∫ x : Fin m → ℝ,
            Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) *
              Complex.I) * φ x)
          (nhdsWithin 0 Cplus) (nhds (Traw φ)))
    (hminus_bv_raw :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y =>
          ∫ x : Fin m → ℝ,
            Fminus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) *
              Complex.I) * φ x)
          (nhdsWithin 0 Cminus) (nhds (Traw φ))) :
    ∃ Tplus Tminus :
        (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ,
      (∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ)) ∧
      (∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dminus,
          realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ)) ∧
      (∀ φ, Tendsto (fun y => Tplus y φ) (nhdsWithin 0 Cplus)
        (nhds ((Tchart.restrictScalars ℝ) φ))) ∧
      (∀ φ, Tendsto (fun y => Tminus y φ) (nhdsWithin 0 Cminus)
        (nhds ((Tchart.restrictScalars ℝ) φ))) := by
  obtain ⟨Tplus, hTplus_eval, hTplus_lim0⟩ :=
    exists_cutoffSliceCLM_family_of_boundaryValue
      Fplus χ Ωplus Traw hΩplus_open hFplus_cont hχ_compact
      hplus_margin hplus_bv_raw
  obtain ⟨Tminus, hTminus_eval, hTminus_lim0⟩ :=
    exists_cutoffSliceCLM_family_of_boundaryValue
      Fminus χ Ωminus Traw hΩminus_open hFminus_cont hχ_compact
      hminus_margin hminus_bv_raw
  refine ⟨Tplus, Tminus, ?_, ?_, ?_, ?_⟩
  · intro ψ hψ w hw
    have him : (fun i => (w i).im) ∈ Cplus := by
      simpa [TubeDomain] using hDplus_sub hw
    exact
      realMollifyLocal_eq_cutoffSliceCLM
        Fplus χ ψ w (Tplus (fun i => (w i).im))
        (hplus_cutoff_one ψ hψ w hw)
        (hTplus_eval (fun i => (w i).im) him)
  · intro ψ hψ w hw
    have him : (fun i => (w i).im) ∈ Cminus := by
      simpa [TubeDomain] using hDminus_sub hw
    exact
      realMollifyLocal_eq_cutoffSliceCLM
        Fminus χ ψ w (Tminus (fun i => (w i).im))
        (hminus_cutoff_one ψ hψ w hw)
        (hTminus_eval (fun i => (w i).im) him)
  · intro φ
    simpa [hTchart φ] using hTplus_lim0 φ
  · intro φ
    simpa [hTchart φ] using hTminus_lim0 φ

end SCV
