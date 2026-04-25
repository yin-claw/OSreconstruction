/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernel

/-!
# Support Lemmas for Local Distributional Edge-of-the-Wedge

This file records the support hygiene used by the
Streater-Wightman/Jost regularization route.  The lemmas are QFT-free and
consume only the checked SCV kernel substrate.
-/

noncomputable section

open Complex MeasureTheory

namespace SCV

variable {m : ℕ}

/-- A kernel whose topological support is contained in a closed ball is
compactly supported in the finite-dimensional real chart. -/
theorem KernelSupportWithin_hasCompactSupport
    {ψ : SchwartzMap (Fin m → ℝ) ℂ} {r : ℝ}
    (hψ : KernelSupportWithin ψ r) :
    HasCompactSupport (ψ : (Fin m → ℝ) → ℂ) := by
  exact IsCompact.of_isClosed_subset
    (isCompact_closedBall 0 r) (isClosed_tsupport _) hψ

/-- Real directional derivatives of Schwartz tests do not enlarge topological
support. -/
theorem directionalDerivSchwartzCLM_tsupport_subset
    (v : ComplexChartSpace m)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    tsupport
      ((directionalDerivSchwartzCLM v φ :
        SchwartzMap (ComplexChartSpace m) ℂ) :
          ComplexChartSpace m → ℂ) ⊆
    tsupport (φ : ComplexChartSpace m → ℂ) := by
  simpa [directionalDerivSchwartzCLM] using
    (SchwartzMap.tsupport_lineDerivOp_subset (m := v) (f := φ))

/-- Real directional derivatives preserve the predicate of being compactly
supported inside an open chart set. -/
theorem directionalDerivSchwartzCLM_supportsInOpen
    {U : Set (ComplexChartSpace m)}
    {φ : SchwartzMap (ComplexChartSpace m) ℂ}
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U)
    (v : ComplexChartSpace m) :
    SupportsInOpen
      ((directionalDerivSchwartzCLM v φ :
        SchwartzMap (ComplexChartSpace m) ℂ) :
          ComplexChartSpace m → ℂ) U := by
  constructor
  · exact hφ.1.mono'
      ((subset_tsupport _).trans
        (directionalDerivSchwartzCLM_tsupport_subset v φ))
  · exact (directionalDerivSchwartzCLM_tsupport_subset v φ).trans hφ.2

/-- The test-function `∂/∂bar z_j` operator does not enlarge topological
support. -/
theorem dbarSchwartzCLM_tsupport_subset
    (j : Fin m)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    tsupport
      ((dbarSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
        ComplexChartSpace m → ℂ) ⊆
    tsupport (φ : ComplexChartSpace m → ℂ) := by
  let X := ComplexChartSpace m
  let dre : SchwartzMap X ℂ := directionalDerivSchwartzCLM (complexRealDir j) φ
  let dim : SchwartzMap X ℂ := directionalDerivSchwartzCLM (complexImagDir j) φ
  have hdre : tsupport (dre : X → ℂ) ⊆ tsupport (φ : X → ℂ) := by
    simpa [X, dre] using directionalDerivSchwartzCLM_tsupport_subset
      (m := m) (v := complexRealDir j) φ
  have hdim : tsupport (dim : X → ℂ) ⊆ tsupport (φ : X → ℂ) := by
    simpa [X, dim] using directionalDerivSchwartzCLM_tsupport_subset
      (m := m) (v := complexImagDir j) φ
  have hleft :
      tsupport (((1 / 2 : ℂ) • dre : SchwartzMap X ℂ) : X → ℂ) ⊆
        tsupport (φ : X → ℂ) := by
    exact
      (tsupport_smul_subset_right (fun _ : X => (1 / 2 : ℂ))
        (dre : X → ℂ)).trans hdre
  have hI :
      tsupport ((Complex.I • dim : SchwartzMap X ℂ) : X → ℂ) ⊆
        tsupport (dim : X → ℂ) := by
    simpa using
      tsupport_smul_subset_right (fun _ : X => Complex.I) (dim : X → ℂ)
  have hright :
      tsupport
          (((1 / 2 : ℂ) • (Complex.I • dim) : SchwartzMap X ℂ) :
            X → ℂ) ⊆
        tsupport (φ : X → ℂ) := by
    exact
      (tsupport_smul_subset_right (fun _ : X => (1 / 2 : ℂ))
        ((Complex.I • dim : SchwartzMap X ℂ) : X → ℂ)).trans
          (hI.trans hdim)
  have hadd :
      tsupport
          ((((1 / 2 : ℂ) • dre +
            (1 / 2 : ℂ) • (Complex.I • dim)) : SchwartzMap X ℂ) :
              X → ℂ) ⊆
        tsupport (((1 / 2 : ℂ) • dre : SchwartzMap X ℂ) : X → ℂ) ∪
          tsupport
            (((1 / 2 : ℂ) • (Complex.I • dim) : SchwartzMap X ℂ) :
              X → ℂ) := by
    simpa using
      tsupport_add (((1 / 2 : ℂ) • dre : SchwartzMap X ℂ) : X → ℂ)
        (((1 / 2 : ℂ) • (Complex.I • dim) : SchwartzMap X ℂ) : X → ℂ)
  intro x hx
  have hx' :
      x ∈
        tsupport
          ((((1 / 2 : ℂ) • dre +
            (1 / 2 : ℂ) • (Complex.I • dim)) : SchwartzMap X ℂ) :
              X → ℂ) := by
    simpa [dbarSchwartzCLM, X, dre, dim, smul_add] using hx
  rcases hadd hx' with hxleft | hxright
  · exact hleft hxleft
  · exact hright hxright

/-- The Cauchy-Riemann test operator preserves compact support inside the same
open chart set. -/
theorem SupportsInOpen.dbar
    {U : Set (ComplexChartSpace m)}
    {φ : SchwartzMap (ComplexChartSpace m) ℂ}
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U)
    (j : Fin m) :
    SupportsInOpen
      ((dbarSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
        ComplexChartSpace m → ℂ) U := by
  constructor
  · exact hφ.1.mono'
      ((subset_tsupport _).trans (dbarSchwartzCLM_tsupport_subset j φ))
  · exact (dbarSchwartzCLM_tsupport_subset j φ).trans hφ.2

end SCV
