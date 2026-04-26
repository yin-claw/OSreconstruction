/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWDbar
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Local Regularity Calculus for Distributional EOW

This file begins the pure-SCV regularity layer used by the local
distributional edge-of-the-wedge route.  It contains the checked
test-function `∂/∂z_j` operator, support preservation, and commutation of the
real coordinate derivatives, plus the coordinate-Laplacian identity that turns
distributional `∂bar`-holomorphy into distributional harmonicity.  The
localized Weyl/parametrix theorem remains the next analytic layer.
-/

noncomputable section

open Complex MeasureTheory
open LineDeriv

namespace SCV

variable {m : ℕ}

/-- The test-function Wirtinger operator `∂/∂z_j` on complex-chart Schwartz
space. -/
def dzSchwartzCLM {m : ℕ} (j : Fin m) :
    SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m) ℂ :=
  (1 / 2 : ℂ) •
    (directionalDerivSchwartzCLM (complexRealDir j) -
      Complex.I • directionalDerivSchwartzCLM (complexImagDir j))

/-- The test-function `∂/∂z_j` operator does not enlarge topological
support. -/
theorem dzSchwartzCLM_tsupport_subset
    (j : Fin m)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    tsupport
      ((dzSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
        ComplexChartSpace m → ℂ) ⊆
    tsupport (φ : ComplexChartSpace m → ℂ) := by
  let X := ComplexChartSpace m
  let dre : SchwartzMap X ℂ := directionalDerivSchwartzCLM (complexRealDir j) φ
  let dim : SchwartzMap X ℂ := directionalDerivSchwartzCLM (complexImagDir j) φ
  let idim : SchwartzMap X ℂ := Complex.I • dim
  let nidim : SchwartzMap X ℂ := -idim
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
      tsupport ((idim : SchwartzMap X ℂ) : X → ℂ) ⊆
        tsupport (dim : X → ℂ) := by
    simpa using
      tsupport_smul_subset_right (fun _ : X => Complex.I) (dim : X → ℂ)
  have hnI :
      tsupport ((nidim : SchwartzMap X ℂ) : X → ℂ) ⊆
        tsupport (dim : X → ℂ) := by
    rw [show ((nidim : SchwartzMap X ℂ) : X → ℂ) =
        -((idim : SchwartzMap X ℂ) : X → ℂ) by rfl]
    rw [tsupport_neg]
    exact hI
  have hright :
      tsupport
          (((1 / 2 : ℂ) • nidim : SchwartzMap X ℂ) :
            X → ℂ) ⊆
        tsupport (φ : X → ℂ) := by
    exact
      (tsupport_smul_subset_right (fun _ : X => (1 / 2 : ℂ))
        ((nidim : SchwartzMap X ℂ) : X → ℂ)).trans
          (hnI.trans hdim)
  have hadd :
      tsupport
          ((((1 / 2 : ℂ) • dre +
            (1 / 2 : ℂ) • nidim) : SchwartzMap X ℂ) :
              X → ℂ) ⊆
        tsupport (((1 / 2 : ℂ) • dre : SchwartzMap X ℂ) : X → ℂ) ∪
          tsupport
            (((1 / 2 : ℂ) • nidim : SchwartzMap X ℂ) :
              X → ℂ) := by
    simpa using
      tsupport_add (((1 / 2 : ℂ) • dre : SchwartzMap X ℂ) : X → ℂ)
        (((1 / 2 : ℂ) • nidim : SchwartzMap X ℂ) : X → ℂ)
  intro x hx
  have hx' :
      x ∈
        tsupport
          ((((1 / 2 : ℂ) • dre +
            (1 / 2 : ℂ) • nidim) : SchwartzMap X ℂ) :
              X → ℂ) := by
    simpa [dzSchwartzCLM, X, dre, dim, idim, nidim, sub_eq_add_neg,
      smul_add] using hx
  rcases hadd hx' with hxleft | hxright
  · exact hleft hxleft
  · exact hright hxright

/-- The `∂/∂z_j` test operator preserves compact support inside the same open
chart set. -/
theorem SupportsInOpen.dz
    {U : Set (ComplexChartSpace m)}
    {φ : SchwartzMap (ComplexChartSpace m) ℂ}
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U)
    (j : Fin m) :
    SupportsInOpen
      ((dzSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
        ComplexChartSpace m → ℂ) U := by
  constructor
  · exact hφ.1.mono'
      ((subset_tsupport _).trans (dzSchwartzCLM_tsupport_subset j φ))
  · exact (dzSchwartzCLM_tsupport_subset j φ).trans hφ.2

/-- Directional derivatives of complex-chart Schwartz functions commute. -/
theorem lineDerivOp_comm_complex {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (v w : ComplexChartSpace m) :
    ∂_{v} ((∂_{w} φ : SchwartzMap (ComplexChartSpace m) ℂ)) =
      ∂_{w} ((∂_{v} φ : SchwartzMap (ComplexChartSpace m) ℂ)) := by
  ext x
  have hsym :=
    (φ.contDiffAt (2 : ℕ∞) (x := x)).isSymmSndFDerivAt
      (n := (2 : WithTop ℕ∞)) (by simp)
  calc
    (∂_{v} ((∂_{w} φ : SchwartzMap (ComplexChartSpace m) ℂ))) x =
        (∂^{![v, w]} φ) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]
    _ = iteratedFDeriv ℝ 2
        (φ : ComplexChartSpace m → ℂ) x ![v, w] := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := φ) (m := ![v, w]) (x := x))
    _ = iteratedFDeriv ℝ 2
        (φ : ComplexChartSpace m → ℂ) x ![w, v] := by
      exact hsym.iteratedFDeriv_cons
    _ = (∂^{![w, v]} φ) x := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := φ) (m := ![w, v]) (x := x)).symm
    _ = (∂_{w} ((∂_{v} φ : SchwartzMap (ComplexChartSpace m) ℂ))) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]

/-- The SCV-owned directional derivative operator commutes in any two real
directions. -/
theorem directionalDerivSchwartzCLM_comm
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (v w : ComplexChartSpace m) :
    directionalDerivSchwartzCLM v (directionalDerivSchwartzCLM w φ) =
      directionalDerivSchwartzCLM w (directionalDerivSchwartzCLM v φ) := by
  simpa [directionalDerivSchwartzCLM] using
    lineDerivOp_comm_complex (m := m) φ v w

/-- The test-function `∂bar_j` and `∂z_j` operators commute. -/
theorem dbar_dzSchwartzCLM_comm
    (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    dbarSchwartzCLM j (dzSchwartzCLM j φ) =
      dzSchwartzCLM j (dbarSchwartzCLM j φ) := by
  let X := ComplexChartSpace m
  let R : SchwartzMap X ℂ →L[ℂ] SchwartzMap X ℂ :=
    directionalDerivSchwartzCLM (complexRealDir j)
  let Y : SchwartzMap X ℂ →L[ℂ] SchwartzMap X ℂ :=
    directionalDerivSchwartzCLM (complexImagDir j)
  have hRY : R (Y φ) = Y (R φ) := by
    simpa [X, R, Y] using directionalDerivSchwartzCLM_comm
      (m := m) φ (complexRealDir j) (complexImagDir j)
  ext z
  change (((1 / 2 : ℂ) • (R + Complex.I • Y))
      (((1 / 2 : ℂ) • (R - Complex.I • Y)) φ)) z =
    (((1 / 2 : ℂ) • (R - Complex.I • Y))
      (((1 / 2 : ℂ) • (R + Complex.I • Y)) φ)) z
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, map_smul, map_add, map_sub]
  rw [hRY]
  simp only [SchwartzMap.smul_apply, SchwartzMap.add_apply,
    SchwartzMap.sub_apply, smul_eq_mul]
  ring_nf

/-- The coordinate real Laplacian on the complex chart:
`∑_j (D_{x_j}^2 + D_{y_j}^2)`.  This avoids imposing a fake inner-product
instance on the repo's plain Pi chart type; the later Weyl theorem will bridge
this coordinate operator to the standard Euclidean Laplacian by a linear
equivalence. -/
def complexChartLaplacianSchwartzCLM {m : ℕ} :
    SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m) ℂ :=
  ∑ j : Fin m,
    ((directionalDerivSchwartzCLM (complexRealDir j)).comp
        (directionalDerivSchwartzCLM (complexRealDir j)) +
      (directionalDerivSchwartzCLM (complexImagDir j)).comp
        (directionalDerivSchwartzCLM (complexImagDir j)))

/-- The coordinate Laplacian applied to a test is the finite sum of real and
imaginary coordinate second derivatives. -/
theorem complexChartLaplacianSchwartzCLM_apply
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    complexChartLaplacianSchwartzCLM φ =
      ∑ j : Fin m,
        (directionalDerivSchwartzCLM (complexRealDir j)
            (directionalDerivSchwartzCLM (complexRealDir j) φ) +
          directionalDerivSchwartzCLM (complexImagDir j)
            (directionalDerivSchwartzCLM (complexImagDir j) φ)) := by
  simp [complexChartLaplacianSchwartzCLM]

/-- In one complex coordinate, `4 ∂bar_j ∂z_j` is the real two-coordinate
second-derivative sum on tests. -/
theorem four_dbar_dzSchwartzCLM_eq_real_imag_second
    (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    (4 : ℂ) • dbarSchwartzCLM j (dzSchwartzCLM j φ) =
      directionalDerivSchwartzCLM (complexRealDir j)
          (directionalDerivSchwartzCLM (complexRealDir j) φ) +
        directionalDerivSchwartzCLM (complexImagDir j)
          (directionalDerivSchwartzCLM (complexImagDir j) φ) := by
  let X := ComplexChartSpace m
  let R : SchwartzMap X ℂ →L[ℂ] SchwartzMap X ℂ :=
    directionalDerivSchwartzCLM (complexRealDir j)
  let Y : SchwartzMap X ℂ →L[ℂ] SchwartzMap X ℂ :=
    directionalDerivSchwartzCLM (complexImagDir j)
  have hRY : R (Y φ) = Y (R φ) := by
    simpa [X, R, Y] using directionalDerivSchwartzCLM_comm
      (m := m) φ (complexRealDir j) (complexImagDir j)
  ext z
  change (((4 : ℂ) • (((1 / 2 : ℂ) • (R + Complex.I • Y))
      (((1 / 2 : ℂ) • (R - Complex.I • Y)) φ))) : SchwartzMap X ℂ) z =
    (R (R φ) + Y (Y φ)) z
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, map_smul, map_sub]
  rw [hRY]
  simp only [SchwartzMap.smul_apply, SchwartzMap.add_apply,
    SchwartzMap.sub_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]

/-- The coordinate real Laplacian is `4 ∑_j ∂bar_j ∂z_j` on complex-chart
Schwartz tests. -/
theorem complexChartLaplacianSchwartzCLM_eq_four_sum_dbar_dz
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    complexChartLaplacianSchwartzCLM φ =
      (4 : ℂ) •
        ∑ j : Fin m, dbarSchwartzCLM j (dzSchwartzCLM j φ) := by
  rw [complexChartLaplacianSchwartzCLM_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact (four_dbar_dzSchwartzCLM_eq_real_imag_second j φ).symm

/-- Distributional `∂bar`-holomorphy implies local harmonicity in the
distributional real-Laplacian sense. -/
theorem local_laplacian_zero_of_distributionalHolomorphic
    (Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    {U0 : Set (ComplexChartSpace m)}
    (hCR : IsDistributionalHolomorphicOn Hdist U0)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0) :
    Hdist (complexChartLaplacianSchwartzCLM φ) = 0 := by
  rw [complexChartLaplacianSchwartzCLM_eq_four_sum_dbar_dz]
  simp only [map_smul, map_sum]
  have hsum :
      ∑ j : Fin m, Hdist (dbarSchwartzCLM j (dzSchwartzCLM j φ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _hj
    exact hCR j (dzSchwartzCLM j φ) (hφ.dz j)
  simp [hsum]

/-- The pointwise `∂/∂bar z_j` expression for a real-differentiable function
on the complex chart. -/
def pointwiseDbar (j : Fin m) (H : ComplexChartSpace m → ℂ)
    (z : ComplexChartSpace m) : ℂ :=
  (1 / 2 : ℂ) *
    (fderiv ℝ H z (complexRealDir j) +
      Complex.I * fderiv ℝ H z (complexImagDir j))

/-- On a global Schwartz function, the test-function `∂bar` operator agrees
pointwise with the corresponding `fderiv` expression. -/
theorem dbarSchwartzCLM_apply_eq_pointwiseDbar
    (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (z : ComplexChartSpace m) :
    (dbarSchwartzCLM j φ) z =
      pointwiseDbar j (φ : ComplexChartSpace m → ℂ) z := by
  simp [pointwiseDbar, dbarSchwartzCLM, directionalDerivSchwartzCLM,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  ring

end SCV
