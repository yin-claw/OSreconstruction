import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCDuBoisBridge

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The antisymmetric swap difference of the raw Euclidean two-point witness. -/
def swapDelta_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ) :
    NPointDomain d 2 → ℂ := fun x =>
  k2TimeParametricKernel (d := d) G x -
    k2TimeParametricKernel (d := d) G
      (swapTwoPointAssembly_local (d := d) x)

/-- Swapping the Euclidean arguments in the raw witness kernel sends the test
factor to `zdsSwap_local`. This is the exact change-of-variables step needed in
the final DuBois-Reymond route. -/
theorem integral_k2TimeParametricKernel_mul_zdsSwap_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (f : ZeroDiagonalSchwartz d 2) :
    ∫ y : NPointDomain d 2,
      k2TimeParametricKernel (d := d) G y * ((zdsSwap_local (d := d) f).1 y) =
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G
            (swapTwoPointAssembly_local (d := d) x) * (f.1 x) := by
  have hcov :=
    integral_comp_swapTwoPointAssembly_local (d := d)
      (fun y : NPointDomain d 2 =>
        k2TimeParametricKernel (d := d) G y *
          ((zdsSwap_local (d := d) f).1 y))
  have hcov_lhs :
      ∫ x : NPointDomain d 2,
        (fun y : NPointDomain d 2 =>
          k2TimeParametricKernel (d := d) G y *
            ((zdsSwap_local (d := d) f).1 y))
          (swapTwoPointAssembly_local (d := d) x) =
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G
            (swapTwoPointAssembly_local (d := d) x) * (f.1 x) := by
    congr 1
    ext x
    change
      k2TimeParametricKernel (d := d) G
          (swapTwoPointAssembly_local (d := d) x) *
        f.1
          (swapTwoPointAssembly_local (d := d)
            (swapTwoPointAssembly_local (d := d) x)) =
      k2TimeParametricKernel (d := d) G
          (swapTwoPointAssembly_local (d := d) x) * f.1 x
    have hswap :
        swapTwoPointAssembly_local (d := d)
            (swapTwoPointAssembly_local (d := d) x) = x := by
      ext i
      fin_cases i <;> simp [swapTwoPointAssembly_local]
    congr 1
    simpa [hswap]
  rw [hcov_lhs] at hcov
  exact hcov.symm

/-- The raw Euclidean two-point witness and its swapped version have the same
pairing against every zero-diagonal Schwartz test. This is the exact `E3` +
change-of-variables identity underlying the final DuBois-Reymond route, and it
avoids introducing any auxiliary integrability side conditions. -/
theorem k2TimeParametricKernel_integral_eq_swap_integral_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G x * (f.1 x))
    (f : ZeroDiagonalSchwartz d 2) :
    ∫ x : NPointDomain d 2,
      k2TimeParametricKernel (d := d) G x * (f.1 x) =
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G
            (swapTwoPointAssembly_local (d := d) x) * (f.1 x) := by
  calc
    ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G x * (f.1 x)
      = OS.S 2 f := by
          exact (hG_euclid f).symm
    _ = OS.S 2 (zdsSwap_local (d := d) f) := by
          exact E3_twoPoint_swap_local (d := d) OS f
    _ =
        ∫ y : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G y *
            ((zdsSwap_local (d := d) f).1 y) := by
              exact hG_euclid (zdsSwap_local (d := d) f)
    _ =
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G
            (swapTwoPointAssembly_local (d := d) x) * (f.1 x) := by
              exact integral_k2TimeParametricKernel_mul_zdsSwap_local (d := d) G f

/-- Distributional swap antisymmetry of the raw Euclidean two-point witness.

Once the two raw pairings against a zero-diagonal Schwartz test are known to be
integrable, `E3` plus the public swap change of variables force the swap
difference `swapDelta_local G` to pair to zero against that test. This extracts
the genuine mathematical core of the final DuBois-Reymond route while leaving
the remaining endgame seam honestly localized to the integrability / a.e.
closure steps. -/
theorem swapDelta_integral_zds_eq_zero_of_integrable_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G x * (f.1 x))
    (f : ZeroDiagonalSchwartz d 2)
    (hInt :
      Integrable
        (fun x : NPointDomain d 2 =>
          k2TimeParametricKernel (d := d) G x * (f.1 x)))
    (hInt_swap :
      Integrable
        (fun x : NPointDomain d 2 =>
          k2TimeParametricKernel (d := d) G
            (swapTwoPointAssembly_local (d := d) x) * (f.1 x))) :
    ∫ x : NPointDomain d 2, swapDelta_local (d := d) G x * (f.1 x) = 0 := by
  calc
    ∫ x : NPointDomain d 2, swapDelta_local (d := d) G x * (f.1 x)
      =
        ∫ x : NPointDomain d 2,
          (k2TimeParametricKernel (d := d) G x * (f.1 x)) -
            (k2TimeParametricKernel (d := d) G
              (swapTwoPointAssembly_local (d := d) x) * (f.1 x)) := by
              simp [swapDelta_local, sub_mul]
    _ =
        (∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G x * (f.1 x)) -
        (∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G
            (swapTwoPointAssembly_local (d := d) x) * (f.1 x)) := by
              rw [integral_sub hInt hInt_swap]
    _ =
        OS.S 2 f - OS.S 2 (zdsSwap_local (d := d) f) := by
          rw [← hG_euclid f,
            ← integral_k2TimeParametricKernel_mul_zdsSwap_local (d := d) G f,
            ← hG_euclid (zdsSwap_local (d := d) f)]
    _ = 0 := by
          rw [E3_twoPoint_swap_local (d := d) OS f]
          simp

/-- Once the common sectorwise kernel agrees almost everywhere with the raw
Euclidean witness kernel, Schwinger reproduction follows immediately by
`integral_congr_ae` and the already-proved Euclidean pairing theorem. This is
the direct shell-level interface needed by the final frontier step after the
remaining DuBois-Reymond a.e.-identification is paid. -/
theorem commonK2TimeParametricKernel_real_eq_schwinger_of_ae_eq_k2TimeParametricKernel_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G x * (f.1 x))
    (hEq : ∀ᵐ x : NPointDomain d 2 ∂volume,
      commonK2TimeParametricKernel_real_local (d := d) G x =
        k2TimeParametricKernel (d := d) G x)
    (f : ZeroDiagonalSchwartz d 2) :
    ∫ x : NPointDomain d 2,
      commonK2TimeParametricKernel_real_local (d := d) G x * (f.1 x) =
        OS.S 2 f := by
  calc
    ∫ x : NPointDomain d 2,
        commonK2TimeParametricKernel_real_local (d := d) G x * (f.1 x)
      =
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G x * (f.1 x) := by
            apply integral_congr_ae
            filter_upwards [hEq] with x hx
            rw [hx]
    _ = OS.S 2 f := by
          exact (hG_euclid f).symm

end OSReconstruction
