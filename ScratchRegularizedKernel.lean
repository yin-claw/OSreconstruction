import OSReconstruction.SCV.PaleyWienerSchwartz

open MeasureTheory Complex
open scoped BigOperators
noncomputable section

example {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (η : Fin m → ℝ) (hη : η ∈ C)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin m → ℝ) :
      (∫ x : Fin m → ℝ,
        multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient
          (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) ξ * f x) =
        Complex.exp (-(ε : ℂ) * (etaPairingCLM η ξ : ℂ)) *
          (((dualConeCutoff C).val ξ : ℂ) * physicsFourierFlatCLM f ξ) := by
  have hz : ∀ x : Fin m → ℝ,
      (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) ∈ SCV.TubeDomain C := by
    intro x
    exact realPlusIEpsEta_mem_tubeDomain C hC_cone x η hη ε hε
  simp_rw [multiDimPsiZExt_eq C hC_open hC_conv hC_cone hC_salient
    (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) (hz x)]
  simp [multiDimPsiZ, multiDimPsiZR, psiZRaw]
