import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexTakagiEntry

/-!
# Algebraic assembly for Autonne-Takagi columns

This file proves the purely matrix-algebraic endpoint of the Takagi assembly:
if the columns of a unitary matrix satisfy the conjugate-linear Takagi
eigenvector equation, then the corresponding matrix diagonalization is
`S = U * diagonal σ * Uᵀ`.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open scoped Matrix.Norms.Operator ComplexOrder ComplexConjugate

namespace BHW

/-- The transpose of a unitary complex matrix also has the needed left inverse. -/
theorem matrix_unitary_star_transpose_mul_transpose
    (m : ℕ) (U : Matrix.unitaryGroup (Fin m) ℂ) :
    star ((U : Matrix (Fin m) (Fin m) ℂ).transpose) *
      ((U : Matrix (Fin m) (Fin m) ℂ).transpose) = 1 := by
  ext i j
  have h := congrFun (congrFun U.2.2 j) i
  by_cases hij : i = j
  · subst j
    simpa [Matrix.mul_apply, mul_comm] using h
  · have hji : j ≠ i := by
      exact fun h => hij h.symm
    simpa [Matrix.mul_apply, hij, hji, mul_comm] using h

/-- If the unitary columns are Takagi eigenvectors for the conjugate-linear map
`v ↦ S *ᵥ star v`, then they assemble into the Takagi matrix identity. -/
theorem complexSymmetric_takagi_matrix_eq_of_col_eigen
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ)
    (U : Matrix.unitaryGroup (Fin m) ℂ) (σ : Fin m → ℝ)
    (hcol : ∀ a : Fin m,
      takagiConjugateLinearMap m S (fun i => (U : Matrix (Fin m) (Fin m) ℂ) i a) =
        (σ a : ℂ) • fun i => (U : Matrix (Fin m) (Fin m) ℂ) i a) :
    S =
      (U : Matrix (Fin m) (Fin m) ℂ) *
        Matrix.diagonal (fun a => (σ a : ℂ)) *
        (U : Matrix (Fin m) (Fin m) ℂ).transpose := by
  have hright := matrix_unitary_star_transpose_mul_transpose m U
  have hSU :
      S * star ((U : Matrix (Fin m) (Fin m) ℂ).transpose) =
        (U : Matrix (Fin m) (Fin m) ℂ) * Matrix.diagonal (fun a => (σ a : ℂ)) := by
    ext i a
    have h := congrFun (hcol a) i
    simpa [takagiConjugateLinearMap, Matrix.mul_apply, Matrix.diagonal, dotProduct, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  calc
    S = S * 1 := by
      rw [mul_one]
    _ = S * (star ((U : Matrix (Fin m) (Fin m) ℂ).transpose) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose) := by
      rw [hright]
    _ = (S * star ((U : Matrix (Fin m) (Fin m) ℂ).transpose)) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose := by
      rw [Matrix.mul_assoc]
    _ = ((U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun a => (σ a : ℂ))) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose := by
      rw [hSU]
    _ = (U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun a => (σ a : ℂ)) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose := by
      rw [Matrix.mul_assoc]

end BHW
