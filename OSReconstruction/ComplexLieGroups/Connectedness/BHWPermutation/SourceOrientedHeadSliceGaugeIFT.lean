import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.Submodule
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGauge

/-!
# Source-oriented head-slice gauge by inverse-function coordinates

This file starts the finite-dimensional inverse-function construction of the
corrected head-slice gauge.  The key coordinate is
`K = H * η - η`, where `η = sourceHeadMetric d r hrD`.  In this coordinate
the sliced Gram map is the polynomial

`K ↦ η + 2K + K * η * K`,

so its derivative at the origin is scalar multiplication by `2`.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace BHW

/-- The symmetric complex square matrices as a complex submodule. -/
def sourceSymmetricMatrixSubmodule (r : ℕ) :
    Submodule ℂ (Matrix (Fin r) (Fin r) ℂ) where
  carrier := {A | Aᵀ = A}
  zero_mem' := by
    simp
  add_mem' := by
    intro A B hA hB
    change (A + B)ᵀ = A + B
    rw [Matrix.transpose_add, hA, hB]
  smul_mem' := by
    intro c A hA
    change (c • A)ᵀ = c • A
    rw [Matrix.transpose_smul, hA]

@[simp]
theorem mem_sourceSymmetricMatrixSubmodule
    {r : ℕ}
    {A : Matrix (Fin r) (Fin r) ℂ} :
    A ∈ sourceSymmetricMatrixSubmodule r ↔ Aᵀ = A :=
  Iff.rfl

/-- The canonical source head metric, viewed in the symmetric submodule. -/
def sourceHeadMetricSymmSubmodule
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceSymmetricMatrixSubmodule r :=
  ⟨sourceHeadMetric d r hrD, sourceHeadMetric_transpose d r hrD⟩

/-- Convert the existing symmetric-coordinate subtype to the symmetric
submodule coordinate. -/
def sourceSymmetricMatrixCoordToSubmodule
    (r : ℕ) :
    SourceSymmetricMatrixCoord r ≃ₜ sourceSymmetricMatrixSubmodule r where
  toFun A := ⟨A.1, A.2⟩
  invFun A := ⟨A.1, A.2⟩
  left_inv A := by
    rfl
  right_inv A := by
    rfl
  continuous_toFun := by
    exact continuous_subtype_val.subtype_mk (fun A => A.2)
  continuous_invFun := by
    exact continuous_subtype_val.subtype_mk (fun A => A.2)

@[simp]
theorem sourceSymmetricMatrixCoordToSubmodule_apply
    (r : ℕ)
    (A : SourceSymmetricMatrixCoord r) :
    (sourceSymmetricMatrixCoordToSubmodule r A :
      Matrix (Fin r) (Fin r) ℂ) = A.1 :=
  rfl

@[simp]
theorem sourceSymmetricMatrixCoordToSubmodule_symm_apply
    (r : ℕ)
    (A : sourceSymmetricMatrixSubmodule r) :
    ((sourceSymmetricMatrixCoordToSubmodule r).symm A :
      Matrix (Fin r) (Fin r) ℂ) = A.1 :=
  rfl

/-- The head metric is an involution. -/
theorem sourceHeadMetric_mul_self
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceHeadMetric d r hrD * sourceHeadMetric d r hrD =
      (1 : Matrix (Fin r) (Fin r) ℂ) := by
  rw [sourceHeadMetric, Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a = b
  · subst b
    by_cases hzero : finSourceHead (Nat.le_of_lt hrD) a = (0 : Fin (d + 1))
    · simp [Matrix.diagonal, MinkowskiSpace.metricSignature, hzero]
    · simp [Matrix.diagonal, MinkowskiSpace.metricSignature, hzero]
  · simp [Matrix.diagonal, hab]

/-- The coordinate `K = H * η - η` on the head-gauge slice. -/
def sourceHeadGaugeSliceSymmCoord
    (d r : ℕ)
    (hrD : r < d + 1)
    (H : SourceHeadGaugeSlice d r hrD) :
    sourceSymmetricMatrixSubmodule r :=
  ⟨H.1 * sourceHeadMetric d r hrD - sourceHeadMetric d r hrD, by
    change
      (H.1 * sourceHeadMetric d r hrD - sourceHeadMetric d r hrD)ᵀ =
        H.1 * sourceHeadMetric d r hrD - sourceHeadMetric d r hrD
    rw [Matrix.transpose_sub, ← H.2, sourceHeadMetric_transpose d r hrD]⟩

/-- Rebuild a head-slice point from the symmetric coordinate `K`. -/
def sourceHeadGaugeSliceOfSymmCoord
    (d r : ℕ)
    (hrD : r < d + 1)
    (K : sourceSymmetricMatrixSubmodule r) :
    SourceHeadGaugeSlice d r hrD :=
  ⟨(sourceHeadMetric d r hrD + K.1) * sourceHeadMetric d r hrD, by
    rw [Matrix.mul_assoc, sourceHeadMetric_mul_self d r hrD, Matrix.mul_one]
    rw [Matrix.transpose_add, sourceHeadMetric_transpose d r hrD, K.2]⟩

@[simp]
theorem sourceHeadGaugeSliceOfSymmCoord_val
    (d r : ℕ)
    (hrD : r < d + 1)
    (K : sourceSymmetricMatrixSubmodule r) :
    (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1 =
      (sourceHeadMetric d r hrD + K.1) * sourceHeadMetric d r hrD :=
  rfl

/-- Coordinate homeomorphism from the head slice to symmetric matrices. -/
def sourceHeadGaugeSliceSymmCoordHomeomorph
    (d r : ℕ)
    (hrD : r < d + 1) :
    SourceHeadGaugeSlice d r hrD ≃ₜ sourceSymmetricMatrixSubmodule r where
  toFun := sourceHeadGaugeSliceSymmCoord d r hrD
  invFun := sourceHeadGaugeSliceOfSymmCoord d r hrD
  left_inv H := by
    let η := sourceHeadMetric d r hrD
    have hcancel :
        η + (H.1 * η - η) = H.1 * η := by
      abel
    apply Subtype.ext
    calc
      ((sourceHeadGaugeSliceOfSymmCoord d r hrD
          (sourceHeadGaugeSliceSymmCoord d r hrD H)).1) =
          ((sourceHeadMetric d r hrD +
              (H.1 * sourceHeadMetric d r hrD - sourceHeadMetric d r hrD)) *
            sourceHeadMetric d r hrD) := rfl
      _ = (H.1 * sourceHeadMetric d r hrD) *
            sourceHeadMetric d r hrD := by
            change (η + (H.1 * η - η)) * η = (H.1 * η) * η
            exact congrArg (fun M => M * η) hcancel
      _ = H.1 * (sourceHeadMetric d r hrD * sourceHeadMetric d r hrD) := by
            rw [Matrix.mul_assoc]
      _ = H.1 := by
            rw [sourceHeadMetric_mul_self d r hrD, Matrix.mul_one]
  right_inv K := by
    let η := sourceHeadMetric d r hrD
    apply Subtype.ext
    calc
      ((sourceHeadGaugeSliceSymmCoord d r hrD
          (sourceHeadGaugeSliceOfSymmCoord d r hrD K)).1) =
          ((sourceHeadMetric d r hrD + K.1) * sourceHeadMetric d r hrD) *
              sourceHeadMetric d r hrD -
            sourceHeadMetric d r hrD := rfl
      _ = (sourceHeadMetric d r hrD + K.1) *
              (sourceHeadMetric d r hrD * sourceHeadMetric d r hrD) -
            sourceHeadMetric d r hrD := by
            rw [Matrix.mul_assoc]
      _ = K.1 := by
            rw [sourceHeadMetric_mul_self d r hrD, Matrix.mul_one]
            simp
  continuous_toFun := by
    have hcont :
        Continuous fun H : SourceHeadGaugeSlice d r hrD =>
          H.1 * sourceHeadMetric d r hrD - sourceHeadMetric d r hrD := by
      fun_prop
    exact hcont.subtype_mk (fun H => (sourceHeadGaugeSliceSymmCoord d r hrD H).2)
  continuous_invFun := by
    have hcont :
        Continuous fun K : sourceSymmetricMatrixSubmodule r =>
          (sourceHeadMetric d r hrD + K.1) * sourceHeadMetric d r hrD := by
      fun_prop
    exact hcont.subtype_mk
      (fun K => (sourceHeadGaugeSliceOfSymmCoord d r hrD K).2)

@[simp]
theorem sourceHeadGaugeSliceSymmCoordHomeomorph_apply
    (d r : ℕ)
    (hrD : r < d + 1)
    (H : SourceHeadGaugeSlice d r hrD) :
    sourceHeadGaugeSliceSymmCoordHomeomorph d r hrD H =
      sourceHeadGaugeSliceSymmCoord d r hrD H :=
  rfl

@[simp]
theorem sourceHeadGaugeSliceSymmCoordHomeomorph_symm_apply
    (d r : ℕ)
    (hrD : r < d + 1)
    (K : sourceSymmetricMatrixSubmodule r) :
    (sourceHeadGaugeSliceSymmCoordHomeomorph d r hrD).symm K =
      sourceHeadGaugeSliceOfSymmCoord d r hrD K :=
  rfl

/-- The sliced Gram map in symmetric `K = H * η - η` coordinates. -/
def sourceHeadSliceGramPolynomial
    (d r : ℕ)
    (hrD : r < d + 1)
    (K : sourceSymmetricMatrixSubmodule r) :
    sourceSymmetricMatrixSubmodule r :=
  ⟨sourceHeadMetric d r hrD + (2 : ℂ) • K.1 +
      K.1 * sourceHeadMetric d r hrD * K.1, by
    change
      (sourceHeadMetric d r hrD + (2 : ℂ) • K.1 +
          K.1 * sourceHeadMetric d r hrD * K.1)ᵀ =
        sourceHeadMetric d r hrD + (2 : ℂ) • K.1 +
          K.1 * sourceHeadMetric d r hrD * K.1
    rw [Matrix.transpose_add, Matrix.transpose_add,
      sourceHeadMetric_transpose d r hrD, Matrix.transpose_smul, K.2]
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      sourceHeadMetric_transpose d r hrD, K.2]
    simp [Matrix.mul_assoc]⟩

@[simp]
theorem sourceHeadSliceGramPolynomial_zero
    (d r : ℕ)
    (hrD : r < d + 1) :
    sourceHeadSliceGramPolynomial d r hrD 0 =
      sourceHeadMetricSymmSubmodule d r hrD := by
  apply Subtype.ext
  simp [sourceHeadSliceGramPolynomial, sourceHeadMetricSymmSubmodule]

/-- In slice coordinates, the polynomial equals `H * η * Hᵀ`. -/
theorem sourceHeadSliceGramPolynomial_eq_factorGram
    (d r : ℕ)
    (hrD : r < d + 1)
    (K : sourceSymmetricMatrixSubmodule r) :
    (sourceHeadSliceGramPolynomial d r hrD K :
        Matrix (Fin r) (Fin r) ℂ) =
      (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1 *
        sourceHeadMetric d r hrD *
        (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1ᵀ := by
  let η := sourceHeadMetric d r hrD
  have hηη : η * η = (1 : Matrix (Fin r) (Fin r) ℂ) := by
    simpa [η] using sourceHeadMetric_mul_self d r hrD
  have hηT : ηᵀ = η := by
    simpa [η] using sourceHeadMetric_transpose d r hrD
  have hKT : K.1ᵀ = K.1 := K.2
  have hquad :
      (η + K.1) * η * (η + K.1) =
        η + (2 : ℂ) • K.1 + K.1 * η * K.1 := by
    calc
      (η + K.1) * η * (η + K.1) =
          (η * η + K.1 * η) * (η + K.1) := by
            rw [add_mul]
      _ = (η * η) * (η + K.1) + (K.1 * η) * (η + K.1) := by
            rw [add_mul]
      _ = η * η * η + η * η * K.1 +
            (K.1 * η * η + K.1 * η * K.1) := by
            rw [mul_add, mul_add]
      _ = η + K.1 + (K.1 + K.1 * η * K.1) := by
            rw [hηη]
            rw [Matrix.mul_assoc K.1 η η, hηη, Matrix.mul_one]
            simp [Matrix.mul_assoc]
      _ = η + (2 : ℂ) • K.1 + K.1 * η * K.1 := by
            simp [two_smul, add_assoc]
  calc
    (sourceHeadSliceGramPolynomial d r hrD K :
        Matrix (Fin r) (Fin r) ℂ) =
        η + (2 : ℂ) • K.1 + K.1 * η * K.1 := by
          rfl
    _ = (η + K.1) * η * (η + K.1) := by
          exact hquad.symm
    _ =
      (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1 *
        sourceHeadMetric d r hrD *
        (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1ᵀ := by
          simp [sourceHeadGaugeSliceOfSymmCoord, Matrix.transpose_mul,
            hηT, hKT, hηη, Matrix.mul_assoc, η]

/-- The derivative of the sliced Gram polynomial at the origin is
scalar multiplication by `2`. -/
def sourceHeadSliceGramPolynomialDerivEquiv
    (r : ℕ) :
    sourceSymmetricMatrixSubmodule r ≃L[ℂ]
      sourceSymmetricMatrixSubmodule r :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℂ) (by norm_num))

end BHW
