import OSReconstruction.ComplexLieGroups.SOConnected

/-!
# SOComplex frame-transitivity support

This file contains the finite-dimensional row/column algebra used by the
signed-frame induction behind the determinant-one Witt normalization step.
The hard frame-transitivity theorem is still downstream; these lemmas make the
one-column descent explicit and reusable.
-/

noncomputable section

open Complex Matrix Classical

namespace SOComplex

@[simp]
theorem inv_val_apply {n : ℕ} (A : SOComplex n) (i j : Fin n) :
    (A⁻¹).val i j = A.val j i := by
  rfl

/-- The first coordinate of the inverse-transformed vector is its dot product
with the first column of the original special orthogonal matrix. -/
theorem inv_mulVec_zero_eq_sum_col {n : ℕ} [NeZero n]
    (A : SOComplex n) (w : Fin n → ℂ) :
    ((A⁻¹).val *ᵥ w) (0 : Fin n) =
      ∑ k : Fin n, A.val k (0 : Fin n) * w k := by
  change (∑ k : Fin n, (A⁻¹).val (0 : Fin n) k * w k) = _
  simp

/-- If the first column of `A` is `v / σ`, then every vector orthogonal to
`v` has zero first coordinate after applying `A⁻¹`. -/
theorem inv_mulVec_zero_eq_zero_of_signed_col_orth {n : ℕ} [NeZero n]
    (A : SOComplex n) {σ : ℂ} (hσ : σ ≠ 0)
    {v w : Fin n → ℂ}
    (hA : ∀ k : Fin n, σ * A.val k (0 : Fin n) = v k)
    (horth : ∑ k : Fin n, v k * w k = 0) :
    ((A⁻¹).val *ᵥ w) (0 : Fin n) = 0 := by
  have hmul : σ * ((A⁻¹).val *ᵥ w) (0 : Fin n) = 0 := by
    rw [inv_mulVec_zero_eq_sum_col]
    calc
      σ * (∑ k : Fin n, A.val k (0 : Fin n) * w k)
          = ∑ k : Fin n, σ * (A.val k (0 : Fin n) * w k) := by
              rw [Finset.mul_sum]
      _ = ∑ k : Fin n, v k * w k := by
              apply Finset.sum_congr rfl
              intro k _
              rw [← mul_assoc, hA k]
      _ = 0 := horth
  exact (mul_eq_zero.mp hmul).resolve_left hσ

/-- Special orthogonal matrices preserve the complex symmetric dot product. -/
theorem dot_mulVec_eq {n : ℕ} (A : SOComplex n)
    (v w : Fin n → ℂ) :
    (∑ k : Fin n, (A.val *ᵥ v) k * (A.val *ᵥ w) k) =
      ∑ k : Fin n, v k * w k := by
  have hvec : (A.val *ᵥ v) ᵥ* A.val = v := by
    calc
      (A.val *ᵥ v) ᵥ* A.val = (v ᵥ* A.val.transpose) ᵥ* A.val := by
          rw [Matrix.vecMul_transpose]
      _ = v ᵥ* (A.val.transpose * A.val) := by
          rw [Matrix.vecMul_vecMul]
      _ = v := by
          rw [A.orthogonal]
          simp
  calc
    (∑ k : Fin n, (A.val *ᵥ v) k * (A.val *ᵥ w) k)
        = (A.val *ᵥ v) ⬝ᵥ (A.val *ᵥ w) := by
            simp [dotProduct]
    _ = ((A.val *ᵥ v) ᵥ* A.val) ⬝ᵥ w := by
            rw [Matrix.dotProduct_mulVec]
    _ = v ⬝ᵥ w := by rw [hvec]
    _ = ∑ k : Fin n, v k * w k := by
            simp [dotProduct]

/-- Special orthogonal matrices preserve the square norm. -/
theorem sumSq_mulVec_eq {n : ℕ} (A : SOComplex n)
    (v : Fin n → ℂ) :
    (∑ k : Fin n, (A.val *ᵥ v) k ^ 2) =
      ∑ k : Fin n, v k ^ 2 := by
  simpa [sq] using dot_mulVec_eq A v v

/-- Applying an element after its inverse recovers the original vector. -/
theorem mulVec_inv_mulVec {n : ℕ} (A : SOComplex n)
    (v : Fin n → ℂ) :
    A.val *ᵥ ((A⁻¹).val *ᵥ v) = v := by
  have hmul : A.val * (A⁻¹).val = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    change (A * A⁻¹).val = (1 : SOComplex n).val
    exact congrArg SOComplex.val (mul_inv_cancel A)
  calc
    A.val *ᵥ ((A⁻¹).val *ᵥ v) =
        (A.val * (A⁻¹).val) *ᵥ v := by
          rw [Matrix.mulVec_mulVec]
    _ = v := by
          rw [hmul]
          simp

/-- Applying the inverse after an element recovers the original vector. -/
theorem inv_mulVec_mulVec {n : ℕ} (A : SOComplex n)
    (v : Fin n → ℂ) :
    (A⁻¹).val *ᵥ (A.val *ᵥ v) = v := by
  have hmul : (A⁻¹).val * A.val = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    change (A⁻¹ * A).val = (1 : SOComplex n).val
    exact congrArg SOComplex.val (inv_mul_cancel A)
  calc
    (A⁻¹).val *ᵥ (A.val *ᵥ v) =
        ((A⁻¹).val * A.val) *ᵥ v := by
          rw [Matrix.mulVec_mulVec]
    _ = v := by
          rw [hmul]
          simp

/-- The first column of `A * embed B` is the first column of `A`. -/
theorem mul_embed_val_col_zero {m : ℕ}
    (A : SOComplex (m + 2)) (B : SOComplex (m + 1))
    (k : Fin (m + 2)) :
    (A * embed B).val k 0 = A.val k 0 := by
  change (A.val * (embed B).val) k 0 = A.val k 0
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp

/-- The remaining columns of `A * embed B` are `A` applied to the embedded
tail columns of `B`. -/
theorem mul_embed_val_col_succ {m : ℕ}
    (A : SOComplex (m + 2)) (B : SOComplex (m + 1))
    (k : Fin (m + 2)) (j : Fin (m + 1)) :
    (A * embed B).val k j.succ =
      ∑ l : Fin (m + 1), A.val k l.succ * B.val l j := by
  change (A.val * (embed B).val) k j.succ = _
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp

/-- If the zeroth coordinate vanishes, dropping it preserves the square norm. -/
theorem sum_tail_sq_eq_of_zero_head {m : ℕ}
    (v : Fin (m + 2) → ℂ) (h0 : v 0 = 0) :
    (∑ i : Fin (m + 1), v i.succ ^ 2) =
      ∑ k : Fin (m + 2), v k ^ 2 := by
  conv_rhs => rw [Fin.sum_univ_succ]
  simp [h0]

/-- If the zeroth coordinates vanish, dropping them preserves the dot product. -/
theorem sum_tail_mul_eq_of_zero_heads {m : ℕ}
    (v w : Fin (m + 2) → ℂ) (hv0 : v 0 = 0) (hw0 : w 0 = 0) :
    (∑ i : Fin (m + 1), v i.succ * w i.succ) =
      ∑ k : Fin (m + 2), v k * w k := by
  conv_rhs => rw [Fin.sum_univ_succ]
  simp [hv0, hw0]

/-- Tail square norm after the signed one-column normalization. -/
theorem tail_sq_eq_of_inv_mulVec_signed_col_orth {m : ℕ}
    (A : SOComplex (m + 2)) {σ τ : ℂ} (hσ : σ ≠ 0)
    {v w : Fin (m + 2) → ℂ}
    (hA : ∀ k : Fin (m + 2), σ * A.val k 0 = v k)
    (hvw : ∑ k : Fin (m + 2), v k * w k = 0)
    (hww : ∑ k : Fin (m + 2), w k ^ 2 = τ ^ 2) :
    (∑ i : Fin (m + 1), ((A⁻¹).val *ᵥ w) i.succ ^ 2) = τ ^ 2 := by
  let w' : Fin (m + 2) → ℂ := (A⁻¹).val *ᵥ w
  have hw0 : w' 0 = 0 :=
    inv_mulVec_zero_eq_zero_of_signed_col_orth A hσ hA hvw
  have hsq : ∑ k : Fin (m + 2), w' k ^ 2 = τ ^ 2 := by
    simpa [w'] using (sumSq_mulVec_eq (A⁻¹) w).trans hww
  calc
    (∑ i : Fin (m + 1), ((A⁻¹).val *ᵥ w) i.succ ^ 2)
        = ∑ i : Fin (m + 1), w' i.succ ^ 2 := by rfl
    _ = ∑ k : Fin (m + 2), w' k ^ 2 :=
        sum_tail_sq_eq_of_zero_head w' hw0
    _ = τ ^ 2 := hsq

/-- Tail dot product after the signed one-column normalization. -/
theorem tail_dot_eq_of_inv_mulVec_signed_col_orth {m : ℕ}
    (A : SOComplex (m + 2)) {σ : ℂ} (hσ : σ ≠ 0)
    {v w u : Fin (m + 2) → ℂ} {c : ℂ}
    (hA : ∀ k : Fin (m + 2), σ * A.val k 0 = v k)
    (hvw : ∑ k : Fin (m + 2), v k * w k = 0)
    (hvu : ∑ k : Fin (m + 2), v k * u k = 0)
    (hwu : ∑ k : Fin (m + 2), w k * u k = c) :
    (∑ i : Fin (m + 1),
      ((A⁻¹).val *ᵥ w) i.succ * ((A⁻¹).val *ᵥ u) i.succ) = c := by
  let w' : Fin (m + 2) → ℂ := (A⁻¹).val *ᵥ w
  let u' : Fin (m + 2) → ℂ := (A⁻¹).val *ᵥ u
  have hw0 : w' 0 = 0 :=
    inv_mulVec_zero_eq_zero_of_signed_col_orth A hσ hA hvw
  have hu0 : u' 0 = 0 :=
    inv_mulVec_zero_eq_zero_of_signed_col_orth A hσ hA hvu
  calc
    (∑ i : Fin (m + 1),
      ((A⁻¹).val *ᵥ w) i.succ * ((A⁻¹).val *ᵥ u) i.succ)
        = ∑ i : Fin (m + 1), w' i.succ * u' i.succ := by rfl
    _ = ∑ k : Fin (m + 2), w' k * u' k :=
        sum_tail_mul_eq_of_zero_heads w' u' hw0 hu0
    _ = ∑ k : Fin (m + 2), w k * u k := by
        simpa [w', u'] using dot_mulVec_eq (A⁻¹) w u
    _ = c := hwu

end SOComplex

end
