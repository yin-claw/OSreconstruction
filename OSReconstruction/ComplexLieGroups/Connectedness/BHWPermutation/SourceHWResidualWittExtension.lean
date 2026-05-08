import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWMaximalIsotropicFrame

/-!
# Nondegenerate block extension for Hall-Wightman residual Witt geometry

This file isolates the nondegenerate part of the remaining low-rank residual
extension theorem.  After the future construction adjoins hyperbolic duals to
the degenerate residual blocks, the resulting pairing-preserving equivalence is
between nondegenerate subspaces.  The theorems below extend that equivalence to
the full ambient complex Minkowski space by matching orthogonal complements.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- Nondegenerate orthogonal complements of same-finrank nondegenerate
subspaces are linearly isometric for the complex Minkowski form. -/
theorem exists_complexMinkowskiOrthogonalComplementIsometry_of_finrank_eq
    {d : ℕ}
    {K L : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hK : ComplexMinkowskiNondegenerateSubspace d K)
    (hL : ComplexMinkowskiNondegenerateSubspace d L)
    (hfin : Module.finrank ℂ K = Module.finrank ℂ L) :
    ∃ C :
        complexMinkowskiOrthogonalSubmodule d K ≃ₗ[ℂ]
          complexMinkowskiOrthogonalSubmodule d L,
      ∀ x y,
        sourceComplexMinkowskiInner d
          ((C x : complexMinkowskiOrthogonalSubmodule d L) :
            Fin (d + 1) → ℂ)
          ((C y : complexMinkowskiOrthogonalSubmodule d L) :
            Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ) := by
  let B := sourceComplexMinkowskiBilinForm d
  have hB_nd : B.Nondegenerate :=
    sourceComplexMinkowskiBilinForm_nondegenerate d
  have hB_symm : B.IsSymm :=
    sourceComplexMinkowskiBilinForm_isSymm d
  have hOK_nd :
      (B.restrict (complexMinkowskiOrthogonalSubmodule d K)).Nondegenerate :=
    complexMinkowskiNondegenerateSubspace_to_restrict
      d _
      (complexMinkowskiOrthogonalSubmodule_nondegenerate d hK)
  have hOL_nd :
      (B.restrict (complexMinkowskiOrthogonalSubmodule d L)).Nondegenerate :=
    complexMinkowskiNondegenerateSubspace_to_restrict
      d _
      (complexMinkowskiOrthogonalSubmodule_nondegenerate d hL)
  have hfin_comp :
      Module.finrank ℂ (complexMinkowskiOrthogonalSubmodule d K) =
        Module.finrank ℂ (complexMinkowskiOrthogonalSubmodule d L) := by
    have hK_orth :=
      LinearMap.BilinForm.finrank_orthogonal (B := B) hB_nd K
    have hL_orth :=
      LinearMap.BilinForm.finrank_orthogonal (B := B) hB_nd L
    rw [
      sourceComplexMinkowskiBilinForm_orthogonal_eq_complexMinkowskiOrthogonalSubmodule
        d K] at hK_orth
    rw [
      sourceComplexMinkowskiBilinForm_orthogonal_eq_complexMinkowskiOrthogonalSubmodule
        d L] at hL_orth
    omega
  rcases
    nondegenerate_complexSymmetricBilinForm_linearEquiv_of_finrank_eq
      (B.restrict (complexMinkowskiOrthogonalSubmodule d K))
      (B.restrict (complexMinkowskiOrthogonalSubmodule d L))
      (restrict_isSymm_of_isSymm hB_symm _)
      (restrict_isSymm_of_isSymm hB_symm _)
      hOK_nd hOL_nd hfin_comp with
  ⟨C, hC⟩
  exact ⟨C, by
    intro x y
    simpa [LinearMap.BilinForm.restrict, B,
      sourceComplexMinkowskiBilinForm] using hC x y⟩

/-- A pairing-preserving equivalence between nondegenerate complex-Minkowski
subspaces extends to a pairing-preserving ambient linear equivalence. -/
theorem complexMinkowski_nondegenerateSubspaceEquiv_ambientExtension
    {d : ℕ}
    {K L : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hK : ComplexMinkowskiNondegenerateSubspace d K)
    (hL : ComplexMinkowskiNondegenerateSubspace d L)
    (T : K ≃ₗ[ℂ] L)
    (hT :
      ∀ x y,
        sourceComplexMinkowskiInner d
          (T x : Fin (d + 1) → ℂ)
          (T y : Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ)) :
    ∃ E : (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ),
      (∀ x y,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d x y) ∧
      ∀ x : K, E (x : Fin (d + 1) → ℂ) = (T x : Fin (d + 1) → ℂ) := by
  rcases
    exists_complexMinkowskiOrthogonalComplementIsometry_of_finrank_eq
      (d := d) hK hL T.finrank_eq with
  ⟨C, hC⟩
  let B := sourceComplexMinkowskiBilinForm d
  have hK_rest : (B.restrict K).Nondegenerate :=
    complexMinkowskiNondegenerateSubspace_to_restrict d K hK
  have hL_rest : (B.restrict L).Nondegenerate :=
    complexMinkowskiNondegenerateSubspace_to_restrict d L hL
  have hK_compl0 : IsCompl K (B.orthogonal K) :=
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
      (B := B) (W := K)
      (sourceComplexMinkowskiBilinForm_isRefl d)).mp hK_rest
  have hL_compl0 : IsCompl L (B.orthogonal L) :=
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
      (B := B) (W := L)
      (sourceComplexMinkowskiBilinForm_isRefl d)).mp hL_rest
  have hK_compl :
      IsCompl K (complexMinkowskiOrthogonalSubmodule d K) := by
    simpa [B,
      sourceComplexMinkowskiBilinForm_orthogonal_eq_complexMinkowskiOrthogonalSubmodule
        d K] using hK_compl0
  have hL_compl :
      IsCompl L (complexMinkowskiOrthogonalSubmodule d L) := by
    simpa [B,
      sourceComplexMinkowskiBilinForm_orthogonal_eq_complexMinkowskiOrthogonalSubmodule
        d L] using hL_compl0
  let OK := complexMinkowskiOrthogonalSubmodule d K
  let OL := complexMinkowskiOrthogonalSubmodule d L
  let eK : (K × OK) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    Submodule.prodEquivOfIsCompl K OK hK_compl
  let eL : (L × OL) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    Submodule.prodEquivOfIsCompl L OL hL_compl
  let P : (K × OK) ≃ₗ[ℂ] (L × OL) :=
    T.prodCongr C
  let E : (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    eK.symm.trans (P.trans eL)
  refine ⟨E, ?_, ?_⟩
  · intro x y
    let xu : K × OK := eK.symm x
    let yv : K × OK := eK.symm y
    calc
      sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d (eL (P xu)) (eL (P yv)) := by
            simp [E, xu, yv]
      _ =
          sourceComplexMinkowskiInner d
            ((P xu).1 : Fin (d + 1) → ℂ)
            ((P yv).1 : Fin (d + 1) → ℂ) +
          sourceComplexMinkowskiInner d
            ((P xu).2 : Fin (d + 1) → ℂ)
            ((P yv).2 : Fin (d + 1) → ℂ) := by
            exact sourceInner_prodEquivOfIsCompl L hL_compl (P xu) (P yv)
      _ =
          sourceComplexMinkowskiInner d
            (xu.1 : Fin (d + 1) → ℂ)
            (yv.1 : Fin (d + 1) → ℂ) +
          sourceComplexMinkowskiInner d
            (xu.2 : Fin (d + 1) → ℂ)
            (yv.2 : Fin (d + 1) → ℂ) := by
            simp [P, hT, hC]
      _ = sourceComplexMinkowskiInner d (eK xu) (eK yv) := by
            rw [sourceInner_prodEquivOfIsCompl K hK_compl xu yv]
      _ = sourceComplexMinkowskiInner d x y := by
            simp [xu, yv]
  · intro x
    have hx :
        eK.symm (x : Fin (d + 1) → ℂ) = (x, (0 : OK)) := by
      exact Submodule.prodEquivOfIsCompl_symm_apply_left K OK hK_compl x
    calc
      E (x : Fin (d + 1) → ℂ) =
          eL (P (eK.symm (x : Fin (d + 1) → ℂ))) := by
            rfl
      _ = eL (P (x, (0 : OK))) := by
            rw [hx]
      _ = eL (T x, (0 : OL)) := by
            simp [P]
      _ = (T x : Fin (d + 1) → ℂ) := by
            simp [eL]

end BHW
