import Mathlib.LinearAlgebra.Dual.Lemmas
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWLowRankAlignment

/-!
# Hall-Wightman common residual-frame support

This file contains the first mechanical subspace facts needed by the
low-rank common residual-frame theorem.  Once the selected spans are aligned,
the residual spans lie in the common orthogonal complement; nondegeneracy of
the selected span then makes the sums with that selected span disjoint.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- A subspace whose vectors are pointwise orthogonal to `M` is contained in
the Minkowski orthogonal complement of `M`. -/
theorem subspace_le_complexMinkowskiOrthogonalSubmodule
    {d : ℕ} {M R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0) :
    R ≤ complexMinkowskiOrthogonalSubmodule d M := by
  intro x hx
  rw [mem_complexMinkowskiOrthogonalSubmodule_iff]
  intro m
  exact hR_orth ⟨x, hx⟩ m

/-- If `M` is nondegenerate and `R` is orthogonal to `M`, then the selected
span and the residual span intersect trivially. -/
theorem complexMinkowski_disjoint_of_nondegenerate_orthogonal
    {d : ℕ} {M R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hR_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0) :
    Disjoint M R := by
  rw [Submodule.disjoint_def]
  intro x hxM hxR
  have hx0_sub : (⟨x, hxM⟩ : M) = 0 := by
    apply hM
    intro m
    exact hR_orth ⟨x, hxR⟩ m
  exact show x = 0 from congrArg Subtype.val hx0_sub

/-- The checked selected-span alignment yields residual spans in the common
Minkowski orthogonal complement, disjoint from the selected span, and totally
isotropic.  This is the exact packet consumed by the common residual-frame
Witt-extension step. -/
theorem hw_lowRank_residualSubspaces_orthogonalComplement_after_selectedAlignment
    {d n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S) :
    ∃ (Rleft Rright : Submodule ℂ (Fin (d + 1) → ℂ)),
      Rleft = Submodule.span ℂ (Set.range A.leftResidual) ∧
      Rright = Submodule.span ℂ (Set.range A.rightResidual) ∧
      Rleft ≤ complexMinkowskiOrthogonalSubmodule d A.M ∧
      Rright ≤ complexMinkowskiOrthogonalSubmodule d A.M ∧
      Disjoint A.M Rleft ∧
      Disjoint A.M Rright ∧
      ComplexMinkowskiTotallyIsotropicSubspace d Rleft ∧
      ComplexMinkowskiTotallyIsotropicSubspace d Rright := by
  rcases hw_lowRank_residualSubspaces_after_selectedAlignment
      (d := d) (n := n) (r := r) (z := z) (w := w)
      (I := I) (S := S) A with
    ⟨Rleft, Rright, hRleft_eq, hRright_eq,
      hRleft_orth, hRright_orth, hRleft_iso, hRright_iso⟩
  refine ⟨Rleft, Rright, hRleft_eq, hRright_eq, ?_, ?_, ?_, ?_,
    hRleft_iso, hRright_iso⟩
  · exact subspace_le_complexMinkowskiOrthogonalSubmodule hRleft_orth
  · exact subspace_le_complexMinkowskiOrthogonalSubmodule hRright_orth
  · exact
      complexMinkowski_disjoint_of_nondegenerate_orthogonal
        A.M_nondeg hRleft_orth
  · exact
      complexMinkowski_disjoint_of_nondegenerate_orthogonal
        A.M_nondeg hRright_orth

/-- Inside the span `M ⊔ R`, the two pulled-back summands are complementary
as soon as `M` and `R` are disjoint in the ambient source space. -/
theorem isCompl_comap_sup_subtype_of_disjoint
    {d : ℕ} {M R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hdisj : Disjoint M R) :
    IsCompl
      (M.comap (M ⊔ R).subtype)
      (R.comap (M ⊔ R).subtype) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxM hxR
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hdisj
      (x : Fin (d + 1) → ℂ) hxM hxR
  · rw [codisjoint_iff_le_sup]
    intro x _
    rw [Submodule.mem_sup]
    have hxSup : (x : Fin (d + 1) → ℂ) ∈ M ⊔ R := x.2
    rw [Submodule.mem_sup] at hxSup
    rcases hxSup with ⟨m, hm, r, hr, hsum⟩
    refine ⟨⟨m, ?_⟩, hm, ⟨r, ?_⟩, hr, ?_⟩
    · exact Submodule.mem_sup_left hm
    · exact Submodule.mem_sup_right hr
    · apply Subtype.ext
      simpa using hsum

/-- The direct sum of the identity on the selected nondegenerate span with an
injective residual embedding, viewed as a linear equivalence between the two
ambient sup submodules.  Pairing preservation is proved separately from the
block formulas and the residual embedding's preservation field. -/
noncomputable def directSum_identity_sum_isotropicEmbedding
    {d : ℕ}
    (M R : Submodule ℂ (Fin (d + 1) → ℂ))
    (E : R →ₗ[ℂ] (Fin (d + 1) → ℂ))
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hR_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0)
    (hE_inj : Function.Injective E)
    (hE_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (E x)
          (m : Fin (d + 1) → ℂ) = 0) :
    ↥(M ⊔ R) ≃ₗ[ℂ] ↥(M ⊔ (LinearMap.range E)) := by
  let Sdom : Submodule ℂ (Fin (d + 1) → ℂ) := M ⊔ R
  let Scod : Submodule ℂ (Fin (d + 1) → ℂ) :=
    M ⊔ (LinearMap.range E)
  let Mdom : Submodule ℂ Sdom := M.comap Sdom.subtype
  let Rdom : Submodule ℂ Sdom := R.comap Sdom.subtype
  let Mcod : Submodule ℂ Scod := M.comap Scod.subtype
  let Rcod : Submodule ℂ Scod := (LinearMap.range E).comap Scod.subtype
  have hdom : IsCompl Mdom Rdom := by
    simpa [Sdom, Mdom, Rdom] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := M) (R := R)
        (complexMinkowski_disjoint_of_nondegenerate_orthogonal hM hR_orth)
  have hRange_orth :
      ∀ x : LinearMap.range E, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0 := by
    intro x m
    rcases x.2 with ⟨r, hr⟩
    rw [← hr]
    exact hE_orth r m
  have hcod : IsCompl Mcod Rcod := by
    simpa [Scod, Mcod, Rcod] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := M) (R := LinearMap.range E)
        (complexMinkowski_disjoint_of_nondegenerate_orthogonal hM hRange_orth)
  let eMdom : Mdom ≃ₗ[ℂ] M :=
    Submodule.comapSubtypeEquivOfLe (show M ≤ Sdom from le_sup_left)
  let eMcod : Mcod ≃ₗ[ℂ] M :=
    Submodule.comapSubtypeEquivOfLe (show M ≤ Scod from le_sup_left)
  let eRdom : Rdom ≃ₗ[ℂ] R :=
    Submodule.comapSubtypeEquivOfLe (show R ≤ Sdom from le_sup_right)
  let eRcod : Rcod ≃ₗ[ℂ] LinearMap.range E :=
    Submodule.comapSubtypeEquivOfLe
      (show LinearMap.range E ≤ Scod from le_sup_right)
  let eRange : R ≃ₗ[ℂ] LinearMap.range E :=
    LinearEquiv.ofInjective E hE_inj
  let eM : Mdom ≃ₗ[ℂ] Mcod := eMdom.trans eMcod.symm
  let eR : Rdom ≃ₗ[ℂ] Rcod := eRdom.trans (eRange.trans eRcod.symm)
  exact (Submodule.prodEquivOfIsCompl Mdom Rdom hdom).symm.trans
    ((eM.prodCongr eR).trans
      (Submodule.prodEquivOfIsCompl Mcod Rcod hcod))

/-- The direct-sum equivalence sends a vector in the residual summand to its
chosen embedded residual vector. -/
theorem directSum_identity_sum_isotropicEmbedding_maps_right
    {d : ℕ}
    {M R : Submodule ℂ (Fin (d + 1) → ℂ)}
    {E : R →ₗ[ℂ] (Fin (d + 1) → ℂ)}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hR_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0)
    (hE_inj : Function.Injective E)
    (hE_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (E x)
          (m : Fin (d + 1) → ℂ) = 0)
    (x : R) :
    ((directSum_identity_sum_isotropicEmbedding
        (d := d) M R E hM hR_orth hE_inj hE_orth)
      ⟨(x : Fin (d + 1) → ℂ), Submodule.mem_sup_right x.2⟩ :
        Fin (d + 1) → ℂ) = E x := by
  let Sdom : Submodule ℂ (Fin (d + 1) → ℂ) := M ⊔ R
  let Scod : Submodule ℂ (Fin (d + 1) → ℂ) :=
    M ⊔ (LinearMap.range E)
  let Mdom : Submodule ℂ Sdom := M.comap Sdom.subtype
  let Rdom : Submodule ℂ Sdom := R.comap Sdom.subtype
  let Mcod : Submodule ℂ Scod := M.comap Scod.subtype
  let Rcod : Submodule ℂ Scod := (LinearMap.range E).comap Scod.subtype
  have hdom : IsCompl Mdom Rdom := by
    simpa [Sdom, Mdom, Rdom] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := M) (R := R)
        (complexMinkowski_disjoint_of_nondegenerate_orthogonal hM hR_orth)
  have hRange_orth :
      ∀ x : LinearMap.range E, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0 := by
    intro x m
    rcases x.2 with ⟨r, hr⟩
    rw [← hr]
    exact hE_orth r m
  have hcod : IsCompl Mcod Rcod := by
    simpa [Scod, Mcod, Rcod] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := M) (R := LinearMap.range E)
        (complexMinkowski_disjoint_of_nondegenerate_orthogonal hM hRange_orth)
  let eMdom : Mdom ≃ₗ[ℂ] M :=
    Submodule.comapSubtypeEquivOfLe (show M ≤ Sdom from le_sup_left)
  let eMcod : Mcod ≃ₗ[ℂ] M :=
    Submodule.comapSubtypeEquivOfLe (show M ≤ Scod from le_sup_left)
  let eRdom : Rdom ≃ₗ[ℂ] R :=
    Submodule.comapSubtypeEquivOfLe (show R ≤ Sdom from le_sup_right)
  let eRcod : Rcod ≃ₗ[ℂ] LinearMap.range E :=
    Submodule.comapSubtypeEquivOfLe
      (show LinearMap.range E ≤ Scod from le_sup_right)
  let eRange : R ≃ₗ[ℂ] LinearMap.range E :=
    LinearEquiv.ofInjective E hE_inj
  let eM : Mdom ≃ₗ[ℂ] Mcod := eMdom.trans eMcod.symm
  let eR : Rdom ≃ₗ[ℂ] Rcod := eRdom.trans (eRange.trans eRcod.symm)
  let T : Sdom ≃ₗ[ℂ] Scod :=
    (Submodule.prodEquivOfIsCompl Mdom Rdom hdom).symm.trans
      ((eM.prodCongr eR).trans
        (Submodule.prodEquivOfIsCompl Mcod Rcod hcod))
  have hTdef :
      directSum_identity_sum_isotropicEmbedding
        (d := d) M R E hM hR_orth hE_inj hE_orth = T := by
    rfl
  rw [hTdef]
  let y : Sdom :=
    ⟨(x : Fin (d + 1) → ℂ), Submodule.mem_sup_right x.2⟩
  let xr : Rdom := ⟨y, x.2⟩
  have hsymm :
      (Submodule.prodEquivOfIsCompl Mdom Rdom hdom).symm y =
        (0, xr) := by
    simpa [y, xr] using
      Submodule.prodEquivOfIsCompl_symm_apply_right Mdom Rdom hdom xr
  have heR_val : ((eR xr : Rcod) : Fin (d + 1) → ℂ) = E x := by
    rfl
  have heM_zero : ((eM (0 : Mdom) : Mcod) : Fin (d + 1) → ℂ) = 0 := by
    rfl
  calc
    ((T y : Scod) : Fin (d + 1) → ℂ)
        = (((Submodule.prodEquivOfIsCompl Mcod Rcod hcod)
            ((eM.prodCongr eR) (0, xr)) : Scod) :
              Fin (d + 1) → ℂ) := by
            dsimp [T]
            rw [hsymm]
    _ = ((eM (0 : Mdom) : Mcod) : Fin (d + 1) → ℂ) +
          ((eR xr : Rcod) : Fin (d + 1) → ℂ) := by
            rfl
    _ = E x := by
            rw [heM_zero, heR_val, zero_add]

/-- The direct-sum equivalence fixes the selected nondegenerate span. -/
theorem directSum_identity_sum_isotropicEmbedding_maps_left
    {d : ℕ}
    {M R : Submodule ℂ (Fin (d + 1) → ℂ)}
    {E : R →ₗ[ℂ] (Fin (d + 1) → ℂ)}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hR_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0)
    (hE_inj : Function.Injective E)
    (hE_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (E x)
          (m : Fin (d + 1) → ℂ) = 0)
    (m : M) :
    ((directSum_identity_sum_isotropicEmbedding
        (d := d) M R E hM hR_orth hE_inj hE_orth)
      ⟨(m : Fin (d + 1) → ℂ), Submodule.mem_sup_left m.2⟩ :
        Fin (d + 1) → ℂ) = m := by
  let Sdom : Submodule ℂ (Fin (d + 1) → ℂ) := M ⊔ R
  let Scod : Submodule ℂ (Fin (d + 1) → ℂ) :=
    M ⊔ (LinearMap.range E)
  let Mdom : Submodule ℂ Sdom := M.comap Sdom.subtype
  let Rdom : Submodule ℂ Sdom := R.comap Sdom.subtype
  let Mcod : Submodule ℂ Scod := M.comap Scod.subtype
  let Rcod : Submodule ℂ Scod := (LinearMap.range E).comap Scod.subtype
  have hdom : IsCompl Mdom Rdom := by
    simpa [Sdom, Mdom, Rdom] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := M) (R := R)
        (complexMinkowski_disjoint_of_nondegenerate_orthogonal hM hR_orth)
  have hRange_orth :
      ∀ x : LinearMap.range E, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0 := by
    intro x m
    rcases x.2 with ⟨r, hr⟩
    rw [← hr]
    exact hE_orth r m
  have hcod : IsCompl Mcod Rcod := by
    simpa [Scod, Mcod, Rcod] using
      isCompl_comap_sup_subtype_of_disjoint
        (d := d) (M := M) (R := LinearMap.range E)
        (complexMinkowski_disjoint_of_nondegenerate_orthogonal hM hRange_orth)
  let eMdom : Mdom ≃ₗ[ℂ] M :=
    Submodule.comapSubtypeEquivOfLe (show M ≤ Sdom from le_sup_left)
  let eMcod : Mcod ≃ₗ[ℂ] M :=
    Submodule.comapSubtypeEquivOfLe (show M ≤ Scod from le_sup_left)
  let eRdom : Rdom ≃ₗ[ℂ] R :=
    Submodule.comapSubtypeEquivOfLe (show R ≤ Sdom from le_sup_right)
  let eRcod : Rcod ≃ₗ[ℂ] LinearMap.range E :=
    Submodule.comapSubtypeEquivOfLe
      (show LinearMap.range E ≤ Scod from le_sup_right)
  let eRange : R ≃ₗ[ℂ] LinearMap.range E :=
    LinearEquiv.ofInjective E hE_inj
  let eM : Mdom ≃ₗ[ℂ] Mcod := eMdom.trans eMcod.symm
  let eR : Rdom ≃ₗ[ℂ] Rcod := eRdom.trans (eRange.trans eRcod.symm)
  let T : Sdom ≃ₗ[ℂ] Scod :=
    (Submodule.prodEquivOfIsCompl Mdom Rdom hdom).symm.trans
      ((eM.prodCongr eR).trans
        (Submodule.prodEquivOfIsCompl Mcod Rcod hcod))
  have hTdef :
      directSum_identity_sum_isotropicEmbedding
        (d := d) M R E hM hR_orth hE_inj hE_orth = T := by
    rfl
  rw [hTdef]
  let y : Sdom :=
    ⟨(m : Fin (d + 1) → ℂ), Submodule.mem_sup_left m.2⟩
  let xm : Mdom := ⟨y, m.2⟩
  have hsymm :
      (Submodule.prodEquivOfIsCompl Mdom Rdom hdom).symm y =
        (xm, 0) := by
    simpa [y, xm] using
      Submodule.prodEquivOfIsCompl_symm_apply_left Mdom Rdom hdom xm
  have heM_val : ((eM xm : Mcod) : Fin (d + 1) → ℂ) = m := by
    rfl
  have heR_zero : ((eR (0 : Rdom) : Rcod) : Fin (d + 1) → ℂ) = 0 := by
    have hz : eR (0 : Rdom) = 0 := map_zero eR
    exact congrArg (fun y : Rcod => (y : Fin (d + 1) → ℂ)) hz
  calc
    ((T y : Scod) : Fin (d + 1) → ℂ)
        = (((Submodule.prodEquivOfIsCompl Mcod Rcod hcod)
            ((eM.prodCongr eR) (xm, 0)) : Scod) :
              Fin (d + 1) → ℂ) := by
            dsimp [T]
            rw [hsymm]
    _ = ((eM xm : Mcod) : Fin (d + 1) → ℂ) +
          ((eR (0 : Rdom) : Rcod) : Fin (d + 1) → ℂ) := by
            rfl
    _ = m := by
            rw [heM_val, heR_zero, add_zero]

/-- The direct-sum equivalence preserves the complex Minkowski pairing when
the residual embedding preserves residual pairings. -/
theorem directSum_identity_sum_isotropicEmbedding_preserves
    {d : ℕ}
    {M R : Submodule ℂ (Fin (d + 1) → ℂ)}
    {E : R →ₗ[ℂ] (Fin (d + 1) → ℂ)}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hR_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0)
    (hE_inj : Function.Injective E)
    (hE_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (E x)
          (m : Fin (d + 1) → ℂ) = 0)
    (hE_preserves :
      ∀ x y : R,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d
            (x : Fin (d + 1) → ℂ)
            (y : Fin (d + 1) → ℂ)) :
    let T :=
      directSum_identity_sum_isotropicEmbedding
        (d := d) M R E hM hR_orth hE_inj hE_orth
    ∀ x y : ↥(M ⊔ R),
      sourceComplexMinkowskiInner d
        ((T x : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ)
        ((T y : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ)
        (y : Fin (d + 1) → ℂ) := by
  intro T x y
  have hfour :
      ∀ a b c e : Fin (d + 1) → ℂ,
        sourceComplexMinkowskiInner d (a + b) (c + e) =
          sourceComplexMinkowskiInner d a c +
            sourceComplexMinkowskiInner d a e +
            sourceComplexMinkowskiInner d b c +
            sourceComplexMinkowskiInner d b e := by
    intro a b c e
    rw [sourceComplexMinkowskiInner_add_left]
    rw [sourceComplexMinkowskiInner_add_right]
    rw [sourceComplexMinkowskiInner_add_right]
    ring
  rcases (Submodule.mem_sup.mp x.2) with ⟨mx0, hmx0, rx0, hrx0, hxsum⟩
  rcases (Submodule.mem_sup.mp y.2) with ⟨my0, hmy0, ry0, hry0, hysum⟩
  let mx : M := ⟨mx0, hmx0⟩
  let rx : R := ⟨rx0, hrx0⟩
  let my : M := ⟨my0, hmy0⟩
  let ry : R := ⟨ry0, hry0⟩
  let xM : ↥(M ⊔ R) :=
    ⟨(mx : Fin (d + 1) → ℂ), Submodule.mem_sup_left mx.2⟩
  let xR : ↥(M ⊔ R) :=
    ⟨(rx : Fin (d + 1) → ℂ), Submodule.mem_sup_right rx.2⟩
  let yM : ↥(M ⊔ R) :=
    ⟨(my : Fin (d + 1) → ℂ), Submodule.mem_sup_left my.2⟩
  let yR : ↥(M ⊔ R) :=
    ⟨(ry : Fin (d + 1) → ℂ), Submodule.mem_sup_right ry.2⟩
  have hx_decomp : x = xM + xR := by
    apply Subtype.ext
    simpa [xM, xR, mx, rx] using hxsum.symm
  have hy_decomp : y = yM + yR := by
    apply Subtype.ext
    simpa [yM, yR, my, ry] using hysum.symm
  have hTx :
      ((T x : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ) =
        (mx : Fin (d + 1) → ℂ) + E rx := by
    calc
      ((T x : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ)
          = ((T (xM + xR) : ↥(M ⊔ LinearMap.range E)) :
              Fin (d + 1) → ℂ) := by rw [hx_decomp]
      _ = ((T xM : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ) +
            ((T xR : ↥(M ⊔ LinearMap.range E)) :
              Fin (d + 1) → ℂ) := by
              exact congrArg
                (fun z : ↥(M ⊔ LinearMap.range E) =>
                  (z : Fin (d + 1) → ℂ))
                (map_add T xM xR)
      _ = (mx : Fin (d + 1) → ℂ) + E rx := by
              rw [directSum_identity_sum_isotropicEmbedding_maps_left
                    (d := d) (M := M) (R := R) (E := E)
                    hM hR_orth hE_inj hE_orth mx,
                  directSum_identity_sum_isotropicEmbedding_maps_right
                    (d := d) (M := M) (R := R) (E := E)
                    hM hR_orth hE_inj hE_orth rx]
  have hTy :
      ((T y : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ) =
        (my : Fin (d + 1) → ℂ) + E ry := by
    calc
      ((T y : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ)
          = ((T (yM + yR) : ↥(M ⊔ LinearMap.range E)) :
              Fin (d + 1) → ℂ) := by rw [hy_decomp]
      _ = ((T yM : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ) +
            ((T yR : ↥(M ⊔ LinearMap.range E)) :
              Fin (d + 1) → ℂ) := by
              exact congrArg
                (fun z : ↥(M ⊔ LinearMap.range E) =>
                  (z : Fin (d + 1) → ℂ))
                (map_add T yM yR)
      _ = (my : Fin (d + 1) → ℂ) + E ry := by
              rw [directSum_identity_sum_isotropicEmbedding_maps_left
                    (d := d) (M := M) (R := R) (E := E)
                    hM hR_orth hE_inj hE_orth my,
                  directSum_identity_sum_isotropicEmbedding_maps_right
                    (d := d) (M := M) (R := R) (E := E)
                    hM hR_orth hE_inj hE_orth ry]
  have hx_val :
      (x : Fin (d + 1) → ℂ) =
        (mx : Fin (d + 1) → ℂ) + (rx : Fin (d + 1) → ℂ) := by
    simpa [mx, rx] using hxsum.symm
  have hy_val :
      (y : Fin (d + 1) → ℂ) =
        (my : Fin (d + 1) → ℂ) + (ry : Fin (d + 1) → ℂ) := by
    simpa [my, ry] using hysum.symm
  have h_mx_Ery :
      sourceComplexMinkowskiInner d (mx : Fin (d + 1) → ℂ) (E ry) = 0 := by
    rw [sourceComplexMinkowskiInner_comm]
    exact hE_orth ry mx
  have h_Erx_my :
      sourceComplexMinkowskiInner d (E rx) (my : Fin (d + 1) → ℂ) = 0 :=
    hE_orth rx my
  have h_mx_ry :
      sourceComplexMinkowskiInner d
        (mx : Fin (d + 1) → ℂ) (ry : Fin (d + 1) → ℂ) = 0 := by
    rw [sourceComplexMinkowskiInner_comm]
    exact hR_orth ry mx
  have h_rx_my :
      sourceComplexMinkowskiInner d
        (rx : Fin (d + 1) → ℂ) (my : Fin (d + 1) → ℂ) = 0 :=
    hR_orth rx my
  rw [hTx, hTy, hx_val, hy_val]
  rw [hfour, hfour]
  rw [h_mx_Ery, h_Erx_my, h_mx_ry, h_rx_my, hE_preserves rx ry]

/-- A totally isotropic subspace embeds injectively into the span of an
independent totally isotropic frame once its finrank is no larger than the
frame length.  Pairing preservation is automatic because both source and
target residual blocks are totally isotropic. -/
theorem complexMinkowski_totallyIsotropic_embedding_into_frame
    {d s : ℕ}
    {R : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q : Fin s → Fin (d + 1) → ℂ}
    (hq_independent : LinearIndependent ℂ q)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (hdim : Module.finrank ℂ R ≤ s) :
    ∃ E : R →ₗ[ℂ] (Fin (d + 1) → ℂ),
      Function.Injective E ∧
      (∀ x : R, E x ∈ Submodule.span ℂ (Set.range q)) ∧
      ∀ x y : R,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d
            (x : Fin (d + 1) → ℂ)
            (y : Fin (d + 1) → ℂ) := by
  let k := Module.finrank ℂ R
  let b := Module.finBasis ℂ R
  let ι : Fin k → Fin s := Fin.castLE hdim
  let L : (Fin k → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ) := {
    toFun := fun a => ∑ i : Fin k, a i • q (ι i)
    map_add' := by
      intro a b'
      ext μ
      simp [Pi.add_apply, Finset.sum_add_distrib, add_smul]
    map_smul' := by
      intro c a
      ext μ
      simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }
  let E : R →ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    L.comp b.equivFunL.toLinearMap
  refine ⟨E, ?_, ?_, ?_⟩
  · intro x y hxy
    apply b.equivFunL.injective
    ext i
    have hli_sub : LinearIndependent ℂ (fun i : Fin k => q (ι i)) :=
      hq_independent.comp ι (Fin.castLE_injective hdim)
    have hsum :
        (∑ i : Fin k,
          (b.equivFunL x - b.equivFunL y) i • q (ι i)) = 0 := by
      have hdiff : E (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      simpa [E, L, sub_eq_add_neg, Pi.sub_apply] using hdiff
    have hcoeff := Fintype.linearIndependent_iff.mp hli_sub
      (fun i : Fin k => (b.equivFunL x - b.equivFunL y) i) hsum
    have hi := hcoeff i
    exact sub_eq_zero.mp (by simpa [Pi.sub_apply] using hi)
  · intro x
    change (∑ i : Fin k, b.equivFunL x i • q (ι i)) ∈
      Submodule.span ℂ (Set.range q)
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ (b.equivFunL x i)
        (Submodule.subset_span ⟨ι i, rfl⟩)
  · intro x y
    have hQiso :=
      complexMinkowskiTotallyIsotropic_span_range d s q hq_pair_zero
    have hEx_mem : E x ∈ Submodule.span ℂ (Set.range q) := by
      change (∑ i : Fin k, b.equivFunL x i • q (ι i)) ∈
        Submodule.span ℂ (Set.range q)
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (b.equivFunL x i)
          (Submodule.subset_span ⟨ι i, rfl⟩)
    have hEy_mem : E y ∈ Submodule.span ℂ (Set.range q) := by
      change (∑ i : Fin k, b.equivFunL y i • q (ι i)) ∈
        Submodule.span ℂ (Set.range q)
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (b.equivFunL y i)
          (Submodule.subset_span ⟨ι i, rfl⟩)
    rw [hQiso ⟨E x, hEx_mem⟩ ⟨E y, hEy_mem⟩, hR_iso x y]

/-- Given an independent totally isotropic frame orthogonal to `M`, a
totally isotropic residual subspace of no larger finrank produces the
injective residual embedding and the associated pairing-preserving direct-sum
equivalence. -/
theorem directSum_identity_sum_isotropicFrameEmbedding
    {d s : ℕ}
    {M R : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q : Fin s → Fin (d + 1) → ℂ}
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hR_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0)
    (hq_independent : LinearIndependent ℂ q)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hq_orth_M :
      ∀ c (m : M),
        sourceComplexMinkowskiInner d (q c)
          (m : Fin (d + 1) → ℂ) = 0)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (hdim : Module.finrank ℂ R ≤ s) :
    ∃ (E : R →ₗ[ℂ] (Fin (d + 1) → ℂ))
      (hE_inj : Function.Injective E)
      (hE_orth :
        ∀ x : R, ∀ m : M,
          sourceComplexMinkowskiInner d (E x)
            (m : Fin (d + 1) → ℂ) = 0),
      (∀ x : R, E x ∈ Submodule.span ℂ (Set.range q)) ∧
      (∀ x y : R,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d
            (x : Fin (d + 1) → ℂ)
            (y : Fin (d + 1) → ℂ)) ∧
      let T := directSum_identity_sum_isotropicEmbedding
        (d := d) M R E hM hR_orth hE_inj hE_orth
      ∀ x y : ↥(M ⊔ R),
        sourceComplexMinkowskiInner d
          ((T x : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ)
          ((T y : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ) := by
  rcases complexMinkowski_totallyIsotropic_embedding_into_frame
      (d := d) (s := s) (R := R) (q := q)
      hq_independent hq_pair_zero hR_iso hdim with
    ⟨E, hE_inj, hE_mem, hE_preserves⟩
  have hE_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d (E x)
          (m : Fin (d + 1) → ℂ) = 0 := by
    intro x m
    exact span_frame_orthogonal_to_subspace
      (d := d) (s := s) (M := M) (q := q)
      hq_orth_M (hE_mem x) m
  refine ⟨E, hE_inj, hE_orth, hE_mem, hE_preserves, ?_⟩
  exact directSum_identity_sum_isotropicEmbedding_preserves
    (d := d) (M := M) (R := R) (E := E)
    hM hR_orth hE_inj hE_orth hE_preserves

/-- A finite family whose values lie in the span of a finite frame has
coefficient functions on that frame. -/
theorem coefficients_of_family_mem_span_finite_frame
    {d n s : ℕ}
    {q : Fin s → Fin (d + 1) → ℂ}
    {v : Fin n → Fin (d + 1) → ℂ}
    (hv : ∀ i, v i ∈ Submodule.span ℂ (Set.range q)) :
    ∃ a : Fin n → Fin s → ℂ,
      ∀ i, v i = ∑ c : Fin s, a i c • q c := by
  choose a ha using fun i =>
    exists_coefficients_of_mem_span_finite_frame (hv i)
  exact ⟨a, ha⟩

/-- A raw frame dual to a totally isotropic frame can be corrected, inside the
same subspace, to an isotropic dual frame.  The correction is the standard
Gram-matrix half-subtraction
`y c - (1 / 2) • ∑ k, ⟪y c, y k⟫ • q k`; the `q`-dual pairings are unchanged
because the `q`-frame is totally isotropic, and the self-pairings cancel by
symmetry of the complex Minkowski form. -/
theorem complexMinkowski_isotropicDualFrame_of_rawDualFrame
    {d s : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q y : Fin s → Fin (d + 1) → ℂ}
    (hq_mem : ∀ c, q c ∈ N)
    (hy_mem : ∀ c, y c ∈ N)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hy_dual :
      ∀ c c',
        sourceComplexMinkowskiInner d (q c) (y c') =
          if c = c' then (1 : ℂ) else 0) :
    ∃ qDual : Fin s → Fin (d + 1) → ℂ,
      (∀ c, qDual c ∈ N) ∧
      (∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0) ∧
      ∀ c c',
        sourceComplexMinkowskiInner d (q c) (qDual c') =
          if c = c' then (1 : ℂ) else 0 := by
  let corr : Fin s → Fin (d + 1) → ℂ :=
    fun c => (2 : ℂ)⁻¹ •
      (∑ k : Fin s, sourceComplexMinkowskiInner d (y c) (y k) • q k)
  let qDual : Fin s → Fin (d + 1) → ℂ := fun c => y c - corr c
  refine ⟨qDual, ?_, ?_, ?_⟩
  · intro c
    apply Submodule.sub_mem
    · exact hy_mem c
    · apply Submodule.smul_mem
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (hq_mem k)
  · intro i j
    have h_y_corr :
        sourceComplexMinkowskiInner d (y i) (corr j) =
          (2 : ℂ)⁻¹ * sourceComplexMinkowskiInner d (y i) (y j) := by
      change sourceComplexMinkowskiInner d (y i)
          ((2 : ℂ)⁻¹ •
            (∑ k : Fin s, sourceComplexMinkowskiInner d (y j) (y k) • q k)) = _
      rw [sourceComplexMinkowskiInner_smul_right,
        sourceComplexMinkowskiInner_sum_smul_right]
      have hsum :
          (∑ k : Fin s,
              sourceComplexMinkowskiInner d (y j) (y k) *
                sourceComplexMinkowskiInner d (y i) (q k)) =
            sourceComplexMinkowskiInner d (y j) (y i) := by
        calc
          (∑ k : Fin s,
              sourceComplexMinkowskiInner d (y j) (y k) *
                sourceComplexMinkowskiInner d (y i) (q k)) =
            ∑ k : Fin s,
              sourceComplexMinkowskiInner d (y j) (y k) *
                (if k = i then (1 : ℂ) else 0) := by
                apply Finset.sum_congr rfl
                intro k _
                rw [sourceComplexMinkowskiInner_comm d (y i) (q k),
                  hy_dual]
          _ = sourceComplexMinkowskiInner d (y j) (y i) := by
                simp
      rw [hsum]
      rw [sourceComplexMinkowskiInner_comm d (y j) (y i)]
    have h_corr_y :
        sourceComplexMinkowskiInner d (corr i) (y j) =
          (2 : ℂ)⁻¹ * sourceComplexMinkowskiInner d (y i) (y j) := by
      change sourceComplexMinkowskiInner d
          ((2 : ℂ)⁻¹ •
            (∑ k : Fin s, sourceComplexMinkowskiInner d (y i) (y k) • q k))
          (y j) = _
      rw [sourceComplexMinkowskiInner_smul_left,
        sourceComplexMinkowskiInner_sum_smul_left]
      have hsum :
          (∑ k : Fin s,
              sourceComplexMinkowskiInner d (y i) (y k) *
                sourceComplexMinkowskiInner d (q k) (y j)) =
            sourceComplexMinkowskiInner d (y i) (y j) := by
        calc
          (∑ k : Fin s,
              sourceComplexMinkowskiInner d (y i) (y k) *
                sourceComplexMinkowskiInner d (q k) (y j)) =
            ∑ k : Fin s,
              sourceComplexMinkowskiInner d (y i) (y k) *
                (if k = j then (1 : ℂ) else 0) := by
                apply Finset.sum_congr rfl
                intro k _
                rw [hy_dual]
          _ = sourceComplexMinkowskiInner d (y i) (y j) := by
                simp
      rw [hsum]
    have h_corr_corr :
        sourceComplexMinkowskiInner d (corr i) (corr j) = 0 := by
      change sourceComplexMinkowskiInner d
          ((2 : ℂ)⁻¹ •
            (∑ k : Fin s, sourceComplexMinkowskiInner d (y i) (y k) • q k))
          ((2 : ℂ)⁻¹ •
            (∑ k : Fin s, sourceComplexMinkowskiInner d (y j) (y k) • q k)) = 0
      rw [sourceComplexMinkowskiInner_smul_left,
        sourceComplexMinkowskiInner_smul_right,
        sourceComplexMinkowskiInner_sum_smul_left]
      simp [sourceComplexMinkowskiInner_sum_smul_right, hq_pair_zero]
    change sourceComplexMinkowskiInner d (y i - corr i) (y j - corr j) = 0
    rw [sourceComplexMinkowskiInner_sub_left,
      sourceComplexMinkowskiInner_sub_right,
      sourceComplexMinkowskiInner_sub_right]
    rw [h_y_corr, h_corr_y, h_corr_corr]
    ring
  · intro i j
    have hq_corr : sourceComplexMinkowskiInner d (q i) (corr j) = 0 := by
      change sourceComplexMinkowskiInner d (q i)
          ((2 : ℂ)⁻¹ •
            (∑ k : Fin s, sourceComplexMinkowskiInner d (y j) (y k) • q k)) = 0
      rw [sourceComplexMinkowskiInner_smul_right,
        sourceComplexMinkowskiInner_sum_smul_right]
      simp [hq_pair_zero]
    change sourceComplexMinkowskiInner d (q i) (y j - corr j) = _
    rw [sourceComplexMinkowskiInner_sub_right, hq_corr, sub_zero, hy_dual]

/-- In a nondegenerate subspace, an independent finite frame has raw dual
vectors for the restricted complex Minkowski pairing.  These raw duals are not
yet isotropic; `complexMinkowski_isotropicDualFrame_of_rawDualFrame` performs
the subsequent isotropization when the original frame is totally isotropic. -/
theorem complexMinkowski_rawDualFrameIn
    {d s : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q : Fin s → Fin (d + 1) → ℂ}
    (hN : ComplexMinkowskiNondegenerateSubspace d N)
    (hq_mem : ∀ c, q c ∈ N)
    (hq_independent : LinearIndependent ℂ q) :
    ∃ y : Fin s → Fin (d + 1) → ℂ,
      (∀ c, y c ∈ N) ∧
      ∀ c c',
        sourceComplexMinkowskiInner d (q c) (y c') =
          if c = c' then (1 : ℂ) else 0 := by
  let qN : Fin s → N := fun c => ⟨q c, hq_mem c⟩
  have hqN_independent : LinearIndependent ℂ qN := by
    rw [Fintype.linearIndependent_iff]
    intro a hsum i
    have hsum_val : (∑ j : Fin s, a j • q j) = 0 := by
      have h := congrArg (fun x : N => (x : Fin (d + 1) → ℂ)) hsum
      simpa [qN] using h
    exact (Fintype.linearIndependent_iff.mp hq_independent a hsum_val) i
  let Q : Submodule ℂ N := Submodule.span ℂ (Set.range qN)
  let bQ : Module.Basis (Fin s) ℂ Q := Module.Basis.span hqN_independent
  let B := (sourceComplexMinkowskiBilinForm d).restrict N
  have hBnd : B.Nondegenerate := by
    simpa [B] using complexMinkowskiNondegenerateSubspace_to_restrict d N hN
  let phi : Fin s → Module.Dual ℂ N := fun c =>
    Subspace.dualLift Q (bQ.coord c)
  let yN : Fin s → N := fun c => (B.toDual hBnd).symm (phi c)
  let y : Fin s → Fin (d + 1) → ℂ := fun c => yN c
  refine ⟨y, ?_, ?_⟩
  · intro c
    exact (yN c).2
  · intro i j
    have hraw : B (yN j) (qN i) = if i = j then (1 : ℂ) else 0 := by
      calc
        B (yN j) (qN i) = phi j (qN i) := by
          simp [yN]
        _ = bQ.coord j ⟨qN i, Submodule.subset_span ⟨i, rfl⟩⟩ := by
          change (Subspace.dualLift Q (bQ.coord j)) (qN i) =
            bQ.coord j ⟨qN i, Submodule.subset_span ⟨i, rfl⟩⟩
          exact Subspace.dualLift_of_mem (W := Q) (φ := bQ.coord j)
            (show qN i ∈ Q from Submodule.subset_span ⟨i, rfl⟩)
        _ = if i = j then (1 : ℂ) else 0 := by
          by_cases hij : i = j <;> simp [bQ, Q, hij]
    have hraw' :
        sourceComplexMinkowskiInner d (y j) (q i) =
          if i = j then (1 : ℂ) else 0 := by
      change B (yN j) (qN i) = if i = j then (1 : ℂ) else 0
      exact hraw
    rw [sourceComplexMinkowskiInner_comm d (q i) (y j)]
    exact hraw'

/-- An independent totally isotropic frame in a nondegenerate subspace admits an
isotropic dual frame inside the same subspace.  This is the finite-dimensional
dual-frame packet used by the low-rank null-boost construction. -/
theorem complexMinkowski_isotropicFrame_dualFrameIn
    {d s : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hN : ComplexMinkowskiNondegenerateSubspace d N)
    {q : Fin s → Fin (d + 1) → ℂ}
    (hq_mem : ∀ c, q c ∈ N)
    (hq_independent : LinearIndependent ℂ q)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0) :
    ∃ qDual : Fin s → Fin (d + 1) → ℂ,
      (∀ c, qDual c ∈ N) ∧
      (∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0) ∧
      ∀ c c',
        sourceComplexMinkowskiInner d (q c) (qDual c') =
          if c = c' then (1 : ℂ) else 0 := by
  rcases complexMinkowski_rawDualFrameIn
      (d := d) (s := s) (N := N) (q := q)
      hN hq_mem hq_independent with
    ⟨y, hy_mem, hy_dual⟩
  exact complexMinkowski_isotropicDualFrame_of_rawDualFrame
    (d := d) (s := s) (N := N) (q := q) (y := y)
    hq_mem hy_mem hq_pair_zero hy_dual

/-- A residual isotropic frame orthogonal to a nondegenerate selected span has
an isotropic dual frame in the same orthogonal complement.  The returned
orthogonality-to-`ξ` field is just orthogonality to `M`, since the base vectors
lie in `M`. -/
theorem complexMinkowski_isotropicDualFrame_of_residualFrame
    {d n s : ℕ}
    {ξ : Fin n → Fin (d + 1) → ℂ}
    {q : Fin s → Fin (d + 1) → ℂ}
    {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hM_nondeg : ComplexMinkowskiNondegenerateSubspace d M)
    (hξ_mem : ∀ i, ξ i ∈ M)
    (hq_orth_M :
      ∀ c (m : M),
        sourceComplexMinkowskiInner d
          (q c) (m : Fin (d + 1) → ℂ) = 0)
    (hq_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0)
    (hq_independent : LinearIndependent ℂ q) :
    ∃ qDual : Fin s → Fin (d + 1) → ℂ,
      (∀ c c', sourceComplexMinkowskiInner d (qDual c) (qDual c') = 0) ∧
      (∀ c c',
        sourceComplexMinkowskiInner d (q c) (qDual c') =
          if c = c' then (1 : ℂ) else 0) ∧
      (∀ c (m : M),
        sourceComplexMinkowskiInner d
          (qDual c) (m : Fin (d + 1) → ℂ) = 0) ∧
      ∀ c i, sourceComplexMinkowskiInner d (qDual c) (ξ i) = 0 := by
  let N := complexMinkowskiOrthogonalSubmodule d M
  have hN : ComplexMinkowskiNondegenerateSubspace d N :=
    complexMinkowskiOrthogonalSubmodule_nondegenerate d hM_nondeg
  have hq_mem : ∀ c, q c ∈ N := by
    intro c
    change q c ∈ complexMinkowskiOrthogonalSubmodule d M
    rw [mem_complexMinkowskiOrthogonalSubmodule_iff]
    intro m
    exact hq_orth_M c m
  rcases complexMinkowski_isotropicFrame_dualFrameIn
      (d := d) (s := s) (N := N)
      hN hq_mem hq_independent hq_pair_zero with
    ⟨qDual, hqDual_mem, hqDual_pair_zero, hq_dual⟩
  have hqDual_orth_M :
      ∀ c (m : M),
        sourceComplexMinkowskiInner d
          (qDual c) (m : Fin (d + 1) → ℂ) = 0 := by
    intro c m
    exact
      (mem_complexMinkowskiOrthogonalSubmodule_iff d M (qDual c)).1
        (by simpa [N] using hqDual_mem c) m
  refine ⟨qDual, hqDual_pair_zero, hq_dual, hqDual_orth_M, ?_⟩
  intro c i
  exact hqDual_orth_M c ⟨ξ i, hξ_mem i⟩

/-- A finite residual expansion with all coefficients scaled by `exp (-t)`
converges to the base configuration.  This is the convergence calculation used
by the low-rank singular normal-form producer; it depends only on finite
products and `exp (-t) → 0`, not on any continuity of the chosen Lorentz
transform family. -/
theorem tendsto_isotropicResidual_exp_neg_base
    {d n s : ℕ}
    (ξ : Fin n → Fin (d + 1) → ℂ)
    (a : Fin n → Fin s → ℂ)
    (q : Fin s → Fin (d + 1) → ℂ) :
    Tendsto
      (fun t : ℝ =>
        fun i μ =>
          ξ i μ + ∑ c : Fin s, (Real.exp (-t) : ℂ) * a i c * q c μ)
      atTop (nhds ξ) := by
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro μ
  have hsum :
      Tendsto
        (fun t : ℝ =>
          ∑ c : Fin s, (Real.exp (-t) : ℂ) * a i c * q c μ)
        atTop (nhds (0 : ℂ)) := by
    simpa using
      tendsto_finset_sum (s := Finset.univ)
        (fun c _ =>
          (tendsto_complex_exp_neg_atTop_nhds_zero.mul
            (tendsto_const_nhds (x := a i c))).mul
            (tendsto_const_nhds (x := q c μ)))
  have hconst : Tendsto (fun _ : ℝ => ξ i μ) atTop (nhds (ξ i μ)) :=
    tendsto_const_nhds
  simpa using hconst.add hsum

end BHW
