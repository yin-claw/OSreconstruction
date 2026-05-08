import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWMaximalIsotropicFrame
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Quotient preimages for Hall-Wightman maximal isotropic frames

This file keeps the next quotient/rank-nullity support for
`complexMinkowski_maximalIsotropicFrameIn_extending` outside the already large
maximal-frame file.  The declarations here start the concrete preimage packet
for the quotient `Rperp / R`: define the preimage in `Rperp`, retype it in `N`
and in original source coordinates, and prove the original-coordinate preimage
remains inside `N` and contains the original totally isotropic subspace.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

set_option maxHeartbeats 800000

local instance complexMinkowskiRelativeOrthogonalHasQuotient
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N) :
    HasQuotient (complexMinkowskiRelativeOrthogonalIn (d := d) N RN)
      (Submodule ℂ (complexMinkowskiRelativeOrthogonalIn (d := d) N RN)) :=
  Submodule.hasQuotient (R := ℂ)
    (M := complexMinkowskiRelativeOrthogonalIn (d := d) N RN)

/-- A subspace is totally isotropic for a bilinear form when every two vectors
in the subspace pair to zero.  This pointwise form avoids quotient-subtype
packaging during the relative-orthogonal argument below. -/
def BilinFormTotallyIsotropicSubspace
    {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (B : LinearMap.BilinForm ℂ V)
    (Q : Submodule ℂ V) : Prop :=
  ∀ {x y : V}, x ∈ Q → y ∈ Q → B x y = 0

/-- Every finite-dimensional vector space with a bilinear form contains a
totally isotropic subspace of maximal finite dimension. -/
theorem bilinForm_maximalTotallyIsotropicSubspace_exists
    {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) :
    ∃ Q : Submodule ℂ V,
      BilinFormTotallyIsotropicSubspace B Q ∧
        ∀ S : Submodule ℂ V,
          BilinFormTotallyIsotropicSubspace B S →
            Module.finrank ℂ S ≤ Module.finrank ℂ Q := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ Q : Submodule ℂ V,
      BilinFormTotallyIsotropicSubspace B Q ∧
        Module.finrank ℂ Q = k
  have hP0 : P 0 := by
    refine ⟨⊥, ?_, ?_⟩
    · intro x y hx _hy
      have hx0 : x = 0 := by
        simpa using (Submodule.mem_bot ℂ).1 hx
      rw [hx0]
      simp
    · simp
  let k := Nat.findGreatest P (Module.finrank ℂ V)
  have hPk : P k := Nat.findGreatest_spec (by simp) hP0
  rcases hPk with ⟨Q, hQ_iso, hQ_rank⟩
  refine ⟨Q, hQ_iso, ?_⟩
  intro S hS_iso
  have hS_bound : Module.finrank ℂ S ≤ Module.finrank ℂ V := by
    simpa using
      Submodule.finrank_mono
        (show S ≤ (⊤ : Submodule ℂ V) from le_top)
  have hP_S : P (Module.finrank ℂ S) :=
    ⟨S, hS_iso, rfl⟩
  have hle : Module.finrank ℂ S ≤ k :=
    Nat.le_findGreatest hS_bound hP_S
  simpa [k, hQ_rank] using hle

/-- Specialized maximal isotropic quotient subspace for the relative-orthogonal
quotient form `Rperp / R`. -/
theorem complexMinkowskiRelativeOrthogonalQuotient_maximalIsotropicSubspace_exists
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N) :
    ∃ Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN),
      BilinFormTotallyIsotropicSubspace
        (complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN)
        Qbar ∧
        ∀ S : Submodule ℂ
          (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
            complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN),
          BilinFormTotallyIsotropicSubspace
            (complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN)
            S →
            Module.finrank ℂ S ≤ Module.finrank ℂ Qbar :=
  bilinForm_maximalTotallyIsotropicSubspace_exists
    (complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN)

/-- The preimage in `Rperp` of a subspace of the quotient `Rperp / R`. -/
def complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN)) :
    Submodule ℂ (complexMinkowskiRelativeOrthogonalIn (d := d) N RN) where
  carrier := {x |
    Submodule.mkQ
      (complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN) x ∈ Qbar}
  zero_mem' := by
    simp
  add_mem' := by
    intro x y hx hy
    exact Qbar.add_mem hx hy
  smul_mem' := by
    intro c x hx
    exact Qbar.smul_mem c hx

/-- The same quotient preimage retyped as a subspace of the ambient subtype
`N`. -/
def complexMinkowskiRelativeOrthogonalQuotientPreimageInN
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN)) :
    Submodule ℂ N :=
  (complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp
    (d := d) (N := N) RN Qbar).map
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN).subtype

/-- The quotient preimage returned to original ambient source coordinates. -/
def complexMinkowskiRelativeOrthogonalQuotientPreimage
    {d : ℕ}
    (N : Submodule ℂ (Fin (d + 1) → ℂ))
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN)) :
    Submodule ℂ (Fin (d + 1) → ℂ) :=
  (complexMinkowskiRelativeOrthogonalQuotientPreimageInN
    (d := d) (N := N) RN Qbar).map N.subtype

/-- The ambient-coordinate quotient preimage remains inside `N`. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimage_le
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN)) :
    complexMinkowskiRelativeOrthogonalQuotientPreimage
      (d := d) N RN Qbar ≤ N := by
  intro x hx
  rcases hx with ⟨xN, _hxN, rfl⟩
  exact xN.2

/-- Any vector in the retyped copy of `R` maps to zero in `Rperp / R`, hence
belongs to every quotient preimage.  This pointwise form keeps elaboration
lighter than the corresponding submodule-order statement. -/
theorem complexMinkowskiSubmoduleInRelativeOrthogonal_mkQ_mem_quotientPreimage
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN))
    (x : complexMinkowskiRelativeOrthogonalIn (d := d) N RN)
    (hx : x ∈
      complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN) :
    Submodule.mkQ
      (complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN) x ∈
        Qbar := by
  rw [Submodule.mkQ_apply]
  have hx0 :
      Submodule.Quotient.mk
          (p := complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN) x =
        Submodule.Quotient.mk
          (p := complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN)
          (0 : complexMinkowskiRelativeOrthogonalIn (d := d) N RN) := by
    apply Quotient.sound'
    let Rin :=
      complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN
    have hxSub :
        x - 0 ∈ Rin := by
      change x + -(0 : complexMinkowskiRelativeOrthogonalIn (d := d) N RN) ∈ Rin
      have hzero : (0 : complexMinkowskiRelativeOrthogonalIn (d := d) N RN) ∈ Rin :=
        Rin.zero_mem
      have hneg : -(0 : complexMinkowskiRelativeOrthogonalIn (d := d) N RN) ∈ Rin :=
        Submodule.neg_mem
          (p := Rin)
          (x := (0 : complexMinkowskiRelativeOrthogonalIn (d := d) N RN))
          hzero
      exact Rin.add_mem hx hneg
    simpa [Submodule.quotientRel_def] using hxSub
  rw [hx0]
  simp

/-- If `R ≤ N` is totally isotropic, then every point of `R` belongs to the
ambient-coordinate preimage of any quotient subspace of `Rperp / R`. -/
theorem complexMinkowskiSubmodule_mem_relativeOrthogonalQuotientPreimage
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N
          (complexMinkowskiSubmoduleIn (d := d) N R) ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N)
          (complexMinkowskiSubmoduleIn (d := d) N R)))
    {x : Fin (d + 1) → ℂ}
    (hx : x ∈ R) :
    x ∈ complexMinkowskiRelativeOrthogonalQuotientPreimage (d := d) N
      (complexMinkowskiSubmoduleIn (d := d) N R) Qbar := by
  let RN := complexMinkowskiSubmoduleIn (d := d) N R
  let Rperp := complexMinkowskiRelativeOrthogonalIn (d := d) N RN
  have hRN_le : RN ≤ Rperp :=
    complexMinkowskiSubmoduleIn_le_relativeOrthogonalIn_of_totallyIsotropic
      (N := N) (R := R) hR_iso
  let xN : N := ⟨x, hR_le hx⟩
  have hxRN : xN ∈ RN := hx
  let xRperp : Rperp := ⟨xN, hRN_le hxRN⟩
  have hxRin : xRperp ∈
      complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN := hxRN
  have hxPre : xRperp ∈
      complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp
        (d := d) (N := N) RN Qbar := by
    exact
      complexMinkowskiSubmoduleInRelativeOrthogonal_mkQ_mem_quotientPreimage
        (d := d) (N := N) RN Qbar xRperp hxRin
  have hxPreN : xN ∈
      complexMinkowskiRelativeOrthogonalQuotientPreimageInN
        (d := d) (N := N) RN Qbar := by
    refine ⟨xRperp, hxPre, ?_⟩
    rfl
  exact ⟨xN, hxPreN, rfl⟩

/-- If `R ≤ N` is totally isotropic, then `R` is contained in every ambient
quotient preimage associated to `Rperp / R`. -/
theorem complexMinkowskiSubmodule_le_relativeOrthogonalQuotientPreimage
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N
          (complexMinkowskiSubmoduleIn (d := d) N R) ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N)
          (complexMinkowskiSubmoduleIn (d := d) N R))) :
    R ≤ complexMinkowskiRelativeOrthogonalQuotientPreimage (d := d) N
      (complexMinkowskiSubmoduleIn (d := d) N R) Qbar := by
  intro x hx
  exact
    complexMinkowskiSubmodule_mem_relativeOrthogonalQuotientPreimage
      (d := d) (N := N) (R := R) hR_le hR_iso Qbar hx

/-- The quotient preimage in `Rperp` is isotropic whenever the quotient
subspace is isotropic for the induced quotient form. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp_pair_zero
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN))
    (hQbar_pair_zero :
      ∀ {x y :
        complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
          complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN},
        x ∈ Qbar →
        y ∈ Qbar →
        complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN
          x y = 0)
    {x y : complexMinkowskiRelativeOrthogonalIn (d := d) N RN}
    (hx : x ∈
      complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp
        (d := d) (N := N) RN Qbar)
    (hy : y ∈
      complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp
        (d := d) (N := N) RN Qbar) :
    sourceComplexMinkowskiInner d
      (((x : complexMinkowskiRelativeOrthogonalIn (d := d) N RN) : N) :
        Fin (d + 1) → ℂ)
      (((y : complexMinkowskiRelativeOrthogonalIn (d := d) N RN) : N) :
        Fin (d + 1) → ℂ) = 0 := by
  change
    Submodule.mkQ
      (complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN) x ∈
        Qbar at hx
  change
    Submodule.mkQ
      (complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN) y ∈
        Qbar at hy
  rw [Submodule.mkQ_apply] at hx hy
  have hxy := hQbar_pair_zero
    (x := Quotient.mk'' x) (y := Quotient.mk'' y) hx hy
  simpa [complexMinkowskiRelativeOrthogonalQuotientForm_mk] using hxy

/-- The quotient preimage retyped in `N` is isotropic whenever the quotient
subspace is isotropic for the induced quotient form. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimageInN_pair_zero
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN))
    (hQbar_pair_zero :
      ∀ {x y :
        complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
          complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN},
        x ∈ Qbar →
        y ∈ Qbar →
        complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN
          x y = 0)
    {x y : N}
    (hx : x ∈
      complexMinkowskiRelativeOrthogonalQuotientPreimageInN
        (d := d) (N := N) RN Qbar)
    (hy : y ∈
      complexMinkowskiRelativeOrthogonalQuotientPreimageInN
        (d := d) (N := N) RN Qbar) :
    sourceComplexMinkowskiInner d
      (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) = 0 := by
  rcases hx with ⟨xperp, hxperp, hx_eq⟩
  rcases hy with ⟨yperp, hyperp, hy_eq⟩
  rw [← hx_eq, ← hy_eq]
  exact
    complexMinkowskiRelativeOrthogonalQuotientPreimageInRperp_pair_zero
      (d := d) (N := N) RN Qbar hQbar_pair_zero hxperp hyperp

/-- The ambient-coordinate quotient preimage is a totally isotropic source
subspace whenever the quotient subspace is isotropic for the induced quotient
form. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimage_isotropic
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N)
    (Qbar : Submodule ℂ
      (complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
        complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN))
    (hQbar_pair_zero :
      ∀ {x y :
        complexMinkowskiRelativeOrthogonalIn (d := d) N RN ⧸
          complexMinkowskiSubmoduleInRelativeOrthogonal (d := d) (N := N) RN},
        x ∈ Qbar →
        y ∈ Qbar →
        complexMinkowskiRelativeOrthogonalQuotientForm (d := d) (N := N) RN
          x y = 0) :
    ComplexMinkowskiTotallyIsotropicSubspace d
      (complexMinkowskiRelativeOrthogonalQuotientPreimage (d := d) N RN Qbar) := by
  intro x y
  rcases x.2 with ⟨xN, hxN, hx_eq⟩
  rcases y.2 with ⟨yN, hyN, hy_eq⟩
  rw [← hx_eq, ← hy_eq]
  exact
    complexMinkowskiRelativeOrthogonalQuotientPreimageInN_pair_zero
      (d := d) (N := N) RN Qbar hQbar_pair_zero hxN hyN

end BHW
