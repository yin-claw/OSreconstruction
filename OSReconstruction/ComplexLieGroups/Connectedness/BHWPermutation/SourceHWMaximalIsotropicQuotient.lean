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

end BHW
