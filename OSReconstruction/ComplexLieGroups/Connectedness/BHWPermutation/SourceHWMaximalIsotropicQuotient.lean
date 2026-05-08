import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWMaximalIsotropicFrame
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Quotient preimages for Hall-Wightman maximal isotropic frames

This file keeps the next quotient/rank-nullity support for
`complexMinkowski_maximalIsotropicFrameIn_extending` outside the already large
maximal-frame file.  The declarations here start the concrete preimage packet
for the quotient `Rperp / R`: define the preimage in `Rperp`, retype it in `N`
and in original source coordinates, and prove the original-coordinate preimage
remains inside `N`.
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

end BHW
