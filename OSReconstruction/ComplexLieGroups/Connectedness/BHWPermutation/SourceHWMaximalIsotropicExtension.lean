import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWMaximalIsotropicQuotient

/-!
# Compatible maximal isotropic extension

This file keeps the final wrapper for extending a fixed totally isotropic
subspace to a globally maximal one separate from the quotient/rank-nullity
support file.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

set_option maxHeartbeats 800000

local instance sourceHWMaximalIsotropicExtension_hasQuotient
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (RN : Submodule ℂ N) :
    HasQuotient (complexMinkowskiRelativeOrthogonalIn (d := d) N RN)
      (Submodule ℂ (complexMinkowskiRelativeOrthogonalIn (d := d) N RN)) :=
  Submodule.hasQuotient (R := ℂ)
    (M := complexMinkowskiRelativeOrthogonalIn (d := d) N RN)

/-- The named quotient-preimage candidate contains the original isotropic
subspace. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal_contains
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (M : ComplexMinkowskiRelativeOrthogonalQuotientMaximalPackage
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R)) :
    R ≤ complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal
      (d := d) (N := N) (R := R) M := by
  let RN := complexMinkowskiSubmoduleIn (d := d) N R
  rw [complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal]
  exact
    complexMinkowskiSubmodule_le_relativeOrthogonalQuotientPreimage
      (d := d) (N := N) (R := R) hR_le hR_iso M.Q

/-- The named quotient-preimage candidate remains inside `N`. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal_le
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (M : ComplexMinkowskiRelativeOrthogonalQuotientMaximalPackage
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R)) :
    complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal
      (d := d) (N := N) (R := R) M ≤ N := by
  let RN := complexMinkowskiSubmoduleIn (d := d) N R
  rw [complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal]
  exact
    complexMinkowskiRelativeOrthogonalQuotientPreimage_le
      (d := d) (N := N) RN M.Q

/-- The named quotient-preimage candidate is totally isotropic. -/
theorem complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal_isotropic
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (M : ComplexMinkowskiRelativeOrthogonalQuotientMaximalPackage
      (d := d) (N := N) (complexMinkowskiSubmoduleIn (d := d) N R)) :
    ComplexMinkowskiTotallyIsotropicSubspace d
      (complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal
        (d := d) (N := N) (R := R) M) := by
  let RN := complexMinkowskiSubmoduleIn (d := d) N R
  rw [complexMinkowskiRelativeOrthogonalQuotientPreimageOfMaximal]
  exact
    complexMinkowskiRelativeOrthogonalQuotientPreimage_isotropic
      (d := d) (N := N) RN M.Q M.Q_iso

end BHW
