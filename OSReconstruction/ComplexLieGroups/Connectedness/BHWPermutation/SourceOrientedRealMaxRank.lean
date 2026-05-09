import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedReal
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameChart

/-!
# Real source full-frame determinant and oriented max rank

This file contains the finite-coordinate bridge used by the oriented real-patch
route: a real source tuple with one nonzero selected full-frame determinant maps
to the max-rank stratum of the oriented source invariant variety.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- A real source tuple with a nonzero selected full-frame determinant has
maximal oriented source rank after applying the real oriented invariant. -/
theorem sourceOrientedMaxRankAt_sourceReal_fullFrameDet_ne_zero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hdet : sourceRealFullFrameDet d n ι x ≠ 0) :
    SourceOrientedMaxRankAt d n
      (sourceRealOrientedMinkowskiInvariant d n x) := by
  apply sourceOrientedMaxRankAt_of_selectedDet_ne_zero d n ι
  · exact sourceRealOrientedMinkowskiInvariant_mem_variety d n x
  · rw [sourceRealOrientedMinkowskiInvariant_det]
    exact_mod_cast hdet

end BHW
