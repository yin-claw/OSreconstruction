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

/-- Selecting full-frame oriented coordinates from a real source invariant
agrees with complexifying the real selected full-frame matrix. -/
theorem sourceFullFrameOrientedCoordOfSource_sourceRealOrientedMinkowskiInvariant
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceFullFrameOrientedCoordOfSource d n ι
        (sourceRealOrientedMinkowskiInvariant d n x) =
      sourceFullFrameOrientedGramCoord d
        ((sourceRealFullFrameMatrix d n ι x).map Complex.ofReal) := by
  rw [sourceRealOrientedMinkowskiInvariant]
  rw [sourceFullFrameOrientedCoordOfSource_sourceOrientedMinkowskiInvariant]
  congr 1

/-- Real mixed Gram rows against the selected full frame. -/
def sourceRealSelectedMixedRows
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceComplementIndex ι → Fin (d + 1) → ℝ :=
  fun k a => sourceRealMinkowskiGram d n x k.1 (ι a)

/-- The real mixed-row coordinate projection is continuous. -/
theorem continuous_sourceRealSelectedMixedRows
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Continuous (sourceRealSelectedMixedRows d n ι) := by
  unfold sourceRealSelectedMixedRows sourceRealMinkowskiGram
  apply continuous_pi
  intro k
  apply continuous_pi
  intro a
  fun_prop

/-- Selecting mixed-row coordinates from a real source invariant agrees with
complexifying the real selected mixed rows. -/
theorem sourceSelectedMixedRows_sourceRealOrientedMinkowskiInvariant
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceSelectedMixedRows d n ι
        (sourceRealOrientedMinkowskiInvariant d n x) =
      fun k a => (sourceRealSelectedMixedRows d n ι x k a : ℂ) := by
  ext k a
  rw [sourceSelectedMixedRows_apply]
  rw [sourceRealOrientedMinkowskiInvariant_gram]
  rfl

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
