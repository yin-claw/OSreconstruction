import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlowBlockers.Core

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

example {v0 : ℂ} (hv0 : v0 ≠ 0) :
    d1InvariantQuad (d1N2SectionOrig (-1) (-9) (-3) 0 v0) =
      ((-1 : ℂ), (-9 : ℂ), (-3 : ℂ), (0 : ℂ)) := by
  have hquad : (0 : ℂ) ^ 2 = 4 * (((-3 : ℂ) ^ 2) - (-1 : ℂ) * (-9 : ℂ)) := by
    norm_num
  have hq0 : (-1 : ℂ) ≠ 0 := by norm_num
  simpa using
    (d1InvariantQuad_sectionOrig
      (q0 := (-1 : ℂ)) (q1 := (-9 : ℂ)) (p := (-3 : ℂ)) (s := (0 : ℂ))
      (v0 := v0) hquad hq0 hv0)

example {w0 : ℂ} (hw0 : w0 ≠ 0) :
    d1InvariantQuad (d1N2SectionSwap (-1) (-9) (-3) 0 w0) =
      ((-9 : ℂ), (-1 : ℂ), (-3 : ℂ), (0 : ℂ)) := by
  have hquad : (0 : ℂ) ^ 2 = 4 * (((-3 : ℂ) ^ 2) - (-1 : ℂ) * (-9 : ℂ)) := by
    norm_num
  have hq1 : (-9 : ℂ) ≠ 0 := by norm_num
  simpa using
    (d1InvariantQuad_sectionSwap
      (q0 := (-1 : ℂ)) (q1 := (-9 : ℂ)) (p := (-3 : ℂ)) (s := (0 : ℂ))
      (w0 := w0) hquad hq1 hw0)

example (z : D1N2Config) (hz : z ∈ ForwardTube 1 2) :
    d1N2SectionOrig (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) (d1V0 z) = z :=
  d1N2SectionOrig_eq_of_forward z hz

example (y : D1N2Config) (hy : y ∈ ForwardTube 1 2) :
    d1N2SectionSwap (d1Q1 y) (d1Q0 y) (d1P01 y) (-d1S01 y) (d1V0 y) = y := by
  have hquadY :
      d1InvariantQuad y = (d1Q0 y, d1Q1 y, d1P01 y, -(-d1S01 y)) := by
    simp [d1InvariantQuad]
  simpa using
    (d1N2SectionSwap_eq_of_forward_invariants
      (q0 := d1Q1 y) (q1 := d1Q0 y) (p := d1P01 y) (s := -d1S01 y)
      y hy hquadY)

end BHW

