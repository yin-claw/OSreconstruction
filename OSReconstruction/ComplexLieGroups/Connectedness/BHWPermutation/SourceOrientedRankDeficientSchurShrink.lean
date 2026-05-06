import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedNormalParameterBall
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientNormalImage

/-!
# Schur-coordinate shrinks for normal parameters

This file packages the topology-only shrink from the normal center to the
Schur head, mixed, and residual-tail coordinates.  The later quantitative
local-image proof supplies concrete coordinate neighborhoods; this file proves
that they can be pulled back to a connected normal-parameter ball.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

@[simp]
theorem sourceOrientedNormalParameterSchurHead_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedNormalParameterSchurHead d n r hrD hrn
        (sourceOrientedNormalCenterParameter d n r hrD hrn) =
      sourceHeadMetric d r hrD := by
  simp [sourceOrientedNormalParameterSchurHead,
    sourceOrientedNormalCenterParameter]

@[simp]
theorem sourceOrientedNormalParameterSchurMixed_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedNormalParameterSchurMixed d n r hrD hrn
        (sourceOrientedNormalCenterParameter d n r hrD hrn) =
      0 := by
  simp [sourceOrientedNormalParameterSchurMixed,
    sourceOrientedNormalCenterParameter]

@[simp]
theorem sourceOrientedNormalParameterSchurTail_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedNormalParameterSchurTail d n r hrD hrn
        (sourceOrientedNormalCenterParameter d n r hrD hrn) =
      0 := by
  ext u v
  simp [sourceOrientedNormalParameterSchurTail, sourceShiftedTailGram,
    sourceVectorMinkowskiInner, sourceTailEmbed,
    sourceOrientedNormalCenterParameter]

/-- Any neighborhoods of the center Schur head, mixed, and residual-tail
coordinates contain a positive-radius normal-parameter ball after pullback. -/
theorem exists_sourceOrientedNormalParameterBall_subset_schur_nhds
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {Uh : Set (Matrix (Fin r) (Fin r) ℂ)}
    (hUh : Uh ∈ 𝓝 (sourceHeadMetric d r hrD))
    {Um : Set (Matrix (Fin r) (Fin (n - r)) ℂ)}
    (hUm : Um ∈ 𝓝 (0 : Matrix (Fin r) (Fin (n - r)) ℂ))
    {Ut : Set (Matrix (Fin (n - r)) (Fin (n - r)) ℂ)}
    (hUt : Ut ∈ 𝓝 (0 : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)) :
    ∃ ε : ℝ,
      0 < ε ∧
        sourceOrientedNormalParameterBall (d := d) (n := n) (r := r)
          (hrD := hrD) (hrn := hrn) ε ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn |
            sourceOrientedNormalParameterSchurHead d n r hrD hrn p ∈ Uh ∧
              sourceOrientedNormalParameterSchurMixed d n r hrD hrn p ∈ Um ∧
              sourceOrientedNormalParameterSchurTail d n r hrD hrn p ∈ Ut} := by
  let p0 := sourceOrientedNormalCenterParameter d n r hrD hrn
  have hhead_nhds :
      (sourceOrientedNormalParameterSchurHead d n r hrD hrn) ⁻¹' Uh ∈
        𝓝 p0 := by
    have hUh' :
        Uh ∈
          𝓝 (sourceOrientedNormalParameterSchurHead d n r hrD hrn p0) := by
      simpa [p0] using hUh
    exact
      (continuous_sourceOrientedNormalParameterSchurHead d n r hrD hrn).continuousAt
        hUh'
  have hmixed_nhds :
      (sourceOrientedNormalParameterSchurMixed d n r hrD hrn) ⁻¹' Um ∈
        𝓝 p0 := by
    have hUm' :
        Um ∈
          𝓝 (sourceOrientedNormalParameterSchurMixed d n r hrD hrn p0) := by
      simpa [p0] using hUm
    exact
      (continuous_sourceOrientedNormalParameterSchurMixed d n r hrD hrn).continuousAt
        hUm'
  have htail_nhds :
      (sourceOrientedNormalParameterSchurTail d n r hrD hrn) ⁻¹' Ut ∈
        𝓝 p0 := by
    have hUt' :
        Ut ∈
          𝓝 (sourceOrientedNormalParameterSchurTail d n r hrD hrn p0) := by
      simpa [p0] using hUt
    exact
      (continuous_sourceOrientedNormalParameterSchurTail d n r hrD hrn).continuousAt
        hUt'
  have hU :
      {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn |
        sourceOrientedNormalParameterSchurHead d n r hrD hrn p ∈ Uh ∧
          sourceOrientedNormalParameterSchurMixed d n r hrD hrn p ∈ Um ∧
          sourceOrientedNormalParameterSchurTail d n r hrD hrn p ∈ Ut} ∈
        𝓝 p0 := by
    refine
      Filter.mem_of_superset
        (Filter.inter_mem hhead_nhds
          (Filter.inter_mem hmixed_nhds htail_nhds)) ?_
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2⟩
  exact
    exists_sourceOrientedNormalParameterBall_subset_of_mem_nhds_center
      d n r hrD hrn hU

end BHW
