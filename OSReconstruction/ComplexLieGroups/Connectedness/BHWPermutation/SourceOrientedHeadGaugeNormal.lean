import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGaugeSupport
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurTailNormal

/-!
# Head-gauge normal-parameter data

The remaining Witt/head-normalization theorem must not merely assert that a
Schur residual tail lies on the shifted-tail variety.  It must identify the
source-variety point with a normal-parameter invariant whose head coordinate is
the local head-gauge factor.  This file records that exact data surface and
checks the mechanical consumers: residual-tail membership and the full Schur
residual packet.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Normal-parameter representative data matched to a local head gauge.

The hard geometric producer for this structure is the finite-dimensional
proper-complex Witt extension carrying the actual selected head frame to the
head-gauge frame, followed by the Schur decomposition of the remaining tail
vectors. -/
structure SourceOrientedHeadGaugeNormalParameterData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD) where
  p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn
  invariant_eq :
    G =
      sourceOrientedMinkowskiInvariant d n
        (sourceOrientedNormalParameterVector d n r hrD hrn p)
  head_eq :
    Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) =
      p.head

namespace SourceOrientedHeadGaugeNormalParameterData

/-- The matched head-gauge normal-parameter head is invertible. -/
theorem head_det_unit
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    {hGvar : G ∈ sourceOrientedGramVariety d n}
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (D :
      SourceOrientedHeadGaugeNormalParameterData
        d n r hrD hrn hGvar Head) :
    IsUnit D.p.head.det := by
  simpa [D.head_eq] using
    Head.factor_det_unit
      (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) hHead

/-- A matched head-gauge normal-parameter representative gives the required
shifted residual-tail membership. -/
theorem residualTail_mem_variety
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    {hGvar : G ∈ sourceOrientedGramVariety d n}
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (D :
      SourceOrientedHeadGaugeNormalParameterData
        d n r hrD hrn hGvar Head) :
    sourceOrientedSchurResidualTailData d n r hrD hrn G
        (Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)) ∈
      sourceShiftedTailOrientedVariety d r hrD (n - r) := by
  exact
    sourceOrientedSchurResidualTailData_mem_variety_of_eq_normalParameter
      d n r hrD hrn D.p D.invariant_eq D.head_eq
      (head_det_unit d n r hrD hrn Head hHead D)

/-- A matched head-gauge normal-parameter representative mechanically produces
the full Schur residual packet. -/
def schurResidualData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (D :
      SourceOrientedHeadGaugeNormalParameterData
        d n r hrD hrn hGvar Head) :
    SourceOrientedSchurResidualData d n r hrD hrn G :=
  sourceOriented_schurResidualData_of_tail_mem
    d n r hrD hrn hGvar Head hHead
    (residualTail_mem_variety d n r hrD hrn Head hHead D)

end SourceOrientedHeadGaugeNormalParameterData

end BHW
