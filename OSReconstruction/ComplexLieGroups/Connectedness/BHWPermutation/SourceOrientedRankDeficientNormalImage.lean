import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientCanonical

/-!
# Normal-parameter images in the oriented source variety

The rank-deficient local-image producer works with parameterized maps into the
oriented source variety subtype.  This file packages the checked normal
Schur/residual parameter map in that subtype-valued form and transports it back
from the canonical Lemma-3 source point to the original exceptional point using
the variety-relative normal-form transport.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The normal Schur/residual parameter map, valued in the oriented source
variety subtype. -/
noncomputable def sourceOrientedNormalParameterVarietyPoint
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    SourceOrientedVariety d n :=
  ⟨sourceOrientedMinkowskiInvariant d n
      (sourceOrientedNormalParameterVector d n r hrD hrn p),
    ⟨sourceOrientedNormalParameterVector d n r hrD hrn p, rfl⟩⟩

@[simp]
theorem sourceOrientedNormalParameterVarietyPoint_val
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    (sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p).1 =
      sourceOrientedMinkowskiInvariant d n
        (sourceOrientedNormalParameterVector d n r hrD hrn p) :=
  rfl

/-- The normal-parameter source-variety map is continuous. -/
theorem continuous_sourceOrientedNormalParameterVarietyPoint
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    Continuous
      (sourceOrientedNormalParameterVarietyPoint d n r hrD hrn) := by
  apply Continuous.subtype_mk
  exact
    (continuous_sourceOrientedMinkowskiInvariant (d := d) (n := n)).comp
      (continuous_sourceOrientedNormalParameterVector d n r hrD hrn)

/-- At the center parameter, the subtype-valued normal image is the canonical
Lemma-3 source point. -/
@[simp]
theorem sourceOrientedNormalParameterVarietyPoint_center
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedNormalParameterVarietyPoint d n r hrD hrn
        (sourceOrientedNormalCenterParameter d n r hrD hrn) =
      hwLemma3CanonicalSourceOrientedVariety d n r := by
  apply Subtype.ext
  simp [sourceOrientedNormalParameterVarietyPoint,
    hwLemma3CanonicalSourceOrientedVariety,
    sourceOrientedNormalParameterVector_center]

/-- Principal Schur head block associated to a normal parameter. -/
noncomputable def sourceOrientedNormalParameterSchurHead
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    Matrix (Fin r) (Fin r) ℂ :=
  p.head * sourceHeadMetric d r hrD * p.headᵀ

/-- Principal Schur mixed block associated to a normal parameter, in the
head/tail orientation used by `sourcePrincipalSchurGraph`. -/
noncomputable def sourceOrientedNormalParameterSchurMixed
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    Matrix (Fin r) (Fin (n - r)) ℂ :=
  (p.mixed * sourceOrientedNormalParameterSchurHead d n r hrD hrn p)ᵀ

/-- Principal Schur residual block associated to a normal parameter. -/
noncomputable def sourceOrientedNormalParameterSchurTail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :
    Matrix (Fin (n - r)) (Fin (n - r)) ℂ :=
  sourceShiftedTailGram d r hrD (n - r) p.tail

/-- On the invertible-head part of normal-parameter space, the ordinary Gram
coordinate of the normal image is the principal Schur graph with residual
`sourceShiftedTailGram`. -/
theorem sourceOrientedNormalParameterVarietyPoint_gram_sourcePrincipalSchurGraph
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hH : IsUnit p.head.det) :
    (sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p).1.gram =
      sourcePrincipalSchurGraph n (sourceHeadTailEquiv n r hrn)
        (sourceOrientedNormalParameterSchurHead d n r hrD hrn p)
        (sourceOrientedNormalParameterSchurMixed d n r hrD hrn p)
        (sourceOrientedNormalParameterSchurTail d n r hrD hrn p) := by
  let A : Matrix (Fin r) (Fin r) ℂ :=
    p.head * sourceHeadMetric d r hrD * p.headᵀ
  have hA : IsUnit A.det := by
    change IsUnit (p.head * sourceHeadMetric d r hrD * p.headᵀ).det
    have hη : IsUnit (sourceHeadMetric d r hrD).det :=
      sourceHeadMetric_det_isUnit d r hrD
    have hHt : IsUnit p.headᵀ.det := Matrix.isUnit_det_transpose p.head hH
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hH.mul hη).mul hHt
  have hcancel :
      (p.mixed * (p.head * sourceHeadMetric d r hrD * p.headᵀ)) *
          (p.head * sourceHeadMetric d r hrD * p.headᵀ)⁻¹ = p.mixed := by
    calc
      (p.mixed * (p.head * sourceHeadMetric d r hrD * p.headᵀ)) *
          (p.head * sourceHeadMetric d r hrD * p.headᵀ)⁻¹
          = p.mixed * ((p.head * sourceHeadMetric d r hrD * p.headᵀ) *
              (p.head * sourceHeadMetric d r hrD * p.headᵀ)⁻¹) := by
                rw [Matrix.mul_assoc]
      _ = p.mixed * (1 : Matrix (Fin r) (Fin r) ℂ) := by
            rw [Matrix.mul_nonsing_inv _ hA]
      _ = p.mixed := by rw [Matrix.mul_one]
  ext i j
  rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
  · rcases finSourceHead_tail_cases hrn j with ⟨b, rfl⟩ | ⟨v, rfl⟩
    · simp only [sourceOrientedNormalParameterVarietyPoint_val,
        SourceOrientedGramData.gram]
      simp [sourcePrincipalSchurGraph, sourceHeadTailEquiv_apply_head,
        sourceOrientedNormalParameterSchurHead,
        sourceOrientedNormalParameterSchurMixed,
        sourceOrientedNormalParameterSchurTail, Matrix.fromBlocks]
      change sourceVectorMinkowskiInner d
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceHead hrn a))
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceHead hrn b)) = _
      rw [sourceOrientedNormalParameterVector_head,
        sourceOrientedNormalParameterVector_head,
        sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector]
    · simp only [sourceOrientedNormalParameterVarietyPoint_val,
        SourceOrientedGramData.gram]
      simp [sourcePrincipalSchurGraph, sourceHeadTailEquiv_apply_head,
        sourceHeadTailEquiv_apply_tail, sourceOrientedNormalParameterSchurHead,
        sourceOrientedNormalParameterSchurMixed,
        sourceOrientedNormalParameterSchurTail, Matrix.fromBlocks]
      change sourceVectorMinkowskiInner d
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceHead hrn a))
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceTail hrn v)) = _
      rw [sourceOrientedNormalParameterVector_head,
        sourceVectorMinkowskiInner_head_tailParameterVector]
      rw [sourceHeadMetric_transpose]
      simp [Matrix.mul_assoc]
  · rcases finSourceHead_tail_cases hrn j with ⟨b, rfl⟩ | ⟨v, rfl⟩
    · simp only [sourceOrientedNormalParameterVarietyPoint_val,
        SourceOrientedGramData.gram]
      simp [sourcePrincipalSchurGraph, sourceHeadTailEquiv_apply_head,
        sourceHeadTailEquiv_apply_tail, sourceOrientedNormalParameterSchurHead,
        sourceOrientedNormalParameterSchurMixed,
        sourceOrientedNormalParameterSchurTail, Matrix.fromBlocks]
      change sourceVectorMinkowskiInner d
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceTail hrn u))
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceHead hrn b)) = _
      rw [sourceOrientedNormalParameterVector_head,
        sourceVectorMinkowskiInner_tailParameterVector_head]
    · simp only [sourceOrientedNormalParameterVarietyPoint_val,
        SourceOrientedGramData.gram]
      simp [sourcePrincipalSchurGraph, sourceHeadTailEquiv_apply_tail,
        sourceOrientedNormalParameterSchurHead,
        sourceOrientedNormalParameterSchurMixed,
        sourceOrientedNormalParameterSchurTail, Matrix.fromBlocks]
      change sourceVectorMinkowskiInner d
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceTail hrn u))
          (sourceOrientedNormalParameterVector d n r hrD hrn p (finSourceTail hrn v)) = _
      rw [sourceVectorMinkowskiInner_tailParameterVector_tail]
      rw [hcancel]
      rw [sourceHeadMetric_transpose]
      simp [sourceShiftedTailGram, Matrix.mul_assoc]
      abel

/-- Full oriented-data form of the principal Schur graph equality.  The
determinant coordinate is retained from the already-realized normal parameter,
while the ordinary Gram coordinate is exposed as a Schur graph. -/
theorem sourceOrientedNormalParameterVarietyPoint_eq_sourcePrincipalSchurGraph
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hH : IsUnit p.head.det) :
    (sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p).1 =
      ((sourcePrincipalSchurGraph n (sourceHeadTailEquiv n r hrn)
        (sourceOrientedNormalParameterSchurHead d n r hrD hrn p)
        (sourceOrientedNormalParameterSchurMixed d n r hrD hrn p)
        (sourceOrientedNormalParameterSchurTail d n r hrD hrn p),
        (sourceOrientedNormalParameterVarietyPoint d n r hrD hrn p).1.det) :
          SourceOrientedGramData d n) := by
  apply Prod.ext
  · exact
      sourceOrientedNormalParameterVarietyPoint_gram_sourcePrincipalSchurGraph
        d n r hrD hrn p hH
  · rfl

namespace SourceOrientedRankDeficientAlgebraicNormalFormData

/-- The normal-parameter image transported from canonical normal form back to
the original exceptional source-variety point. -/
noncomputable def originalNormalVarietyPoint
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    (p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn) :
    SourceOrientedVariety d n :=
  N.varietyTransport.invFun
    (sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p)

@[simp]
theorem originalNormalVarietyPoint_val
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    (p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn) :
    (N.originalNormalVarietyPoint p).1 =
      (N.varietyTransport.invFun
        (sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p)).1 :=
  rfl

/-- The transported normal-parameter source-variety map is continuous. -/
theorem continuous_originalNormalVarietyPoint
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0) :
    Continuous N.originalNormalVarietyPoint :=
  N.varietyTransport.continuous_invFun.comp
    (continuous_sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn)

/-- The transported normal image is centered at the original exceptional point. -/
theorem originalNormalVarietyPoint_center
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0) :
    (N.originalNormalVarietyPoint
      (sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn)).1 = G0 := by
  rw [originalNormalVarietyPoint, sourceOrientedNormalParameterVarietyPoint_center]
  exact N.canonical_to_original

/-- Max-rank of the transported image is exactly max-rank of the canonical
normal-parameter image. -/
theorem originalNormalVarietyPoint_maxRank_iff
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    (p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn) :
    SourceOrientedMaxRankAt d n (N.originalNormalVarietyPoint p).1 ↔
      SourceOrientedMaxRankAt d n
        (sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p).1 :=
  N.varietyTransport.invFun_maxRank_iff
    (sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p)

end SourceOrientedRankDeficientAlgebraicNormalFormData

end BHW
