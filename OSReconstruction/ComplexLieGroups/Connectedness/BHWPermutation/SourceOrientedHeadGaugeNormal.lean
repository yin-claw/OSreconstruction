import OSReconstruction.ComplexLieGroups.SOFrameTransitivity
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

/-- The inverse Wick scale also squares to the complex Minkowski signature. -/
theorem complexMinkowskiDotInvScale_sq
    (d : ℕ) (μ : Fin (d + 1)) :
    complexMinkowskiDotInvScale d μ * complexMinkowskiDotInvScale d μ =
      (MinkowskiSpace.metricSignature d μ : ℂ) := by
  by_cases hμ : μ = 0 <;>
    simp [complexMinkowskiDotInvScale, MinkowskiSpace.metricSignature, hμ]

theorem complexMinkowskiDotInvScale_ne_zero
    (d : ℕ) (μ : Fin (d + 1)) :
    complexMinkowskiDotInvScale d μ ≠ 0 := by
  by_cases hμ : μ = 0 <;>
    simp [complexMinkowskiDotInvScale, hμ]

theorem complexMinkowskiDotScale_mul_invScale
    (d : ℕ) (μ : Fin (d + 1)) :
    complexMinkowskiDotScale d μ * complexMinkowskiDotInvScale d μ = 1 := by
  rw [mul_comm]
  exact complexMinkowskiDotInvScale_mul_scale d μ

/-- The inverse Wick-scaled coordinates of a source vector. -/
def complexMinkowskiInvDotVector
    (d : ℕ) (v : Fin (d + 1) → ℂ) :
    Fin (d + 1) → ℂ :=
  fun μ => complexMinkowskiDotInvScale d μ * v μ

/-- The complex Minkowski pairing is also the ordinary dot pairing after
inverse Wick scaling. -/
theorem sourceVectorMinkowskiInner_eq_dot_after_invScale
    (d : ℕ) (u v : Fin (d + 1) → ℂ) :
    sourceVectorMinkowskiInner d u v =
      ∑ μ : Fin (d + 1),
        complexMinkowskiInvDotVector d u μ *
          complexMinkowskiInvDotVector d v μ := by
  unfold sourceVectorMinkowskiInner complexMinkowskiInvDotVector
  apply Finset.sum_congr rfl
  intro μ _
  rw [← complexMinkowskiDotInvScale_sq d μ]
  ring

/-- In inverse Wick-scaled dot coordinates, `fromSOComplex A` acts by the
ordinary matrix `A`. -/
theorem complexMinkowskiInvDotVector_complexLorentzVectorAction_fromSOComplex
    (d : ℕ) (A : SOComplex (d + 1)) (v : Fin (d + 1) → ℂ) :
    complexMinkowskiInvDotVector d
        (complexLorentzVectorAction (ComplexLorentzGroup.fromSOComplex A) v) =
      A.val *ᵥ complexMinkowskiInvDotVector d v := by
  ext μ
  calc
    complexMinkowskiInvDotVector d
        (complexLorentzVectorAction (ComplexLorentzGroup.fromSOComplex A) v) μ
        = complexMinkowskiDotInvScale d μ *
            ∑ ν : Fin (d + 1),
              (complexMinkowskiDotScale d μ * A.val μ ν *
                complexMinkowskiDotInvScale d ν) * v ν := by
            simp [complexMinkowskiInvDotVector, complexLorentzVectorAction,
              ComplexLorentzGroup.fromSOComplex_val_apply,
              complexMinkowskiDotScale, complexMinkowskiDotInvScale]
    _ = ∑ ν : Fin (d + 1),
          (complexMinkowskiDotInvScale d μ * complexMinkowskiDotScale d μ) *
            (A.val μ ν * (complexMinkowskiDotInvScale d ν * v ν)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ν _
            ring
    _ = ∑ ν : Fin (d + 1),
          A.val μ ν * (complexMinkowskiDotInvScale d ν * v ν) := by
            rw [complexMinkowskiDotInvScale_mul_scale]
            simp
    _ = (A.val *ᵥ complexMinkowskiInvDotVector d v) μ := by
            simp [complexMinkowskiInvDotVector, Matrix.mulVec, dotProduct]

/-- The signed dot-scale attached to the `a`th Minkowski prefix coordinate. -/
def minkowskiPrefixSigma (m r : ℕ) (a : Fin r) : ℂ :=
  complexMinkowskiDotInvScale (m + r) (SOComplex.prefixCol m r a)

theorem minkowskiPrefixSigma_ne_zero
    (m r : ℕ) (a : Fin r) :
    minkowskiPrefixSigma m r a ≠ 0 :=
  complexMinkowskiDotInvScale_ne_zero (m + r) (SOComplex.prefixCol m r a)

theorem minkowskiPrefixSigma_sq
    (m r : ℕ) (a : Fin r) :
    minkowskiPrefixSigma m r a ^ 2 =
      (MinkowskiSpace.metricSignature (m + r)
        (SOComplex.prefixCol m r a) : ℂ) := by
  simp [minkowskiPrefixSigma, sq, complexMinkowskiDotInvScale_sq]

/-- Determinant-one complex Lorentz transitivity for a source frame whose Gram
matrix is the standard Minkowski prefix metric. -/
theorem complexMinkowski_detOneWittExtension_to_canonicalPrefixFrame
    (m r : ℕ)
    (x : Fin r → Fin (m + r + 1) → ℂ)
    (hgram :
      ∀ a b : Fin r,
        sourceVectorMinkowskiInner (m + r) (x a) (x b) =
          if a = b then
            (MinkowskiSpace.metricSignature (m + r)
              (SOComplex.prefixCol m r a) : ℂ)
          else 0) :
    ∃ Λ : ComplexLorentzGroup (m + r),
      ∀ a : Fin r,
        complexLorentzVectorAction Λ (x a) =
          fun μ => if μ = SOComplex.prefixCol m r a then 1 else 0 := by
  let σ : Fin r → ℂ := minkowskiPrefixSigma m r
  let xdot : Fin r → Fin (m + r + 1) → ℂ :=
    fun a => complexMinkowskiInvDotVector (m + r) (x a)
  have hσ : ∀ a : Fin r, σ a ≠ 0 := by
    intro a
    exact minkowskiPrefixSigma_ne_zero m r a
  have hdotGram :
      ∀ a b : Fin r,
        (∑ k : Fin (m + r + 1), xdot a k * xdot b k) =
          if a = b then (σ a) ^ 2 else 0 := by
    intro a b
    rw [← sourceVectorMinkowskiInner_eq_dot_after_invScale (m + r) (x a) (x b)]
    rw [hgram a b]
    by_cases hab : a = b
    · subst hab
      simp [σ, minkowskiPrefixSigma_sq]
    · simp [hab]
  obtain ⟨A, hA⟩ :=
    SOComplex.exists_so_with_signedPrefixCols m r σ hσ xdot hdotGram
  refine ⟨ComplexLorentzGroup.fromSOComplex A⁻¹, ?_⟩
  intro a
  have hAinv_xdot :
      (A⁻¹).val *ᵥ xdot a =
        fun μ => if μ = SOComplex.prefixCol m r a then σ a else 0 := by
    ext μ
    have horth := congrFun (congrFun A.orthogonal μ) (SOComplex.prefixCol m r a)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at horth
    calc
      ((A⁻¹).val *ᵥ xdot a) μ
          = ∑ k : Fin (m + r + 1), A.val k μ * xdot a k := by
              simp [Matrix.mulVec, dotProduct, SOComplex.inv_val_apply]
      _ = ∑ k : Fin (m + r + 1),
            A.val k μ * (σ a * A.val k (SOComplex.prefixCol m r a)) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [hA a k]
      _ = σ a *
            ∑ k : Fin (m + r + 1),
              A.val k μ * A.val k (SOComplex.prefixCol m r a) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = σ a * (if μ = SOComplex.prefixCol m r a then 1 else 0) := by
              rw [horth]
      _ = (if μ = SOComplex.prefixCol m r a then σ a else 0) := by
              by_cases hμ : μ = SOComplex.prefixCol m r a <;> simp [hμ]
  have hdot_action :
      complexMinkowskiInvDotVector (m + r)
          (complexLorentzVectorAction
            (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a)) =
        fun μ => if μ = SOComplex.prefixCol m r a then σ a else 0 := by
    calc
      complexMinkowskiInvDotVector (m + r)
          (complexLorentzVectorAction
            (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a))
          = (A⁻¹).val *ᵥ xdot a := by
              rw [complexMinkowskiInvDotVector_complexLorentzVectorAction_fromSOComplex]
      _ = fun μ => if μ = SOComplex.prefixCol m r a then σ a else 0 := hAinv_xdot
  ext μ
  by_cases hμ : μ = SOComplex.prefixCol m r a
  · subst hμ
    have hμdot :
        complexMinkowskiDotInvScale (m + r) (SOComplex.prefixCol m r a) *
          complexLorentzVectorAction
            (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a)
            (SOComplex.prefixCol m r a) =
          σ a := by
      simpa [complexMinkowskiInvDotVector] using
        congrFun hdot_action (SOComplex.prefixCol m r a)
    calc
      complexLorentzVectorAction (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a)
          (SOComplex.prefixCol m r a)
          = 1 *
              complexLorentzVectorAction
                (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a)
                (SOComplex.prefixCol m r a) := by rw [one_mul]
      _ = (complexMinkowskiDotScale (m + r) (SOComplex.prefixCol m r a) *
            complexMinkowskiDotInvScale (m + r) (SOComplex.prefixCol m r a)) *
              complexLorentzVectorAction
                (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a)
                (SOComplex.prefixCol m r a) := by
            rw [complexMinkowskiDotScale_mul_invScale]
      _ = complexMinkowskiDotScale (m + r) (SOComplex.prefixCol m r a) *
            (complexMinkowskiDotInvScale (m + r) (SOComplex.prefixCol m r a) *
              complexLorentzVectorAction
                (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a)
                (SOComplex.prefixCol m r a)) := by ring
      _ = complexMinkowskiDotScale (m + r) (SOComplex.prefixCol m r a) *
            σ a := by
            rw [hμdot]
      _ = 1 := by
            simp [σ, minkowskiPrefixSigma, complexMinkowskiDotScale_mul_invScale]
      _ = (fun μ => if μ = SOComplex.prefixCol m r a then 1 else 0)
            (SOComplex.prefixCol m r a) := by
            simp
  · calc
      complexLorentzVectorAction (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a) μ
          = 1 *
              complexLorentzVectorAction
                (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a) μ := by
            rw [one_mul]
      _ = (complexMinkowskiDotScale (m + r) μ *
            complexMinkowskiDotInvScale (m + r) μ) *
              complexLorentzVectorAction
                (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a) μ := by
            rw [complexMinkowskiDotScale_mul_invScale]
      _ = complexMinkowskiDotScale (m + r) μ *
            (complexMinkowskiDotInvScale (m + r) μ *
              complexLorentzVectorAction
                (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a) μ) := by ring
      _ = 0 := by
            rw [show
              complexMinkowskiDotInvScale (m + r) μ *
                complexLorentzVectorAction
                  (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a) μ =
                0 by
                  simpa [complexMinkowskiInvDotVector, hμ] using
                    congrFun hdot_action μ]
            ring
      _ = (fun μ => if μ = SOComplex.prefixCol m r a then 1 else 0) μ := by
            simp [hμ]

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

/-- The normal parameter whose head coordinate is the local head-gauge factor
and whose mixed/tail coordinates are zero.  This is the target head frame used
before the transformed tail coordinates are chosen. -/
def sourceOrientedHeadGaugeHeadParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD) :
    SourceOrientedRankDeficientNormalParameter d n r hrD hrn where
  head := Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)
  mixed := 0
  tail := 0

@[simp]
theorem sourceOrientedHeadGaugeHeadParameter_head
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD) :
    (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head).head =
      Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) := by
  rfl

/-- The local head gauge identifies the actual selected head Gram matrix with
the normal-form head Gram matrix of the gauge head frame. -/
theorem sourceOriented_headGauge_actualHeadGram_eq_normalHeadGram
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    (a b : Fin r) :
    sourceVectorMinkowskiInner d
        (z (finSourceHead hrn a))
        (z (finSourceHead hrn b)) =
      sourceVectorMinkowskiInner d
        (sourceOrientedNormalHeadVector d n r hrD hrn
          (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a)
        (sourceOrientedNormalHeadVector d n r hrD hrn
          (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) b) := by
  let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar
  let p0 := sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head
  have hfactor :
      p0.head * sourceHeadMetric d r hrD * p0.headᵀ =
        sourceOrientedSchurHeadBlock n r hrn G := by
    simpa [Acoord, p0, sourceOrientedHeadGaugeHeadParameter] using
      Head.factor_gram Acoord hHead
  calc
    sourceVectorMinkowskiInner d
        (z (finSourceHead hrn a))
        (z (finSourceHead hrn b)) =
        sourceOrientedSchurHeadBlock n r hrn G a b := by
          subst G
          rfl
    _ = (p0.head * sourceHeadMetric d r hrD * p0.headᵀ) a b := by
          rw [hfactor]
    _ = sourceVectorMinkowskiInner d
        (sourceOrientedNormalHeadVector d n r hrD hrn p0 a)
        (sourceOrientedNormalHeadVector d n r hrD hrn p0 b) := by
          exact
            (sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector
              d n r hrD hrn p0 a b).symm

/-- The gauge normal head frame is linearly independent. -/
theorem sourceOriented_headGauge_normalHead_linearIndependent
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U) :
    LinearIndependent ℂ
      (fun a : Fin r =>
        sourceOrientedNormalHeadVector d n r hrD hrn
          (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a) := by
  let p0 := sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head
  have hp0_det : IsUnit p0.head.det := by
    simpa [p0, sourceOrientedHeadGaugeHeadParameter] using
      Head.factor_det_unit
        (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) hHead
  have hη : IsUnit (sourceHeadMetric d r hrD).det :=
    sourceHeadMetric_det_isUnit d r hrD
  have hp0t : IsUnit p0.headᵀ.det :=
    Matrix.isUnit_det_transpose p0.head hp0_det
  have hheadGram :
      IsUnit (p0.head * sourceHeadMetric d r hrD * p0.headᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hp0_det.mul hη).mul hp0t
  have hA :
      IsUnit
        (sourceOrientedSchurHeadBlock n r hrn
          (sourceOrientedMinkowskiInvariant d n
            (sourceOrientedNormalParameterVector d n r hrD hrn p0))).det := by
    rw [sourceOrientedSchurHeadBlock_normalParameter]
    exact hheadGram
  have hLI :=
    sourceHeadRows_linearIndependent_of_schurHeadBlock_isUnit
      d n r hrn
      (sourceOrientedNormalParameterVector d n r hrD hrn p0) hA
  simpa [sourceOrientedNormalParameterVector_head] using hLI

/-- Checked same-Gram frame data supplied by a local head gauge.

The hard Witt theorem should consume precisely this finite-dimensional packet:
the actual selected head frame and the gauge normal head frame are linearly
independent and have the same nondegenerate Gram matrix. -/
structure SourceOrientedHeadGaugeFrameSameGramData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z) where
  actual_linearIndependent :
    LinearIndependent ℂ (fun a : Fin r => z (finSourceHead hrn a))
  normal_linearIndependent :
    LinearIndependent ℂ
      (fun a : Fin r =>
        sourceOrientedNormalHeadVector d n r hrD hrn
          (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a)
  same_gram :
    ∀ a b : Fin r,
      sourceVectorMinkowskiInner d
          (z (finSourceHead hrn a))
          (z (finSourceHead hrn b)) =
        sourceVectorMinkowskiInner d
          (sourceOrientedNormalHeadVector d n r hrD hrn
            (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a)
          (sourceOrientedNormalHeadVector d n r hrD hrn
            (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) b)
  headGram_det_unit :
    IsUnit (sourceOrientedSchurHeadBlock n r hrn G).det

/-- A local head gauge mechanically produces the same-Gram frame packet needed
by the remaining determinant-one Witt step. -/
def sourceOriented_headGaugeFrameSameGramData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z) :
    SourceOrientedHeadGaugeFrameSameGramData
      d n r hrD hrn Head hGvar hHead hz where
  actual_linearIndependent :=
    sourceHeadRows_linearIndependent_of_headGauge
      d n r hrD hrn hGvar Head hHead hz
  normal_linearIndependent :=
    sourceOriented_headGauge_normalHead_linearIndependent
      d n r hrD hrn hGvar Head hHead
  same_gram :=
    sourceOriented_headGauge_actualHeadGram_eq_normalHeadGram
      d n r hrD hrn hGvar Head hHead hz
  headGram_det_unit :=
    sourceOrientedSchurHeadBlock_det_isUnit_of_headGauge
      d n r hrD hrn hGvar Head hHead

/-- Pairing a vector against a canonical head coordinate vector extracts the
corresponding diagonal-sign-weighted head coordinate. -/
theorem sourceVectorMinkowskiInner_right_hwLemma3CanonicalSource_head
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (v : Fin (d + 1) → ℂ)
    (a : Fin r) :
    sourceVectorMinkowskiInner d v
        (hwLemma3CanonicalSource d n r (finSourceHead hrn a)) =
      (MinkowskiSpace.metricSignature d
          (finSourceHead (Nat.le_of_lt hrD) a) : ℂ) *
        v (finSourceHead (Nat.le_of_lt hrD) a) := by
  rw [sourceVectorMinkowskiInner]
  rw [Finset.sum_eq_single (finSourceHead (Nat.le_of_lt hrD) a)]
  · rw [hwLemma3CanonicalSource_head_apply (hrD := hrD)]
    simp
  · intro μ _hμ hne
    have hzero :
        hwLemma3CanonicalSource d n r (finSourceHead hrn a) μ = 0 := by
      rw [hwLemma3CanonicalSource_head_apply (hrD := hrD)]
      simp [hne]
    simp [hzero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

/-- A vector orthogonal to every gauge normal head vector has zero canonical
head coordinates. -/
theorem sourceOriented_headGauge_headCoord_eq_zero_of_orthogonal_normalHead
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {v : Fin (d + 1) → ℂ}
    (horth :
      ∀ a : Fin r,
        sourceVectorMinkowskiInner d v
          (sourceOrientedNormalHeadVector d n r hrD hrn
            (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a) =
          0)
    (a : Fin r) :
    v (finSourceHead (Nat.le_of_lt hrD) a) = 0 := by
  let p0 := sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head
  let H := p0.head
  let u : Fin r → ℂ := fun b =>
    (MinkowskiSpace.metricSignature d
      (finSourceHead (Nat.le_of_lt hrD) b) : ℂ) *
      v (finSourceHead (Nat.le_of_lt hrD) b)
  have hHdet : IsUnit H.det := by
    simpa [H, p0, sourceOrientedHeadGaugeHeadParameter] using
      Head.factor_det_unit
        (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) hHead
  have hHu : H.mulVec u = 0 := by
    ext b
    have hpair :
        sourceVectorMinkowskiInner d v
          (sourceOrientedNormalHeadVector d n r hrD hrn p0 b) =
        H.mulVec u b := by
      change
        sourceVectorMinkowskiInner d v
          (fun μ =>
            ∑ c : Fin r,
              p0.head b c *
                hwLemma3CanonicalSource d n r (finSourceHead hrn c) μ) =
          H.mulVec u b
      rw [sourceVectorMinkowskiInner_sum_right]
      simp_rw [sourceVectorMinkowskiInner_smul_right]
      simp_rw [
        sourceVectorMinkowskiInner_right_hwLemma3CanonicalSource_head
          d n r hrD hrn v]
      simp [H, u, Matrix.mulVec, dotProduct]
    exact hpair.symm.trans (horth b)
  have hu : u = 0 := by
    have hleft :
        H⁻¹.mulVec (H.mulVec u) = H⁻¹.mulVec (0 : Fin r → ℂ) := by
      rw [hHu]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul H hHdet,
      Matrix.one_mulVec] at hleft
    simpa using hleft
  have ha := congrFun hu a
  have hmetric_ne :
      (MinkowskiSpace.metricSignature d
        (finSourceHead (Nat.le_of_lt hrD) a) : ℂ) ≠ 0 := by
    by_cases h0 : finSourceHead (Nat.le_of_lt hrD) a = 0
    · simp [MinkowskiSpace.metricSignature, h0]
    · simp [MinkowskiSpace.metricSignature, h0]
  exact (mul_eq_zero.mp ha).resolve_left hmetric_ne

/-- A spacetime vector with zero canonical head coordinates is exactly the
tail embedding of its canonical tail coordinates. -/
theorem eq_sourceTailEmbed_of_headCoord_eq_zero
    (d r : ℕ)
    (hrD : r < d + 1)
    (v : Fin (d + 1) → ℂ)
    (hhead : ∀ a : Fin r, v (finSourceHead (Nat.le_of_lt hrD) a) = 0) :
    v =
      sourceTailEmbed d r hrD
        (fun u : Fin (d + 1 - r) =>
          v (finSourceTail (Nat.le_of_lt hrD) u)) := by
  ext μ
  rcases finSourceHead_tail_cases (Nat.le_of_lt hrD) μ with
    ⟨a, rfl⟩ | ⟨u, rfl⟩
  · simp [sourceTailEmbed, hhead a]
  · simp [sourceTailEmbed]

/-- Constructive tail-coordinate data after a Lorentz transformation has
normalized the selected head frame to the gauge normal head frame. -/
def sourceOriented_headGaugeTailCoordinatesAfterWittData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    (Λ : ComplexLorentzGroup d)
    (hΛhead :
      ∀ a : Fin r,
        complexLorentzAction Λ z (finSourceHead hrn a) =
          sourceOrientedNormalHeadVector d n r hrD hrn
            (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a) :
    { q : Fin (n - r) → Fin (d + 1 - r) → ℂ //
      let H :=
        Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)
      let L :=
        sourceSchurMixedCoeff n r hrn G
          (sourceOrientedSchurHeadBlock n r hrn G)
      complexLorentzAction Λ z =
        sourceOrientedNormalParameterVector d n r hrD hrn
          { head := H
            mixed := L
            tail := q } } := by
  let A := sourceOrientedSchurHeadBlock n r hrn G
  let H := Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)
  let L := sourceSchurMixedCoeff n r hrn G A
  let p0 := sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head
  let y : Fin r → Fin (d + 1) → ℂ := fun a =>
    sourceOrientedNormalHeadVector d n r hrD hrn p0 a
  let w := complexLorentzAction Λ z
  let res : Fin (n - r) → Fin (d + 1) → ℂ := fun u μ =>
    w (finSourceTail hrn u) μ - ∑ a : Fin r, L u a * y a μ
  let q : Fin (n - r) → Fin (d + 1 - r) → ℂ := fun u β =>
    res u (finSourceTail (Nat.le_of_lt hrD) β)
  refine ⟨q, ?_⟩
  let p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn :=
    { head := H
      mixed := L
      tail := q }
  change w = sourceOrientedNormalParameterVector d n r hrD hrn p
  have hAunit : IsUnit A.det := by
    simpa [A] using
      sourceOrientedSchurHeadBlock_det_isUnit_of_headGauge
        d n r hrD hrn hGvar Head hHead
  have hLmul :
      L * A = sourceOrientedSchurMixedBlock n r hrn G := by
    simpa [L, A] using
      sourceSchurMixedCoeff_mul_headBlock n r hrn G A hAunit
  have hfactor : H * sourceHeadMetric d r hrD * Hᵀ = A := by
    simpa [H, A] using
      Head.factor_gram
        (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) hHead
  have hygram :
      ∀ a b : Fin r, sourceVectorMinkowskiInner d (y a) (y b) = A a b := by
    intro a b
    calc
      sourceVectorMinkowskiInner d (y a) (y b) =
          (p0.head * sourceHeadMetric d r hrD * p0.headᵀ) a b := by
            simp [y, p0,
              sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector]
      _ = A a b := by
            simpa [p0, sourceOrientedHeadGaugeHeadParameter, H] using
              congrFun (congrFun hfactor a) b
  have hgramW : sourceMinkowskiGram d n w = G.gram := by
    calc
      sourceMinkowskiGram d n w =
          sourceMinkowskiGram d n z := by
            exact sourceMinkowskiGram_complexLorentzAction
              (d := d) (n := n) Λ z
      _ = G.gram := by
            rw [hz]
            rfl
  have htail_head :
      ∀ u a,
        sourceVectorMinkowskiInner d (w (finSourceTail hrn u)) (y a) =
          sourceOrientedSchurMixedBlock n r hrn G u a := by
    intro u a
    calc
      sourceVectorMinkowskiInner d (w (finSourceTail hrn u)) (y a) =
          sourceVectorMinkowskiInner d
            (w (finSourceTail hrn u)) (w (finSourceHead hrn a)) := by
            have hyw : y a = w (finSourceHead hrn a) :=
              (hΛhead a).symm
            rw [hyw]
      _ = sourceMinkowskiGram d n w (finSourceTail hrn u)
            (finSourceHead hrn a) := rfl
      _ = G.gram (finSourceTail hrn u) (finSourceHead hrn a) := by
            rw [hgramW]
      _ = sourceOrientedSchurMixedBlock n r hrn G u a := rfl
  have hres_orth :
      ∀ u a, sourceVectorMinkowskiInner d (res u) (y a) = 0 := by
    intro u a
    calc
      sourceVectorMinkowskiInner d (res u) (y a) =
          sourceOrientedSchurMixedBlock n r hrn G u a -
            (L * A) u a := by
            simp [res, sourceVectorMinkowskiInner_sub_left,
              sourceVectorMinkowskiInner_sum_left,
              sourceVectorMinkowskiInner_smul_left, htail_head, hygram,
              Matrix.mul_apply]
      _ = 0 := by
            rw [hLmul]
            simp
  have hres_tail :
      ∀ u, res u = sourceTailEmbed d r hrD (q u) := by
    intro u
    apply eq_sourceTailEmbed_of_headCoord_eq_zero d r hrD
    intro a
    exact
      sourceOriented_headGauge_headCoord_eq_zero_of_orthogonal_normalHead
        d n r hrD hrn hGvar Head hHead (hres_orth u) a
  ext i μ
  rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
  · calc
      w (finSourceHead hrn a) μ = y a μ := congrFun (hΛhead a) μ
      _ = sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceHead hrn a) μ := by
            simp [p, y, p0, sourceOrientedNormalParameterVector_head,
              sourceOrientedHeadGaugeHeadParameter, H, sourceOrientedNormalHeadVector]
  · have htail :
        w (finSourceTail hrn u) =
          (fun μ =>
            (∑ a : Fin r,
              L u a *
                sourceOrientedNormalHeadVector d n r hrD hrn p a μ) +
              sourceTailEmbed d r hrD (q u) μ) := by
      ext ν
      have hresν := congrFun (hres_tail u) ν
      rw [sub_eq_iff_eq_add] at hresν
      simpa [res, q, y, p, p0, sourceOrientedHeadGaugeHeadParameter, H,
        sourceOrientedNormalHeadVector, add_comm, add_left_comm, add_assoc]
        using hresν
    calc
      w (finSourceTail hrn u) μ =
          ((fun μ =>
            (∑ a : Fin r,
              L u a *
                sourceOrientedNormalHeadVector d n r hrD hrn p a μ) +
              sourceTailEmbed d r hrD (q u) μ) μ) := congrFun htail μ
      _ = sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceTail hrn u) μ := by
            rw [sourceOrientedNormalParameterVector_tail]

/-- After a Lorentz transformation has normalized the selected head frame to
the gauge normal head frame, the transformed tail labels have the corresponding
Schur mixed coordinates plus canonical shifted-tail coordinates. -/
theorem sourceOriented_headGauge_tailCoordinates_after_witt
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    (Λ : ComplexLorentzGroup d)
    (hΛhead :
      ∀ a : Fin r,
        complexLorentzAction Λ z (finSourceHead hrn a) =
          sourceOrientedNormalHeadVector d n r hrD hrn
            (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a) :
    ∃ q : Fin (n - r) → Fin (d + 1 - r) → ℂ,
      let H :=
        Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)
      let L :=
        sourceSchurMixedCoeff n r hrn G
          (sourceOrientedSchurHeadBlock n r hrn G)
      complexLorentzAction Λ z =
        sourceOrientedNormalParameterVector d n r hrD hrn
          { head := H
            mixed := L
            tail := q } := by
  let Q :=
    sourceOriented_headGaugeTailCoordinatesAfterWittData
      d n r hrD hrn Head hGvar hHead hz Λ hΛhead
  exact ⟨Q.1, Q.2⟩

/-- Once the determinant-one Witt step supplies a Lorentz transformation
normalizing the selected head frame, the matched head-gauge normal-parameter
data is fully mechanical. -/
def sourceOriented_headGaugeNormalParameterData_of_lorentz_head_normalized
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    (Λ : ComplexLorentzGroup d)
    (hΛhead :
      ∀ a : Fin r,
        complexLorentzAction Λ z (finSourceHead hrn a) =
          sourceOrientedNormalHeadVector d n r hrD hrn
            (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a) :
    SourceOrientedHeadGaugeNormalParameterData
      d n r hrD hrn hGvar Head := by
  let Q :=
    sourceOriented_headGaugeTailCoordinatesAfterWittData
      d n r hrD hrn Head hGvar hHead hz Λ hΛhead
  let q := Q.1
  let H :=
    Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)
  let L :=
    sourceSchurMixedCoeff n r hrn G
      (sourceOrientedSchurHeadBlock n r hrn G)
  let p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn :=
    { head := H
      mixed := L
      tail := q }
  have hq :
      complexLorentzAction Λ z =
        sourceOrientedNormalParameterVector d n r hrD hrn p := by
    simpa [q, H, L, p] using Q.2
  exact
    { p := p
      invariant_eq := by
        calc
          G = sourceOrientedMinkowskiInvariant d n z := hz
          _ = sourceOrientedMinkowskiInvariant d n
                (complexLorentzAction Λ z) := by
              exact (sourceOrientedMinkowskiInvariant_complexLorentzAction
                (d := d) (n := n) Λ z).symm
          _ = sourceOrientedMinkowskiInvariant d n
                (sourceOrientedNormalParameterVector d n r hrD hrn p) := by
              rw [hq]
      head_eq := by
        rfl }

/-- Typed output of the remaining determinant-one Witt head-normalization
theorem.

This is deliberately a `Type`-valued structure rather than a bare existential:
the downstream normal-parameter data contains computed tail coordinates, so
Lean must be able to use the chosen Lorentz element constructively. -/
structure SourceOrientedHeadGaugeWittData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z) where
  Λ : ComplexLorentzGroup d
  head_normalized :
    ∀ a : Fin r,
      complexLorentzAction Λ z (finSourceHead hrn a) =
        sourceOrientedNormalHeadVector d n r hrD hrn
          (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a

namespace SourceOrientedHeadGaugeWittData

/-- The checked consumer from typed Witt head-normalization data to matched
normal-parameter data. -/
def normalParameterData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    (W : SourceOrientedHeadGaugeWittData
      d n r hrD hrn Head hGvar hHead hz) :
    SourceOrientedHeadGaugeNormalParameterData
      d n r hrD hrn hGvar Head :=
  sourceOriented_headGaugeNormalParameterData_of_lorentz_head_normalized
    d n r hrD hrn Head hGvar hHead hz W.Λ W.head_normalized

end SourceOrientedHeadGaugeWittData

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

/-- If a proper complex Lorentz transformation carries one realizing source
tuple to a normal-parameter tuple whose head is the local gauge factor, then
the matched head-gauge normal-parameter data follows by oriented-invariant
preservation.

The remaining hard theorem is therefore exactly the finite-dimensional
construction of such a Lorentz normalization. -/
def sourceOriented_headGaugeNormalParameterData_of_lorentz_normalized
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn}
    (hhead :
      Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) =
        p.head)
    (Λ : ComplexLorentzGroup d)
    (hΛ :
      complexLorentzAction Λ z =
        sourceOrientedNormalParameterVector d n r hrD hrn p) :
    SourceOrientedHeadGaugeNormalParameterData
      d n r hrD hrn hGvar Head where
  p := p
  invariant_eq := by
    calc
      G = sourceOrientedMinkowskiInvariant d n z := hz
      _ = sourceOrientedMinkowskiInvariant d n (complexLorentzAction Λ z) := by
        exact (sourceOrientedMinkowskiInvariant_complexLorentzAction
          (d := d) (n := n) Λ z).symm
      _ = sourceOrientedMinkowskiInvariant d n
            (sourceOrientedNormalParameterVector d n r hrD hrn p) := by
        rw [hΛ]
  head_eq := hhead

/-- Blockwise version of
`sourceOriented_headGaugeNormalParameterData_of_lorentz_normalized`, using the
head/tail source-label split. -/
def sourceOriented_headGaugeNormalParameterData_of_lorentz_head_tail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn}
    (hhead :
      Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) =
        p.head)
    (Λ : ComplexLorentzGroup d)
    (hΛhead :
      ∀ a : Fin r,
        complexLorentzAction Λ z (finSourceHead hrn a) =
          sourceOrientedNormalParameterVector d n r hrD hrn p
            (finSourceHead hrn a))
    (hΛtail :
      ∀ u : Fin (n - r),
        complexLorentzAction Λ z (finSourceTail hrn u) =
          sourceOrientedNormalParameterVector d n r hrD hrn p
            (finSourceTail hrn u)) :
    SourceOrientedHeadGaugeNormalParameterData
      d n r hrD hrn hGvar Head :=
  sourceOriented_headGaugeNormalParameterData_of_lorentz_normalized
    d n r hrD hrn hGvar Head hz hhead Λ (by
      ext i μ
      rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
      · exact congrFun (hΛhead a) μ
      · exact congrFun (hΛtail u) μ)

end BHW
