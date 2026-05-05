import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurResidual

/-!
# Euclidean tail model for source-oriented Schur residuals

This file contains the finite coordinate bridge between the shifted residual
tail metric inherited from the ambient Minkowski source coordinates and the
Euclidean tail model used by the small-tail realization induction.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Euclidean tail oriented coordinates: ordinary dot-product Gram coordinates
and all top tail determinants. -/
structure SourceTailOrientedData
    (D m : ℕ) where
  gram : Matrix (Fin m) (Fin m) ℂ
  det : (Fin D ↪ Fin m) → ℂ

@[ext]
theorem SourceTailOrientedData.ext
    {D m : ℕ}
    {T U : SourceTailOrientedData D m}
    (hgram : T.gram = U.gram)
    (hdet : T.det = U.det) :
    T = U := by
  cases T
  cases U
  simp at hgram hdet ⊢
  exact ⟨hgram, hdet⟩

@[ext]
theorem SourceShiftedTailOrientedData.ext
    {d r m : ℕ}
    {hrD : r < d + 1}
    {T U : SourceShiftedTailOrientedData d r hrD m}
    (hgram : T.gram = U.gram)
    (hdet : T.det = U.det) :
    T = U := by
  cases T
  cases U
  simp at hgram hdet ⊢
  exact ⟨hgram, hdet⟩

/-- Euclidean tail oriented invariant of a tail tuple. -/
def sourceTailOrientedInvariant
    (D m : ℕ)
    (q : Fin m → Fin D → ℂ) :
    SourceTailOrientedData D m where
  gram := fun u v => ∑ μ : Fin D, q u μ * q v μ
  det := fun lam => Matrix.det (fun a μ : Fin D => q (lam a) μ)

@[simp]
theorem sourceTailOrientedInvariant_gram
    (D m : ℕ)
    (q : Fin m → Fin D → ℂ) :
    (sourceTailOrientedInvariant D m q).gram =
      fun u v => ∑ μ : Fin D, q u μ * q v μ := by
  rfl

@[simp]
theorem sourceTailOrientedInvariant_det
    (D m : ℕ)
    (q : Fin m → Fin D → ℂ)
    (lam : Fin D ↪ Fin m) :
    (sourceTailOrientedInvariant D m q).det lam =
      Matrix.det (fun a μ : Fin D => q (lam a) μ) := by
  rfl

/-- The Euclidean tail oriented variety. -/
def sourceTailOrientedVariety
    (D m : ℕ) :
    Set (SourceTailOrientedData D m) :=
  Set.range (sourceTailOrientedInvariant D m)

/-- Source-label permutation action on Euclidean tail oriented data. -/
def sourceTailPermuteOrientedData
    (D m : ℕ)
    (σ : Equiv.Perm (Fin m))
    (T : SourceTailOrientedData D m) :
    SourceTailOrientedData D m where
  gram := fun u v => T.gram (σ u) (σ v)
  det := fun lam => T.det (lam.trans σ.toEmbedding)

/-- Permuting the tail tuple permutes Euclidean tail oriented data. -/
theorem sourceTailOrientedInvariant_perm
    (D m : ℕ)
    (σ : Equiv.Perm (Fin m))
    (q : Fin m → Fin D → ℂ) :
    sourceTailOrientedInvariant D m (fun u => q (σ u)) =
      sourceTailPermuteOrientedData D m σ
        (sourceTailOrientedInvariant D m q) := by
  apply SourceTailOrientedData.ext
  · ext u v
    rfl
  · funext lam
    rfl

theorem sourceTailPermuteOrientedData_symm_apply
    (D m : ℕ)
    (σ : Equiv.Perm (Fin m))
    (T : SourceTailOrientedData D m) :
    sourceTailPermuteOrientedData D m σ.symm
        (sourceTailPermuteOrientedData D m σ T) = T := by
  apply SourceTailOrientedData.ext
  · ext u v
    simp [sourceTailPermuteOrientedData]
  · funext lam
    have hcomp : (lam.trans σ.symm.toEmbedding).trans σ.toEmbedding = lam := by
      ext a
      simp [Function.Embedding.trans]
    simp [sourceTailPermuteOrientedData, hcomp]

/-- Source-label permutations preserve membership in the Euclidean tail
oriented variety. -/
theorem sourceTailOrientedVariety_perm_iff
    (D m : ℕ)
    (σ : Equiv.Perm (Fin m))
    (T : SourceTailOrientedData D m) :
    sourceTailPermuteOrientedData D m σ T ∈
        sourceTailOrientedVariety D m ↔
      T ∈ sourceTailOrientedVariety D m := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨fun u => q (σ.symm u), ?_⟩
    apply SourceTailOrientedData.ext
    · ext u v
      have hgram :=
        congrFun
          (congrFun (congrArg SourceTailOrientedData.gram hq) (σ.symm u))
          (σ.symm v)
      simpa [sourceTailPermuteOrientedData] using hgram
    · funext lam
      have hdet :=
        congrFun (congrArg SourceTailOrientedData.det hq)
          (lam.trans σ.symm.toEmbedding)
      have hcomp : (lam.trans σ.symm.toEmbedding).trans σ.toEmbedding = lam := by
        ext a
        simp [Function.Embedding.trans]
      simpa [sourceTailPermuteOrientedData, sourceTailOrientedInvariant,
        hcomp] using hdet
  · rintro ⟨q, rfl⟩
    exact ⟨fun u => q (σ u), sourceTailOrientedInvariant_perm D m σ q⟩

/-- Stored diagonal normalization from the shifted tail metric to the Euclidean
tail dot product. -/
structure SourceShiftedTailMetricNormalization
    (d r : ℕ)
    (hrD : r < d + 1) where
  scale : Fin (d + 1 - r) → ℂ
  scale_ne_zero : ∀ μ, scale μ ≠ 0
  scale_sq :
    ∀ μ,
      scale μ * scale μ =
        (MinkowskiSpace.metricSignature d
          (finSourceTail (Nat.le_of_lt hrD) μ) : ℂ)
  detScale : ℂ
  detScale_eq : detScale = ∏ μ, scale μ
  detScale_ne_zero : detScale ≠ 0

/-- Canonical shifted-tail metric normalization. -/
def sourceShiftedTailMetricNormalization
    (d r : ℕ)
    (hrD : r < d + 1) :
    SourceShiftedTailMetricNormalization d r hrD where
  scale := sourceTailMetricScale d r hrD
  scale_ne_zero := sourceTailMetricScale_ne_zero d r hrD
  scale_sq := sourceTailMetricScale_mul_self d r hrD
  detScale := sourceTailMetricDetScale d r hrD
  detScale_eq := rfl
  detScale_ne_zero := sourceTailMetricDetScale_ne_zero d r hrD

/-- Convert shifted-tail oriented data to Euclidean tail data by the diagonal
normalization.  Gram coordinates are unchanged; full determinant coordinates
are multiplied by the product of the coordinate scales. -/
def sourceShiftedTailDataToEuclidean
    (d r m : ℕ)
    (hrD : r < d + 1)
    (N : SourceShiftedTailMetricNormalization d r hrD)
    (T : SourceShiftedTailOrientedData d r hrD m) :
    SourceTailOrientedData (d + 1 - r) m where
  gram := T.gram
  det := fun lam => N.detScale * T.det lam

theorem sourceVectorMinkowskiInner_sourceTailEmbed_tail
    (d r : ℕ)
    (hrD : r < d + 1)
    (q p : Fin (d + 1 - r) → ℂ) :
    sourceVectorMinkowskiInner d
        (sourceTailEmbed d r hrD q)
        (sourceTailEmbed d r hrD p) =
      ∑ μ : Fin (d + 1 - r),
        (MinkowskiSpace.metricSignature d
          (finSourceTail (Nat.le_of_lt hrD) μ) : ℂ) * q μ * p μ := by
  rw [sourceVectorMinkowskiInner]
  rw [← Equiv.sum_comp (sourceHeadTailSumEquiv d r hrD)
    (fun μ : Fin (d + 1) =>
      (MinkowskiSpace.metricSignature d μ : ℂ) *
        sourceTailEmbed d r hrD q μ * sourceTailEmbed d r hrD p μ)]
  simp [sourceHeadTailSumEquiv_inl, sourceHeadTailSumEquiv_inr]

/-- Scaling a shifted-tail tuple by the normalization scalars gives the
Euclidean tail datum associated to the shifted-tail oriented invariant. -/
theorem sourceShiftedTailInvariant_toEuclidean
    (d r m : ℕ)
    (hrD : r < d + 1)
    (N : SourceShiftedTailMetricNormalization d r hrD)
    (q : Fin m → Fin (d + 1 - r) → ℂ) :
    sourceTailOrientedInvariant (d + 1 - r) m
        (fun u μ => N.scale μ * q u μ) =
      sourceShiftedTailDataToEuclidean d r m hrD N
        (sourceShiftedTailOrientedInvariant d r hrD m q) := by
  apply SourceTailOrientedData.ext
  · ext u v
    simp [sourceTailOrientedInvariant, sourceShiftedTailDataToEuclidean,
      sourceShiftedTailOrientedInvariant, sourceShiftedTailGram,
      sourceVectorMinkowskiInner_sourceTailEmbed_tail]
    apply Finset.sum_congr rfl
    intro μ _
    calc
      N.scale μ * q u μ * (N.scale μ * q v μ)
          = (N.scale μ * N.scale μ) * q u μ * q v μ := by ring
      _ = (MinkowskiSpace.metricSignature d
            (finSourceTail (Nat.le_of_lt hrD) μ) : ℂ) * q u μ * q v μ := by
          rw [N.scale_sq μ]
  · funext lam
    let M : Matrix (Fin (d + 1 - r)) (Fin (d + 1 - r)) ℂ :=
      fun a μ => q (lam a) μ
    have hmat :
        (fun a μ : Fin (d + 1 - r) => N.scale μ * q (lam a) μ) =
          M * Matrix.diagonal N.scale := by
      ext a μ
      simp [M, Matrix.mul_apply, Matrix.diagonal, mul_comm]
    calc
      Matrix.det (fun a μ : Fin (d + 1 - r) => N.scale μ * q (lam a) μ)
          = Matrix.det (M * Matrix.diagonal N.scale) := by rw [hmat]
      _ = N.detScale * Matrix.det M := by
          rw [Matrix.det_mul, Matrix.det_diagonal, N.detScale_eq]
          ring
      _ = N.detScale *
            Matrix.det (fun a μ : Fin (d + 1 - r) => q (lam a) μ) := by
          rfl

/-- The diagonal normalization is injective on shifted-tail oriented data. -/
theorem sourceShiftedTailDataToEuclidean_injective
    (d r m : ℕ)
    (hrD : r < d + 1)
    (N : SourceShiftedTailMetricNormalization d r hrD) :
    Function.Injective
      (sourceShiftedTailDataToEuclidean d r m hrD N) := by
  intro T U hTU
  apply SourceShiftedTailOrientedData.ext
  · exact congrArg SourceTailOrientedData.gram hTU
  · funext lam
    have hdet := congrFun (congrArg SourceTailOrientedData.det hTU) lam
    exact mul_left_cancel₀ N.detScale_ne_zero hdet

/-- Shifted-tail variety membership is equivalent to Euclidean tail variety
membership after diagonal normalization. -/
theorem sourceShiftedTailVariety_toEuclidean_iff
    (d r m : ℕ)
    (hrD : r < d + 1)
    (N : SourceShiftedTailMetricNormalization d r hrD)
    (T : SourceShiftedTailOrientedData d r hrD m) :
    sourceShiftedTailDataToEuclidean d r m hrD N T ∈
        sourceTailOrientedVariety (d + 1 - r) m ↔
      T ∈ sourceShiftedTailOrientedVariety d r hrD m := by
  constructor
  · rintro ⟨qE, hqE⟩
    let q : Fin m → Fin (d + 1 - r) → ℂ :=
      fun u μ => (N.scale μ)⁻¹ * qE u μ
    refine ⟨q, ?_⟩
    apply sourceShiftedTailDataToEuclidean_injective d r m hrD N
    calc
      sourceShiftedTailDataToEuclidean d r m hrD N
          (sourceShiftedTailOrientedInvariant d r hrD m q)
          = sourceTailOrientedInvariant (d + 1 - r) m
              (fun u μ => N.scale μ * q u μ) := by
            exact (sourceShiftedTailInvariant_toEuclidean d r m hrD N q).symm
      _ = sourceTailOrientedInvariant (d + 1 - r) m qE := by
            congr
            ext u μ
            simp [q, N.scale_ne_zero μ]
      _ = sourceShiftedTailDataToEuclidean d r m hrD N T := hqE
  · rintro ⟨q, rfl⟩
    exact ⟨fun u μ => N.scale μ * q u μ,
      sourceShiftedTailInvariant_toEuclidean d r m hrD N q⟩

/-- A Euclidean realization of the normalized shifted-tail data descends to a
shifted-tail realization after scaling the coordinates back. -/
theorem sourceShiftedTailInvariant_eq_of_toEuclidean_eq
    (d r m : ℕ)
    (hrD : r < d + 1)
    (N : SourceShiftedTailMetricNormalization d r hrD)
    (q : Fin m → Fin (d + 1 - r) → ℂ)
    (T : SourceShiftedTailOrientedData d r hrD m)
    (hE :
      sourceTailOrientedInvariant (d + 1 - r) m
          (fun u μ => N.scale μ * q u μ) =
        sourceShiftedTailDataToEuclidean d r m hrD N T) :
    sourceShiftedTailOrientedInvariant d r hrD m q = T := by
  apply sourceShiftedTailDataToEuclidean_injective d r m hrD N
  rw [← hE]
  exact (sourceShiftedTailInvariant_toEuclidean d r m hrD N q).symm

/-- Estimate-compatible Euclidean small-realization packet for the tail model.
It stores both directions needed by the rank-deficient Schur chart: small data
are realized by small vectors, and small vectors have small invariant data. -/
structure SourceTailOrientedCompatibleSmallRealization
    (D m : ℕ) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  eta : ℝ
  eta_pos : 0 < eta
  realize :
    ∀ T : SourceTailOrientedData D m,
      T ∈ sourceTailOrientedVariety D m →
      (∀ u v, ‖T.gram u v‖ < eta) →
      (∀ ι, ‖T.det ι‖ < eta) →
      ∃ q : Fin m → Fin D → ℂ,
        (∀ u μ, ‖q u μ‖ < epsilon) ∧
        sourceTailOrientedInvariant D m q = T
  self_image_small :
    ∀ q : Fin m → Fin D → ℂ,
      (∀ u μ, ‖q u μ‖ < epsilon) →
      (∀ u v, ‖(sourceTailOrientedInvariant D m q).gram u v‖ < eta) ∧
      (∀ ι, ‖(sourceTailOrientedInvariant D m q).det ι‖ < eta)

/-- Estimate-compatible shifted-tail small-realization packet.  This is the
shifted-signature analogue consumed by the source-oriented Schur chart. -/
structure SourceShiftedTailCompatibleSmallRealization
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  eta : ℝ
  eta_pos : 0 < eta
  realize :
    ∀ T : SourceShiftedTailOrientedData d r hrD m,
      T ∈ sourceShiftedTailOrientedVariety d r hrD m →
      (∀ u v, ‖T.gram u v‖ < eta) →
      (∀ ι, ‖T.det ι‖ < eta) →
      ∃ q : Fin m → Fin (d + 1 - r) → ℂ,
        (∀ u μ, ‖q u μ‖ < epsilon) ∧
        sourceShiftedTailOrientedInvariant d r hrD m q = T
  self_image_small :
    ∀ q : Fin m → Fin (d + 1 - r) → ℂ,
      (∀ u μ, ‖q u μ‖ < epsilon) →
      (∀ u v,
        ‖(sourceShiftedTailOrientedInvariant d r hrD m q).gram u v‖ < eta) ∧
      (∀ ι,
        ‖(sourceShiftedTailOrientedInvariant d r hrD m q).det ι‖ < eta)

/-- The shifted-tail compatible small-realization packet follows mechanically
from the Euclidean one by diagonal normalization. -/
def sourceShiftedTailCompatibleSmallRealization_of_euclidean
    (d r m : ℕ)
    (hrD : r < d + 1)
    (E : SourceTailOrientedCompatibleSmallRealization (d + 1 - r) m) :
    SourceShiftedTailCompatibleSmallRealization d r hrD m := by
  classical
  let N := sourceShiftedTailMetricNormalization d r hrD
  have hscale_norm : ∀ μ : Fin (d + 1 - r), ‖N.scale μ‖ = 1 := by
    intro μ
    simp [N, sourceShiftedTailMetricNormalization, sourceTailMetricScale_norm]
  have hdet_norm : ‖N.detScale‖ = 1 := by
    simp [N, sourceShiftedTailMetricNormalization, sourceTailMetricDetScale_norm]
  refine
    { epsilon := E.epsilon
      epsilon_pos := E.epsilon_pos
      eta := E.eta
      eta_pos := E.eta_pos
      realize := ?_
      self_image_small := ?_ }
  · intro T hTvar hTgram hTdet
    have hTEvar :
        sourceShiftedTailDataToEuclidean d r m hrD N T ∈
          sourceTailOrientedVariety (d + 1 - r) m := by
      exact (sourceShiftedTailVariety_toEuclidean_iff d r m hrD N T).2 hTvar
    have hTEgram :
        ∀ u v, ‖(sourceShiftedTailDataToEuclidean d r m hrD N T).gram u v‖ <
          E.eta := by
      intro u v
      exact hTgram u v
    have hTEdet :
        ∀ ι, ‖(sourceShiftedTailDataToEuclidean d r m hrD N T).det ι‖ <
          E.eta := by
      intro ι
      calc
        ‖(sourceShiftedTailDataToEuclidean d r m hrD N T).det ι‖
            = ‖N.detScale * T.det ι‖ := rfl
        _ = ‖T.det ι‖ := by simp [hdet_norm]
        _ < E.eta := hTdet ι
    rcases E.realize
        (sourceShiftedTailDataToEuclidean d r m hrD N T)
        hTEvar hTEgram hTEdet with
      ⟨qE, hqE_small, hqE_realizes⟩
    let q : Fin m → Fin (d + 1 - r) → ℂ :=
      fun u μ => (N.scale μ)⁻¹ * qE u μ
    refine ⟨q, ?_, ?_⟩
    · intro u μ
      calc
        ‖q u μ‖ = ‖qE u μ‖ := by
          simp [q, norm_inv, hscale_norm μ]
        _ < E.epsilon := hqE_small u μ
    · apply sourceShiftedTailInvariant_eq_of_toEuclidean_eq d r m hrD N q T
      calc
        sourceTailOrientedInvariant (d + 1 - r) m
            (fun u μ => N.scale μ * q u μ)
            = sourceTailOrientedInvariant (d + 1 - r) m qE := by
              congr
              ext u μ
              simp [q, N.scale_ne_zero μ]
        _ = sourceShiftedTailDataToEuclidean d r m hrD N T := hqE_realizes
  · intro q hq_small
    have hqE_small :
        ∀ u μ, ‖N.scale μ * q u μ‖ < E.epsilon := by
      intro u μ
      calc
        ‖N.scale μ * q u μ‖ = ‖q u μ‖ := by
          simp [hscale_norm μ]
        _ < E.epsilon := hq_small u μ
    rcases E.self_image_small (fun u μ => N.scale μ * q u μ) hqE_small with
      ⟨hgramE, hdetE⟩
    constructor
    · intro u v
      have h := hgramE u v
      simpa [sourceShiftedTailInvariant_toEuclidean, sourceShiftedTailDataToEuclidean]
        using h
    · intro ι
      have h := hdetE ι
      have h' :
          ‖N.detScale *
              (sourceShiftedTailOrientedInvariant d r hrD m q).det ι‖ <
            E.eta := by
        simpa [sourceShiftedTailInvariant_toEuclidean,
          sourceShiftedTailDataToEuclidean] using h
      calc
        ‖(sourceShiftedTailOrientedInvariant d r hrD m q).det ι‖
            = ‖N.detScale *
                (sourceShiftedTailOrientedInvariant d r hrD m q).det ι‖ := by
              simp [hdet_norm]
        _ < E.eta := h'

end BHW
