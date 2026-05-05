import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexTakagiGlobal
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedTailEuclidean

/-!
# Small Euclidean tail realizations

This file starts the estimate-carrying Euclidean tail realization induction
used by the rank-deficient Hall-Wightman Schur charts.  The first checked
case is the top-rank branch: the just-proved small symmetric same-Gram
factorization gives a small dot-factor for the whole tail Gram matrix, and
the oriented determinant sheet is repaired by the stored coordinate
reflection.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Euclidean tail-variety points have Gram rank at most the tail dimension. -/
theorem sourceTailOrientedVariety_rank_le
    (D m : ℕ)
    {T : SourceTailOrientedData D m}
    (hTvar : T ∈ sourceTailOrientedVariety D m) :
    (Matrix.of fun i j : Fin m => T.gram i j).rank ≤ D := by
  rcases hTvar with ⟨q, rfl⟩
  have hmem :=
    sourceComplexDotGram_mem_sourceSymmetricRankLEVariety D m q
  rw [sourceSymmetricRankLEVariety_eq_rank_le] at hmem
  simpa [sourceTailOrientedInvariant, sourceComplexDotGram] using hmem.2

/-- Below top tail rank, all full Euclidean orientation coordinates vanish. -/
theorem sourceTailOrientedVariety_det_eq_zero_of_rank_lt
    (D m : ℕ)
    (hD : 0 < D)
    {T : SourceTailOrientedData D m}
    (hTvar : T ∈ sourceTailOrientedVariety D m)
    (hrank_lt : sourceGramMatrixRank m T.gram < D) :
    T.det = 0 := by
  funext ι
  have hrank_le_pred :
      (Matrix.of fun i j : Fin m => T.gram i j).rank ≤ D - 1 := by
    have hlt :
        (Matrix.of fun i j : Fin m => T.gram i j).rank < D := by
      simpa [sourceGramMatrixRank] using hrank_lt
    omega
  let e : Fin (D - 1 + 1) ≃ Fin D :=
    finCongr (Nat.sub_one_add_one_eq_of_pos hD)
  have hminor :=
    sourceMatrix_minors_eq_zero_of_rank_le
      (n := m) (D := D - 1) (Z := T.gram) hrank_le_pred
      (fun a : Fin (D - 1 + 1) => ι (e a))
      (fun a : Fin (D - 1 + 1) => ι (e a))
  let A : Matrix (Fin (D - 1 + 1)) (Fin (D - 1 + 1)) ℂ :=
    fun a b => T.gram (ι (e a)) (ι (e b))
  have hA_zero : A.det = 0 := by
    simpa [sourceMatrixMinor, A] using hminor
  have hblock_zero :
      Matrix.det (fun a b : Fin D => T.gram (ι a) (ι b)) = 0 := by
    have hreindex :
        Matrix.reindex e e A =
          (fun a b : Fin D => T.gram (ι a) (ι b)) := by
      ext a b
      simp [A, Matrix.reindex_apply]
    calc
      Matrix.det (fun a b : Fin D => T.gram (ι a) (ι b))
          = Matrix.det (Matrix.reindex e e A) := by rw [hreindex]
      _ = A.det := Matrix.det_reindex_self e A
      _ = 0 := hA_zero
  have hsquare := sourceTailOrientedVariety_selectedGram_det D m hTvar ι
  have hdet_sq_zero : T.det ι * T.det ι = 0 := by
    rw [← hsquare, hblock_zero]
  exact mul_self_eq_zero.mp hdet_sq_zero

private theorem sourceTailOrientedSmallRealization_fullRank_of_factorBound
    (D m : ℕ)
    (hD : 0 < D)
    {η ε : ℝ}
    (hfactor :
      ∀ S : Fin m → Fin m → ℂ,
        S ∈ sourceSymmetricMatrixSpace m →
        (Matrix.of fun i j : Fin m => S i j).rank ≤ D →
        (∀ i j, ‖S i j‖ < η) →
        ∃ q : Fin m → Fin D → ℂ,
          (∀ i a, ‖q i a‖ < ε) ∧
          sourceComplexDotGram D m q = S)
    (T : SourceTailOrientedData D m)
    (hTvar : T ∈ sourceTailOrientedVariety D m)
    (hrank : sourceGramMatrixRank m T.gram = D)
    (ι : Fin D ↪ Fin m)
    (hdetUnit :
      IsUnit (Matrix.det (fun a b : Fin D => T.gram (ι a) (ι b))))
    (hgramSmall : ∀ u v, ‖T.gram u v‖ < η) :
    ∃ q : Fin m → Fin D → ℂ,
      (∀ u μ, ‖q u μ‖ < ε) ∧
      sourceTailOrientedInvariant D m q = T := by
  have hsym : T.gram ∈ sourceSymmetricMatrixSpace m := by
    rcases hTvar with ⟨q, rfl⟩
    intro u v
    simp [sourceTailOrientedInvariant, mul_comm]
  have hRank :
      (Matrix.of fun i j : Fin m => T.gram i j).rank ≤ D := by
    simpa [sourceGramMatrixRank] using le_of_eq hrank
  rcases hfactor T.gram hsym hRank hgramSmall with
    ⟨q0, hq0Small, hq0Gram⟩
  have hgram :
      (sourceTailOrientedInvariant D m q0).gram = T.gram := by
    ext u v
    have huv := congrFun (congrFun hq0Gram u) v
    simpa [sourceTailOrientedInvariant, sourceComplexDotGram] using huv
  have hblock_ne :
      Matrix.det (fun a b : Fin D => T.gram (ι a) (ι b)) ≠ 0 :=
    isUnit_iff_ne_zero.mp hdetUnit
  have hdet_ne : T.det ι ≠ 0 := by
    intro hdet_zero
    apply hblock_ne
    calc
      Matrix.det (fun a b : Fin D => T.gram (ι a) (ι b))
          = T.det ι * T.det ι :=
            sourceTailOrientedVariety_selectedGram_det D m hTvar ι
      _ = 0 := by
            rw [hdet_zero]
            ring
  rcases sourceTailOrientedInvariant_or_reflection_eq_of_gram_eq
      D m hD hTvar ι hdet_ne q0 hgram with
    ⟨q, hqNorm, hqRealizes⟩
  refine ⟨q, ?_, hqRealizes⟩
  intro u μ
  rw [hqNorm u μ]
  exact hq0Small u μ

private theorem sourceTailOrientedSmallRealization_rankLt_of_factorBound
    (D m : ℕ)
    (hD : 0 < D)
    {η ε : ℝ}
    (hfactor :
      ∀ S : Fin m → Fin m → ℂ,
        S ∈ sourceSymmetricMatrixSpace m →
        (Matrix.of fun i j : Fin m => S i j).rank ≤ D →
        (∀ i j, ‖S i j‖ < η) →
        ∃ q : Fin m → Fin D → ℂ,
          (∀ i a, ‖q i a‖ < ε) ∧
          sourceComplexDotGram D m q = S)
    (T : SourceTailOrientedData D m)
    (hTvar : T ∈ sourceTailOrientedVariety D m)
    (hrank_lt : sourceGramMatrixRank m T.gram < D)
    (hgramSmall : ∀ u v, ‖T.gram u v‖ < η) :
    ∃ q : Fin m → Fin D → ℂ,
      (∀ u μ, ‖q u μ‖ < ε) ∧
      sourceTailOrientedInvariant D m q = T := by
  have hsym : T.gram ∈ sourceSymmetricMatrixSpace m := by
    rcases hTvar with ⟨q, rfl⟩
    intro u v
    simp [sourceTailOrientedInvariant, mul_comm]
  have hRank := sourceTailOrientedVariety_rank_le D m hTvar
  rcases hfactor T.gram hsym hRank hgramSmall with
    ⟨q0, hq0Small, hq0Gram⟩
  have hgram :
      (sourceTailOrientedInvariant D m q0).gram = T.gram := by
    ext u v
    have huv := congrFun (congrFun hq0Gram u) v
    simpa [sourceTailOrientedInvariant, sourceComplexDotGram] using huv
  have hq0var :
      sourceTailOrientedInvariant D m q0 ∈
        sourceTailOrientedVariety D m := by
    exact ⟨q0, rfl⟩
  have hq0_rank_lt :
      sourceGramMatrixRank m
        (sourceTailOrientedInvariant D m q0).gram < D := by
    rw [hgram]
    exact hrank_lt
  have hTdet_zero :
      T.det = 0 :=
    sourceTailOrientedVariety_det_eq_zero_of_rank_lt
      D m hD hTvar hrank_lt
  have hq0det_zero :
      (sourceTailOrientedInvariant D m q0).det = 0 :=
    sourceTailOrientedVariety_det_eq_zero_of_rank_lt
      D m hD hq0var hq0_rank_lt
  refine ⟨q0, hq0Small, ?_⟩
  apply SourceTailOrientedData.ext
  · exact hgram
  · rw [hq0det_zero, hTdet_zero]

/-- Full-rank selected-block Euclidean tail small realization.  The selected
minor only fixes the orientation sheet; the small factor is produced for the
whole Gram matrix by the global source-coordinate Takagi factorization. -/
theorem sourceTailOrientedSmallRealization_fullRankStep
    (D m : ℕ)
    (hD : 0 < D)
    (_hDm : D ≤ m)
    (ι : Fin D ↪ Fin m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧
      ∀ T : SourceTailOrientedData D m,
        T ∈ sourceTailOrientedVariety D m →
        sourceGramMatrixRank m T.gram = D →
        IsUnit
          (Matrix.det
            (fun a b : Fin D => T.gram (ι a) (ι b))) →
        (∀ u v, ‖T.gram u v‖ < η) →
        (∀ ι, ‖T.det ι‖ < η) →
        ∃ q : Fin m → Fin D → ℂ,
          (∀ u μ, ‖q u μ‖ < ε) ∧
          sourceTailOrientedInvariant D m q = T := by
  rcases sourceComplexSymmetric_factorSmall_rankLE m D hε with
    ⟨η, hη_pos, hfactor⟩
  refine ⟨η, hη_pos, ?_⟩
  intro T hTvar hrank hdetUnit hgramSmall _hdetSmall
  exact
    sourceTailOrientedSmallRealization_fullRank_of_factorBound
      D m hD hfactor T hTvar hrank ι hdetUnit hgramSmall

/-- Full-rank Euclidean tail small realization with the selected invertible
minor chosen internally from the rank and variety hypotheses. -/
theorem sourceTailOrientedSmallRealization_fullRank_bound
    (D m : ℕ)
    (hD : 0 < D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧
      ∀ T : SourceTailOrientedData D m,
        T ∈ sourceTailOrientedVariety D m →
        sourceGramMatrixRank m T.gram = D →
        (∀ u v, ‖T.gram u v‖ < η) →
        (∀ ι, ‖T.det ι‖ < η) →
        ∃ q : Fin m → Fin D → ℂ,
          (∀ u μ, ‖q u μ‖ < ε) ∧
          sourceTailOrientedInvariant D m q = T := by
  rcases sourceComplexSymmetric_factorSmall_rankLE m D hε with
    ⟨η, hη_pos, hfactor⟩
  refine ⟨η, hη_pos, ?_⟩
  intro T hTvar hrank hgramSmall _hdetSmall
  rcases sourceTail_exists_principalMinor_of_rank D m D T hTvar hrank with
    ⟨ι, hdetUnit⟩
  exact
    sourceTailOrientedSmallRealization_fullRank_of_factorBound
      D m hD hfactor T hTvar hrank ι hdetUnit hgramSmall

/-- Rank-deficient Euclidean tail small realization.  In rank `< D`, all full
orientation coordinates vanish, so the global same-Gram small factor already
has the correct oriented invariant. -/
theorem sourceTailOrientedSmallRealization_rankLt_bound
    (D m : ℕ)
    (hD : 0 < D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧
      ∀ T : SourceTailOrientedData D m,
        T ∈ sourceTailOrientedVariety D m →
        sourceGramMatrixRank m T.gram < D →
        (∀ u v, ‖T.gram u v‖ < η) →
        (∀ ι, ‖T.det ι‖ < η) →
        ∃ q : Fin m → Fin D → ℂ,
          (∀ u μ, ‖q u μ‖ < ε) ∧
          sourceTailOrientedInvariant D m q = T := by
  rcases sourceComplexSymmetric_factorSmall_rankLE m D hε with
    ⟨η, hη_pos, hfactor⟩
  refine ⟨η, hη_pos, ?_⟩
  intro T hTvar hrank_lt hgramSmall _hdetSmall
  exact
    sourceTailOrientedSmallRealization_rankLt_of_factorBound
      D m hD hfactor T hTvar hrank_lt hgramSmall

/-- Euclidean tail small realization in positive tail dimension.  The proof is
now a two-way rank split: top rank uses determinant-sheet repair, and lower
rank has all full determinant coordinates forced to zero. -/
theorem sourceTailOrientedSmallRealization
    (D m : ℕ)
    (hD : 0 < D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧
      ∀ T : SourceTailOrientedData D m,
        T ∈ sourceTailOrientedVariety D m →
        (∀ u v, ‖T.gram u v‖ < η) →
        (∀ ι, ‖T.det ι‖ < η) →
        ∃ q : Fin m → Fin D → ℂ,
          (∀ u μ, ‖q u μ‖ < ε) ∧
          sourceTailOrientedInvariant D m q = T := by
  rcases sourceTailOrientedSmallRealization_fullRank_bound
      D m hD hε with
    ⟨ηFull, hηFull_pos, hfull⟩
  rcases sourceTailOrientedSmallRealization_rankLt_bound
      D m hD hε with
    ⟨ηLow, hηLow_pos, hlow⟩
  let η := min ηFull ηLow
  have hη_pos : 0 < η := lt_min hηFull_pos hηLow_pos
  refine ⟨η, hη_pos, ?_⟩
  intro T hTvar hgramSmall hdetSmall
  let r := sourceGramMatrixRank m T.gram
  by_cases hr : r = D
  · exact
      hfull T hTvar hr
        (fun u v => lt_of_lt_of_le (hgramSmall u v) (min_le_left _ _))
        (fun ι => lt_of_lt_of_le (hdetSmall ι) (min_le_left _ _))
  · have hrle : r ≤ D := by
      simpa [r] using sourceTailOrientedVariety_rank_le D m hTvar
    have hrlt : r < D := lt_of_le_of_ne hrle hr
    exact
      hlow T hTvar hrlt
        (fun u v => lt_of_lt_of_le (hgramSmall u v) (min_le_right _ _))
        (fun ι => lt_of_lt_of_le (hdetSmall ι) (min_le_right _ _))

end BHW
