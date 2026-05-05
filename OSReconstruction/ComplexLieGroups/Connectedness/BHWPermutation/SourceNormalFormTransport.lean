import Mathlib.LinearAlgebra.Matrix.Permutation
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSchurPatch
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedAdaptedRepresentative
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedNormalParameter

/-!
# Finite source normal-form transport support

This file begins the checked finite-dimensional infrastructure for the
Hall-Wightman Lemma-3 normal-form transport.  It contains only source-label
bookkeeping, block matrices, and permutation invariance of scalar Gram rank;
the analytic continuation and perturbative estimates remain in the proof docs
until their finite support is all checked.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Reindex source labels as the first `r` head labels followed by the
remaining `n - r` tail labels. -/
noncomputable def sourceHeadTailEquiv
    (n r : ℕ) (hrn : r ≤ n) :
    Fin n ≃ Fin r ⊕ Fin (n - r) :=
  (Equiv.ofBijective
    (Sum.elim (finSourceHead hrn) (finSourceTail hrn))
    (by
      constructor
      · intro x y hxy
        cases x with
        | inl a =>
            cases y with
            | inl b =>
                exact congrArg Sum.inl ((finSourceHead_injective hrn) hxy)
            | inr v =>
                exact False.elim ((finSourceHead_ne_finSourceTail hrn a v) hxy)
        | inr u =>
            cases y with
            | inl b =>
                exact False.elim ((finSourceHead_ne_finSourceTail hrn b u) hxy.symm)
            | inr v =>
                exact congrArg Sum.inr ((finSourceTail_injective hrn) hxy)
      · intro i
        rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
        · exact ⟨Sum.inl a, rfl⟩
        · exact ⟨Sum.inr u, rfl⟩)).symm

@[simp]
theorem sourceHeadTailEquiv_apply_head
    {n r : ℕ} (hrn : r ≤ n) (a : Fin r) :
    sourceHeadTailEquiv n r hrn (finSourceHead hrn a) = Sum.inl a := by
  rw [sourceHeadTailEquiv, Equiv.symm_apply_eq]
  rfl

@[simp]
theorem sourceHeadTailEquiv_apply_tail
    {n r : ℕ} (hrn : r ≤ n) (u : Fin (n - r)) :
    sourceHeadTailEquiv n r hrn (finSourceTail hrn u) = Sum.inr u := by
  rw [sourceHeadTailEquiv, Equiv.symm_apply_eq]
  rfl

/-- Block matrix for the source head/tail split, with lower-left block `B`
and upper-right block `Bᵀ`. -/
def sourceBlockMatrix
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ) :
    Fin n → Fin n → ℂ :=
  let E := sourceHeadTailEquiv n r hrn
  fun i j =>
    (Matrix.fromBlocks A B.transpose B C) (E i) (E j)

def sourceHeadHeadBlock
    (n r : ℕ) (hrn : r ≤ n)
    (G : Fin n → Fin n → ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun a b => G (finSourceHead hrn a) (finSourceHead hrn b)

def sourceTailHeadBlock
    (n r : ℕ) (hrn : r ≤ n)
    (G : Fin n → Fin n → ℂ) :
    Matrix (Fin (n - r)) (Fin r) ℂ :=
  fun u a => G (finSourceTail hrn u) (finSourceHead hrn a)

def sourceTailTailBlock
    (n r : ℕ) (hrn : r ≤ n)
    (G : Fin n → Fin n → ℂ) :
    Matrix (Fin (n - r)) (Fin (n - r)) ℂ :=
  fun u v => G (finSourceTail hrn u) (finSourceTail hrn v)

/-- Source-index linear change on ordered source tuples. -/
def sourceTupleLinearChange
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun i μ => ∑ a : Fin n, M i a * z a μ

/-- Source-index congruence on scalar Gram matrices. -/
def sourceGramCongruence
    (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (Z : Fin n → Fin n → ℂ) :
    Fin n → Fin n → ℂ :=
  fun i j => ∑ a : Fin n, ∑ b : Fin n, M i a * Z a b * M j b

/-- Canonical scalar Gram matrix for the Lemma-3 normal form.  The head block
is the inherited Minkowski-signature diagonal, not the Euclidean identity. -/
def hwLemma3CanonicalGram
    (d n r : ℕ) (hrD : r < d + 1) (hrn : r ≤ n) :
    Fin n → Fin n → ℂ :=
  sourceBlockMatrix n r hrn (sourceHeadMetric d r hrD) 0 0

theorem hwLemma3CanonicalGram_eq_sourceBlockMatrix
    (d n r : ℕ) (hrD : r < d + 1) (hrn : r ≤ n) :
    hwLemma3CanonicalGram d n r hrD hrn =
      sourceBlockMatrix n r hrn (sourceHeadMetric d r hrD) 0 0 := rfl

@[simp]
theorem sourceBlockMatrix_head_head
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)
    (a b : Fin r) :
    sourceBlockMatrix n r hrn A B C
        (finSourceHead hrn a) (finSourceHead hrn b) =
      A a b := by
  simp [sourceBlockMatrix]

@[simp]
theorem sourceBlockMatrix_tail_head
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)
    (u : Fin (n - r)) (a : Fin r) :
    sourceBlockMatrix n r hrn A B C
        (finSourceTail hrn u) (finSourceHead hrn a) =
      B u a := by
  simp [sourceBlockMatrix]

@[simp]
theorem sourceBlockMatrix_head_tail
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)
    (a : Fin r) (u : Fin (n - r)) :
    sourceBlockMatrix n r hrn A B C
        (finSourceHead hrn a) (finSourceTail hrn u) =
      B u a := by
  simp [sourceBlockMatrix]

@[simp]
theorem sourceBlockMatrix_tail_tail
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)
    (u v : Fin (n - r)) :
    sourceBlockMatrix n r hrn A B C
        (finSourceTail hrn u) (finSourceTail hrn v) =
      C u v := by
  simp [sourceBlockMatrix]

theorem sourceBlockMatrix_reindex_headTail
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ) :
    ((Matrix.of fun i j : Fin n => sourceBlockMatrix n r hrn A B C i j).submatrix
        (sourceHeadTailEquiv n r hrn).symm (sourceHeadTailEquiv n r hrn).symm) =
      Matrix.fromBlocks A B.transpose B C := by
  ext x y
  cases x with
  | inl a =>
      cases y with
      | inl b => simp [sourceBlockMatrix]
      | inr v => simp [sourceBlockMatrix]
  | inr u =>
      cases y with
      | inl b => simp [sourceBlockMatrix]
      | inr v => simp [sourceBlockMatrix]

theorem sourceBlockMatrix_of_headTailBlocks
    (n r : ℕ) (hrn : r ≤ n)
    (G : Fin n → Fin n → ℂ)
    (hG : G ∈ sourceSymmetricMatrixSpace n) :
    sourceBlockMatrix n r hrn
      (sourceHeadHeadBlock n r hrn G)
      (sourceTailHeadBlock n r hrn G)
      (sourceTailTailBlock n r hrn G) = G := by
  ext i j
  rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
  · rcases finSourceHead_tail_cases hrn j with ⟨b, rfl⟩ | ⟨v, rfl⟩
    · simp [sourceHeadHeadBlock]
    · simpa [sourceTailHeadBlock] using
        hG (finSourceTail hrn v) (finSourceHead hrn a)
  · rcases finSourceHead_tail_cases hrn j with ⟨b, rfl⟩ | ⟨v, rfl⟩
    · simp [sourceTailHeadBlock]
    · simp [sourceTailTailBlock]

theorem sourceHeadHeadBlock_symm_of_sourceSymmetric
    (n r : ℕ) (hrn : r ≤ n)
    {G : Fin n → Fin n → ℂ}
    (hG : G ∈ sourceSymmetricMatrixSpace n) :
    (sourceHeadHeadBlock n r hrn G).transpose =
      sourceHeadHeadBlock n r hrn G := by
  ext a b
  exact hG (finSourceHead hrn b) (finSourceHead hrn a)

/-- A permutation matrix for source labels.  Its left action on a tuple sends
the `i`-th output source vector to the old `σ i` source vector. -/
def sourcePermutationMatrix
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  σ.permMatrix ℂ

theorem sourcePermutationMatrix_det_isUnit
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsUnit (sourcePermutationMatrix n σ).det := by
  apply isUnit_iff_ne_zero.mpr
  simp [sourcePermutationMatrix]

theorem sourceTupleLinearChange_sourcePermutationMatrix
    (d n : ℕ) (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceTupleLinearChange d n
        (sourcePermutationMatrix n σ) z =
      fun i => z (σ i) := by
  ext i μ
  have h :=
    congrFun (Matrix.permMatrix_mulVec
      (R := ℂ) (σ := σ) (v := fun a : Fin n => z a μ)) i
  simp [sourceTupleLinearChange, sourcePermutationMatrix, Matrix.mulVec_eq_sum] at h ⊢

theorem sourceGramCongruence_sourcePermutationMatrix
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (Z : Fin n → Fin n → ℂ) :
    sourceGramCongruence n (sourcePermutationMatrix n σ) Z =
      sourcePermuteComplexGram n σ Z := by
  ext i j
  simp [sourceGramCongruence, sourcePermutationMatrix,
    sourcePermuteComplexGram, Equiv.Perm.permMatrix]

theorem sourceMinkowskiGram_sourceTupleLinearChange
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceMinkowskiGram d n (sourceTupleLinearChange d n M z) =
      sourceGramCongruence n M (sourceMinkowskiGram d n z) := by
  ext i j
  calc
    sourceMinkowskiGram d n (sourceTupleLinearChange d n M z) i j
        =
          ∑ μ : Fin (d + 1), ∑ a : Fin n, ∑ b : Fin n,
            M i a * (M j b *
              (z a μ * (z b μ * (MinkowskiSpace.metricSignature d μ : ℂ)))) := by
          simp [sourceMinkowskiGram, sourceTupleLinearChange,
            Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
    _ =
          ∑ a : Fin n, ∑ b : Fin n, ∑ μ : Fin (d + 1),
            M i a * (M j b *
              (z a μ * (z b μ * (MinkowskiSpace.metricSignature d μ : ℂ)))) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.sum_comm]
    _ =
        sourceGramCongruence n M (sourceMinkowskiGram d n z) i j := by
          simp [sourceMinkowskiGram, sourceGramCongruence,
            Finset.mul_sum, mul_comm, mul_left_comm]

theorem sourceMinkowskiGram_hwLemma3CanonicalSource
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceMinkowskiGram d n (hwLemma3CanonicalSource d n r) =
      hwLemma3CanonicalGram d n r hrD hrn := by
  ext i j
  rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
  · rcases finSourceHead_tail_cases hrn j with ⟨b, rfl⟩ | ⟨v, rfl⟩
    · simp [hwLemma3CanonicalGram,
        sourceMinkowskiGram_hwLemma3CanonicalSource_head d n r hrD hrn a b]
    · have htail := hwLemma3CanonicalSource_tail d n r hrn v
      simp [hwLemma3CanonicalGram, sourceMinkowskiGram, htail]
  · have htail_i := hwLemma3CanonicalSource_tail d n r hrn u
    rcases finSourceHead_tail_cases hrn j with ⟨b, rfl⟩ | ⟨v, rfl⟩
    · simp [hwLemma3CanonicalGram, sourceMinkowskiGram, htail_i]
    · have htail_j := hwLemma3CanonicalSource_tail d n r hrn v
      simp [hwLemma3CanonicalGram, sourceMinkowskiGram, htail_i, htail_j]

theorem hwLemma3_schurComplement_eq_zero_of_rank_eq
    (n r : ℕ) (hrn : r ≤ n)
    {G : Fin n → Fin n → ℂ}
    {A : Matrix (Fin r) (Fin r) ℂ}
    {B : Matrix (Fin (n - r)) (Fin r) ℂ}
    {C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ}
    (hGsym : G ∈ sourceSymmetricMatrixSpace n)
    (hBlock : G = sourceBlockMatrix n r hrn A B C)
    (hRank : sourceGramMatrixRank n G = r)
    (hA : IsUnit A.det) :
    C - B * A⁻¹ * B.transpose = 0 := by
  let E := sourceHeadTailEquiv n r hrn
  have hA' :
      IsUnit ((((Matrix.of fun i j : Fin n => G i j).reindex E E).toBlocks₁₁).det) := by
    subst G
    simpa [E, sourceBlockMatrix_reindex_headTail] using hA
  have hRank' :
      (Matrix.of fun i j : Fin n => G i j).rank = Fintype.card (Fin r) := by
    simpa [sourceGramMatrixRank] using hRank
  have hschur :=
    (rank_eq_card_iff_reindexed_schur_complement_eq_zero
      (Z := (Matrix.of fun i j : Fin n => G i j))
      (e := E)
      (hZsym := hGsym)
      (hA := hA')).1 hRank'
  subst G
  simpa [E, sourceBlockMatrix_reindex_headTail] using hschur

theorem sourceGramMatrixRank_sourcePermuteComplexGram
    (n : ℕ) (σ : Equiv.Perm (Fin n))
  (G : Fin n → Fin n → ℂ) :
    sourceGramMatrixRank n (sourcePermuteComplexGram n σ G) =
      sourceGramMatrixRank n G := by
  change (Matrix.submatrix G σ σ).rank = Matrix.rank G
  exact Matrix.rank_submatrix (G : Matrix (Fin n) (Fin n) ℂ) σ σ

theorem sourcePermuteComplexGram_mem_sourceSymmetricMatrixSpace
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {G : Fin n → Fin n → ℂ}
    (hG : G ∈ sourceSymmetricMatrixSpace n) :
    sourcePermuteComplexGram n σ G ∈ sourceSymmetricMatrixSpace n := by
  intro i j
  exact hG (σ i) (σ j)

theorem exists_sourcePermutation_movingPrincipalBlockToHead
    (n r : ℕ)
    (hrn : r ≤ n)
    {I : Fin r → Fin n}
    (hI : Function.Injective I) :
  ∃ σ : Equiv.Perm (Fin n),
      ∀ a : Fin r, σ (finSourceHead hrn a) = I a := by
  classical
  have hcard_sum :
      n = r + Fintype.card (selectedIndexComplement I) := by
    simpa using Fintype.card_congr (selectedIndexSumEquiv I hI)
  have hcard_compl :
      Fintype.card (selectedIndexComplement I) = n - r := by
    omega
  have hcard_tail :
      Fintype.card (Fin (n - r)) =
        Fintype.card (selectedIndexComplement I) := by
    simp [hcard_compl]
  let eTail : Fin (n - r) ≃ selectedIndexComplement I :=
    Fintype.equivOfCardEq hcard_tail
  let σ : Equiv.Perm (Fin n) :=
    (sourceHeadTailEquiv n r hrn).trans
      ((Equiv.refl (Fin r)).sumCongr eTail) |>.trans
        (selectedIndexSumEquiv I hI).symm
  refine ⟨σ, ?_⟩
  intro a
  simp only [σ, Equiv.trans_apply, sourceHeadTailEquiv_apply_head,
    Equiv.sumCongr_apply]
  rw [Equiv.symm_apply_eq]
  simp [selectedIndexSumEquiv_apply_selected I hI a]

end BHW
