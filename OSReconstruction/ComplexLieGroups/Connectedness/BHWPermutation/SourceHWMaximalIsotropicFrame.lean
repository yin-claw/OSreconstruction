import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWLowRankNormalForm

/-!
# Maximal isotropic frames for Hall-Wightman low-rank geometry

This file proves the finite-dimensional existence of a maximal totally
isotropic frame inside any complex Minkowski subspace.  It does not yet prove
the stronger residual-alignment theorem needed by the low-rank Hall-Wightman
branch: the remaining geometric work must still choose such a frame in a way
compatible with the right residual span and produce the determinant-one
correction moving the left residual span into it.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- A maximal totally isotropic subspace inside a given ambient subspace,
maximal by finite dimension among all totally isotropic subspaces contained
in the ambient subspace. -/
structure ComplexMinkowskiMaximalIsotropicSubspaceIn
    (d : ℕ)
    (N : Submodule ℂ (Fin (d + 1) → ℂ)) where
  Q : Submodule ℂ (Fin (d + 1) → ℂ)
  Q_le : Q ≤ N
  Q_iso : ComplexMinkowskiTotallyIsotropicSubspace d Q
  maximal :
    ∀ R : Submodule ℂ (Fin (d + 1) → ℂ),
      R ≤ N →
      ComplexMinkowskiTotallyIsotropicSubspace d R →
      Module.finrank ℂ R ≤ Module.finrank ℂ Q

/-- A finite independent frame for a maximal totally isotropic subspace. -/
structure ComplexMinkowskiMaximalIsotropicFrameIn
    (d : ℕ)
    (N : Submodule ℂ (Fin (d + 1) → ℂ)) where
  s : ℕ
  q : Fin s → Fin (d + 1) → ℂ
  q_mem : ∀ c, q c ∈ N
  q_independent : LinearIndependent ℂ q
  q_pair_zero : ∀ c c', sourceComplexMinkowskiInner d (q c) (q c') = 0
  maximal :
    ∀ R : Submodule ℂ (Fin (d + 1) → ℂ),
      R ≤ N →
      ComplexMinkowskiTotallyIsotropicSubspace d R →
      Module.finrank ℂ R ≤ s

/-- Turn a maximal isotropic subspace into an explicit independent frame. -/
noncomputable def complexMinkowskiMaximalIsotropicFrameIn_of_subspace
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (F : ComplexMinkowskiMaximalIsotropicSubspaceIn d N) :
    ComplexMinkowskiMaximalIsotropicFrameIn d N := by
  let b := Module.finBasis ℂ F.Q
  let s := Module.finrank ℂ F.Q
  let q : Fin s → Fin (d + 1) → ℂ := fun c =>
    (b c : Fin (d + 1) → ℂ)
  refine
    { s := s
      q := q
      q_mem := ?_
      q_independent := ?_
      q_pair_zero := ?_
      maximal := ?_ }
  · intro c
    exact F.Q_le (b c).2
  · exact b.linearIndependent.map' F.Q.subtype (Submodule.ker_subtype F.Q)
  · intro c c'
    exact F.Q_iso (b c) (b c')
  · intro R hR_le hR_iso
    exact F.maximal R hR_le hR_iso

/-- The zero subspace is totally isotropic. -/
theorem complexMinkowskiTotallyIsotropic_bot
    (d : ℕ) :
    ComplexMinkowskiTotallyIsotropicSubspace d
      (⊥ : Submodule ℂ (Fin (d + 1) → ℂ)) := by
  intro x _
  have hx : (x : Fin (d + 1) → ℂ) = 0 := (Submodule.mem_bot ℂ).1 x.2
  rw [hx]
  simp [sourceComplexMinkowskiInner]

/-- Finite-dimensional maximal-finrank argument for the existence of a
maximal totally isotropic subspace inside any ambient subspace. -/
theorem complexMinkowski_maximalIsotropicSubspaceIn_exists
    (d : ℕ)
    (N : Submodule ℂ (Fin (d + 1) → ℂ)) :
    Nonempty (ComplexMinkowskiMaximalIsotropicSubspaceIn d N) := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ Q : Submodule ℂ (Fin (d + 1) → ℂ),
      Q ≤ N ∧
        ComplexMinkowskiTotallyIsotropicSubspace d Q ∧
        Module.finrank ℂ Q = k
  have hP0 : P 0 := by
    refine ⟨⊥, bot_le, complexMinkowskiTotallyIsotropic_bot d, ?_⟩
    simp
  let k := Nat.findGreatest P (Module.finrank ℂ N)
  have hPk : P k := Nat.findGreatest_spec (by simp) hP0
  rcases hPk with ⟨Q, hQ_le, hQ_iso, hQ_rank⟩
  refine ⟨{ Q := Q, Q_le := hQ_le, Q_iso := hQ_iso, maximal := ?_ }⟩
  intro R hR_le hR_iso
  have hR_bound : Module.finrank ℂ R ≤ Module.finrank ℂ N :=
    Submodule.finrank_mono hR_le
  have hP_R : P (Module.finrank ℂ R) :=
    ⟨R, hR_le, hR_iso, rfl⟩
  have hle : Module.finrank ℂ R ≤ k :=
    Nat.le_findGreatest hR_bound hP_R
  simpa [k, hQ_rank] using hle

/-- Every ambient subspace contains a finite maximal totally isotropic frame. -/
theorem complexMinkowski_maximalIsotropicFrameIn_exists
    (d : ℕ)
    (N : Submodule ℂ (Fin (d + 1) → ℂ)) :
    Nonempty (ComplexMinkowskiMaximalIsotropicFrameIn d N) := by
  rcases complexMinkowski_maximalIsotropicSubspaceIn_exists d N with ⟨F⟩
  exact ⟨complexMinkowskiMaximalIsotropicFrameIn_of_subspace F⟩

namespace ComplexMinkowskiMaximalIsotropicFrameIn

/-- The span of a maximal isotropic frame lies in its ambient subspace. -/
theorem span_le
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (F : ComplexMinkowskiMaximalIsotropicFrameIn d N) :
    Submodule.span ℂ (Set.range F.q) ≤ N := by
  rw [Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  exact F.q_mem c

/-- The span of a maximal isotropic frame is totally isotropic. -/
theorem span_isotropic
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (F : ComplexMinkowskiMaximalIsotropicFrameIn d N) :
    ComplexMinkowskiTotallyIsotropicSubspace d
      (Submodule.span ℂ (Set.range F.q)) :=
  complexMinkowskiTotallyIsotropic_span_range d F.s F.q F.q_pair_zero

/-- The span of an independent maximal frame has finrank equal to the frame
length. -/
theorem finrank_span
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (F : ComplexMinkowskiMaximalIsotropicFrameIn d N) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range F.q)) = F.s := by
  simpa using finrank_span_eq_card F.q_independent

/-- Maximality can be read against the finrank of the frame span. -/
theorem maximal_span
    {d : ℕ}
    {N : Submodule ℂ (Fin (d + 1) → ℂ)}
    (F : ComplexMinkowskiMaximalIsotropicFrameIn d N)
    (R : Submodule ℂ (Fin (d + 1) → ℂ))
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R) :
    Module.finrank ℂ R ≤
      Module.finrank ℂ (Submodule.span ℂ (Set.range F.q)) := by
  simpa [F.finrank_span] using F.maximal R hR_le hR_iso

end ComplexMinkowskiMaximalIsotropicFrameIn

/-- A totally isotropic subspace of the same ambient subspace embeds into a
maximal isotropic frame. -/
theorem complexMinkowski_totallyIsotropic_embedding_into_maximalFrame
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (F : ComplexMinkowskiMaximalIsotropicFrameIn d N)
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R) :
    ∃ E : R →ₗ[ℂ] (Fin (d + 1) → ℂ),
      Function.Injective E ∧
      (∀ x : R, E x ∈ Submodule.span ℂ (Set.range F.q)) ∧
      ∀ x y : R,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d
            (x : Fin (d + 1) → ℂ)
            (y : Fin (d + 1) → ℂ) :=
  complexMinkowski_totallyIsotropic_embedding_into_frame
    (d := d) (s := F.s) (R := R) (q := F.q)
    F.q_independent F.q_pair_zero hR_iso
    (F.maximal R hR_le hR_iso)

/-- A maximal isotropic frame supplies the dimension bound required by the
direct-sum residual embedding packet. -/
theorem directSum_identity_sum_isotropicMaximalFrameEmbedding
    {d : ℕ}
    {M N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (F : ComplexMinkowskiMaximalIsotropicFrameIn d N)
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hR_orth :
      ∀ x : R, ∀ m : M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0)
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R)
    (hq_orth_M :
      ∀ c (m : M),
        sourceComplexMinkowskiInner d (F.q c)
          (m : Fin (d + 1) → ℂ) = 0) :
    ∃ (E : R →ₗ[ℂ] (Fin (d + 1) → ℂ))
      (hE_inj : Function.Injective E)
      (hE_orth :
        ∀ x : R, ∀ m : M,
          sourceComplexMinkowskiInner d (E x)
            (m : Fin (d + 1) → ℂ) = 0),
      (∀ x : R, E x ∈ Submodule.span ℂ (Set.range F.q)) ∧
      (∀ x y : R,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d
            (x : Fin (d + 1) → ℂ)
            (y : Fin (d + 1) → ℂ)) ∧
      let T := directSum_identity_sum_isotropicEmbedding
        (d := d) M R E hM hR_orth hE_inj hE_orth
      ∀ x y : ↥(M ⊔ R),
        sourceComplexMinkowskiInner d
          ((T x : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ)
          ((T y : ↥(M ⊔ LinearMap.range E)) : Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ) :=
  directSum_identity_sum_isotropicFrameEmbedding
    (d := d) (s := F.s) (M := M) (R := R) (q := F.q)
    hM hR_orth F.q_independent F.q_pair_zero hq_orth_M hR_iso
    (F.maximal R hR_le hR_iso)

/-- The final geometric packet expected from the compatible maximal-frame
and determinant-one residual-alignment theorem.  It chooses a maximal frame
inside the orthogonal complement of the selected span and a Lorentz correction
fixing the selected span, with both residual families landing in that frame
span. -/
structure HWLowRankResidualFrameExtensionData
    {d n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S) where
  F : ComplexMinkowskiMaximalIsotropicFrameIn d
    (complexMinkowskiOrthogonalSubmodule d A.M)
  Λfix : ComplexLorentzGroup d
  Λfix_M :
    ∀ m : A.M,
      complexLorentzVectorAction Λfix
        (m : Fin (d + 1) → ℂ) =
      (m : Fin (d + 1) → ℂ)
  left_span :
    ∀ i,
      complexLorentzVectorAction Λfix (A.leftResidual i) ∈
        Submodule.span ℂ (Set.range F.q)
  right_span :
    ∀ i, A.rightResidual i ∈ Submodule.span ℂ (Set.range F.q)

/-- Convert the final geometric frame-extension packet into the residual
alignment data consumed by the checked low-rank normal-form assembly. -/
def hw_lowRank_residualAlignmentData_of_frameExtensionData
    {d n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    {A : HWLowRankSelectedSpanAlignment d n r z w I S}
    (D : HWLowRankResidualFrameExtensionData A) :
    HWLowRankResidualAlignmentData A :=
  { Λfix := D.Λfix
    s := D.F.s
    q := D.F.q
    Λfix_M := D.Λfix_M
    left_span := D.left_span
    right_span := D.right_span
    q_pair_zero := D.F.q_pair_zero
    q_orth_M := by
      intro c m
      exact
        (mem_complexMinkowskiOrthogonalSubmodule_iff
          d A.M (D.F.q c)).1 (D.F.q_mem c) m
    q_independent := D.F.q_independent }

end BHW
