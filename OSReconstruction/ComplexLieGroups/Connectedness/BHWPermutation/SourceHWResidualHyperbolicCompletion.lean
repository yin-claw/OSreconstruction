import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWResidualFrameExtension

/-!
# Hyperbolic completion data for residual isotropic subspaces

This file supplies the finite basis frame plus isotropic dual frame needed by
the remaining residual hyperbolic block construction.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- A finite basis frame for a totally isotropic subspace, together with an
isotropic dual frame in a chosen nondegenerate ambient subspace. -/
structure ComplexMinkowskiIsotropicSubspaceBasisDualFrameData
    (d : ℕ)
    (N R : Submodule ℂ (Fin (d + 1) → ℂ)) where
  k : ℕ
  frame : Fin k → Fin (d + 1) → ℂ
  dual : Fin k → Fin (d + 1) → ℂ
  k_eq : k = Module.finrank ℂ R
  frame_mem_R : ∀ c, frame c ∈ R
  frame_span_eq : Submodule.span ℂ (Set.range frame) = R
  frame_mem_N : ∀ c, frame c ∈ N
  dual_mem_N : ∀ c, dual c ∈ N
  frame_independent : LinearIndependent ℂ frame
  frame_pair_zero :
    ∀ c c', sourceComplexMinkowskiInner d (frame c) (frame c') = 0
  dual_pair_zero :
    ∀ c c', sourceComplexMinkowskiInner d (dual c) (dual c') = 0
  frame_dual :
    ∀ c c',
      sourceComplexMinkowskiInner d (frame c) (dual c') =
        if c = c' then (1 : ℂ) else 0

/-- A totally isotropic subspace inside a nondegenerate ambient subspace admits
a finite basis frame and an isotropic dual frame in that same ambient subspace.

This is the source/target hyperbolic-basis supply used before constructing the
completed residual block equivalence. -/
noncomputable def complexMinkowski_isotropicSubspace_basisDualFrameData
    {d : ℕ}
    {N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hN : ComplexMinkowskiNondegenerateSubspace d N)
    (hR_le : R ≤ N)
    (hR_iso : ComplexMinkowskiTotallyIsotropicSubspace d R) :
    ComplexMinkowskiIsotropicSubspaceBasisDualFrameData d N R := by
  let k := Module.finrank ℂ R
  let b := Module.finBasis ℂ R
  let frame : Fin k → Fin (d + 1) → ℂ := fun c => (b c : R)
  have hframe_mem_R : ∀ c, frame c ∈ R := by
    intro c
    exact (b c).2
  have hframe_mem_N : ∀ c, frame c ∈ N := by
    intro c
    exact hR_le (hframe_mem_R c)
  have hframe_independent : LinearIndependent ℂ frame := by
    rw [Fintype.linearIndependent_iff]
    intro a hsum c
    have hsum_R : (∑ i : Fin k, a i • b i) = 0 := by
      apply Subtype.ext
      simpa [frame] using hsum
    exact (Fintype.linearIndependent_iff.mp b.linearIndependent a hsum_R) c
  have hframe_span_eq :
      Submodule.span ℂ (Set.range frame) = R := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (by
        rintro x ⟨c, rfl⟩
        exact hframe_mem_R c)
    · intro x hx
      let xr : R := ⟨x, hx⟩
      have hx_repr :
          x = ∑ c : Fin k, b.repr xr c • frame c := by
        calc
          x = (xr : Fin (d + 1) → ℂ) := rfl
          _ = ((∑ c : Fin k, b.repr xr c • b c : R) :
                Fin (d + 1) → ℂ) := by
                exact congrArg
                  (fun y : R => (y : Fin (d + 1) → ℂ))
                  (b.sum_repr xr).symm
          _ = ∑ c : Fin k, ((b.repr xr c • b c : R) :
                Fin (d + 1) → ℂ) := by
                change R.subtype
                    (∑ c : Fin k, b.repr xr c • b c) =
                  ∑ c : Fin k, R.subtype (b.repr xr c • b c)
                rw [map_sum]
          _ = ∑ c : Fin k, b.repr xr c • frame c := by
                rfl
      rw [hx_repr]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem _ (b.repr xr c)
          (Submodule.subset_span ⟨c, rfl⟩)
  have hframe_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (frame c) (frame c') = 0 := by
    intro c c'
    exact hR_iso ⟨frame c, hframe_mem_R c⟩ ⟨frame c', hframe_mem_R c'⟩
  let hdual_exists :=
    complexMinkowski_isotropicFrame_dualFrameIn
      (d := d) (s := k) (N := N) (q := frame)
      hN hframe_mem_N hframe_independent hframe_pair_zero
  let dual : Fin k → Fin (d + 1) → ℂ := Classical.choose hdual_exists
  have hdual_mem_N : ∀ c, dual c ∈ N :=
    (Classical.choose_spec hdual_exists).1
  have hdual_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (dual c) (dual c') = 0 :=
    (Classical.choose_spec hdual_exists).2.1
  have hframe_dual :
      ∀ c c',
        sourceComplexMinkowskiInner d (frame c) (dual c') =
          if c = c' then (1 : ℂ) else 0 :=
    (Classical.choose_spec hdual_exists).2.2
  exact
    { k := k
      frame := frame
      dual := dual
      k_eq := rfl
      frame_mem_R := hframe_mem_R
      frame_span_eq := hframe_span_eq
      frame_mem_N := hframe_mem_N
      dual_mem_N := hdual_mem_N
      frame_independent := hframe_independent
      frame_pair_zero := hframe_pair_zero
      dual_pair_zero := hdual_pair_zero
      frame_dual := hframe_dual }

namespace ComplexMinkowskiIsotropicSubspaceBasisDualFrameData

/-- If the ambient subspace of a hyperbolic completion lies in the orthogonal
complement of `M`, then the basis half is orthogonal to `M`. -/
theorem frame_orthogonal_to_subspace
    {d : ℕ}
    {M N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (D : ComplexMinkowskiIsotropicSubspaceBasisDualFrameData d N R)
    (hN_le_orth : N ≤ complexMinkowskiOrthogonalSubmodule d M) :
    ∀ c (m : M),
      sourceComplexMinkowskiInner d (D.frame c)
        (m : Fin (d + 1) → ℂ) = 0 := by
  intro c m
  exact
    (mem_complexMinkowskiOrthogonalSubmodule_iff d M (D.frame c)).1
      (hN_le_orth (D.frame_mem_N c)) m

/-- If the ambient subspace of a hyperbolic completion lies in the orthogonal
complement of `M`, then the dual half is orthogonal to `M`. -/
theorem dual_orthogonal_to_subspace
    {d : ℕ}
    {M N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (D : ComplexMinkowskiIsotropicSubspaceBasisDualFrameData d N R)
    (hN_le_orth : N ≤ complexMinkowskiOrthogonalSubmodule d M) :
    ∀ c (m : M),
      sourceComplexMinkowskiInner d (D.dual c)
        (m : Fin (d + 1) → ℂ) = 0 := by
  intro c m
  exact
    (mem_complexMinkowskiOrthogonalSubmodule_iff d M (D.dual c)).1
      (hN_le_orth (D.dual_mem_N c)) m

/-- A selected nondegenerate block plus the hyperbolic completion supplied by
`ComplexMinkowskiIsotropicSubspaceBasisDualFrameData` is nondegenerate. -/
theorem selected_sup_hyperbolic_nondegenerate
    {d : ℕ}
    {M N R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (D : ComplexMinkowskiIsotropicSubspaceBasisDualFrameData d N R)
    (hM : ComplexMinkowskiNondegenerateSubspace d M)
    (hN_le_orth : N ≤ complexMinkowskiOrthogonalSubmodule d M) :
    ComplexMinkowskiNondegenerateSubspace d
      (M ⊔ (Submodule.span ℂ (Set.range D.frame) ⊔
        Submodule.span ℂ (Set.range D.dual))) :=
  complexMinkowski_selected_sup_hyperbolicFrameSpan_nondegenerate
    (d := d) (s := D.k) (M := M) (q := D.frame) (qDual := D.dual)
    hM (D.frame_orthogonal_to_subspace hN_le_orth)
    (D.dual_orthogonal_to_subspace hN_le_orth)
    D.frame_pair_zero D.dual_pair_zero D.frame_dual

end ComplexMinkowskiIsotropicSubspaceBasisDualFrameData

end BHW
