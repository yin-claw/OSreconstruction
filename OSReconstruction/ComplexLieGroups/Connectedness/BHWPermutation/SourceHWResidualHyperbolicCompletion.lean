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

/-- Canonical equivalence between the spans of two linearly independent
families with the same index type, obtained by transporting through coefficient
Finsupps. -/
noncomputable def linearEquiv_spanOfLinearIndependentFrames
    {ι V : Type*}
    [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V]
    {v w : ι → V}
    (hv : LinearIndependent ℂ v)
    (hw : LinearIndependent ℂ w) :
    Submodule.span ℂ (Set.range v) ≃ₗ[ℂ]
      Submodule.span ℂ (Set.range w) :=
  hv.linearCombinationEquiv.symm.trans hw.linearCombinationEquiv

/-- The canonical span equivalence sends each source frame vector to the
matching target frame vector. -/
theorem linearEquiv_spanOfLinearIndependentFrames_apply
    {ι V : Type*}
    [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V]
    {v w : ι → V}
    (hv : LinearIndependent ℂ v)
    (hw : LinearIndependent ℂ w)
    (i : ι) :
    ((linearEquiv_spanOfLinearIndependentFrames hv hw
      ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ :
        Submodule.span ℂ (Set.range w)) : V) = w i := by
  let x : Submodule.span ℂ (Set.range v) :=
    ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hx : hv.repr x = Finsupp.single i 1 := hv.repr_eq_single i x rfl
  change ((hw.linearCombinationEquiv (hv.repr x) :
    Submodule.span ℂ (Set.range w)) : V) = w i
  rw [hx]
  simp [LinearIndependent.linearCombinationEquiv_apply_coe,
    Finsupp.linearCombination_single]

/-- On totally isotropic source and target frame spans, the canonical span
equivalence preserves the complex Minkowski pairing. -/
theorem linearEquiv_spanOfLinearIndependentFrames_preserves_isotropic
    {d s : ℕ}
    {v w : Fin s → Fin (d + 1) → ℂ}
    (hv : LinearIndependent ℂ v)
    (hw : LinearIndependent ℂ w)
    (hv_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (v c) (v c') = 0)
    (hw_pair_zero :
      ∀ c c', sourceComplexMinkowskiInner d (w c) (w c') = 0) :
    let E := linearEquiv_spanOfLinearIndependentFrames hv hw
    ∀ x y : Submodule.span ℂ (Set.range v),
      sourceComplexMinkowskiInner d
        ((E x : Submodule.span ℂ (Set.range w)) : Fin (d + 1) → ℂ)
        ((E y : Submodule.span ℂ (Set.range w)) : Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) := by
  intro E x y
  have hv_iso :
      ComplexMinkowskiTotallyIsotropicSubspace d
        (Submodule.span ℂ (Set.range v)) :=
    complexMinkowskiTotallyIsotropic_span_range d s v hv_pair_zero
  have hw_iso :
      ComplexMinkowskiTotallyIsotropicSubspace d
        (Submodule.span ℂ (Set.range w)) :=
    complexMinkowskiTotallyIsotropic_span_range d s w hw_pair_zero
  rw [hw_iso (E x) (E y), hv_iso x y]

/-- The canonical span equivalences for two dual frame pairs preserve the
cross pairing between the frame span and the dual-frame span. -/
theorem linearEquiv_spanOfLinearIndependentFrames_preserves_dual_pairing
    {d s : ℕ}
    {v vDual w wDual : Fin s → Fin (d + 1) → ℂ}
    (hv : LinearIndependent ℂ v)
    (hvDual : LinearIndependent ℂ vDual)
    (hw : LinearIndependent ℂ w)
    (hwDual : LinearIndependent ℂ wDual)
    (hdual_v :
      ∀ c c',
        sourceComplexMinkowskiInner d (v c) (vDual c') =
          if c = c' then (1 : ℂ) else 0)
    (hdual_w :
      ∀ c c',
        sourceComplexMinkowskiInner d (w c) (wDual c') =
          if c = c' then (1 : ℂ) else 0) :
    let E := linearEquiv_spanOfLinearIndependentFrames hv hw
    let EDual := linearEquiv_spanOfLinearIndependentFrames hvDual hwDual
    ∀ x : Submodule.span ℂ (Set.range v),
    ∀ y : Submodule.span ℂ (Set.range vDual),
      sourceComplexMinkowskiInner d
        ((E x : Submodule.span ℂ (Set.range w)) : Fin (d + 1) → ℂ)
        ((EDual y : Submodule.span ℂ (Set.range wDual)) :
          Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d
        (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) := by
  intro E EDual x y
  let p : (a : Fin (d + 1) → ℂ) → (b : Fin (d + 1) → ℂ) →
      a ∈ Submodule.span ℂ (Set.range v) →
      b ∈ Submodule.span ℂ (Set.range vDual) → Prop :=
    fun a b ha hb =>
      sourceComplexMinkowskiInner d
        ((E ⟨a, ha⟩ : Submodule.span ℂ (Set.range w)) :
          Fin (d + 1) → ℂ)
        ((EDual ⟨b, hb⟩ : Submodule.span ℂ (Set.range wDual)) :
          Fin (d + 1) → ℂ) =
      sourceComplexMinkowskiInner d a b
  change p (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ) x.2 y.2
  apply Submodule.span_induction₂
    (R := ℂ) (s := Set.range v) (t := Set.range vDual) (p := p)
  · intro a b ha hb
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    dsimp [p]
    rw [linearEquiv_spanOfLinearIndependentFrames_apply hv hw i,
      linearEquiv_spanOfLinearIndependentFrames_apply hvDual hwDual j,
      hdual_w, hdual_v]
  · intro b hb
    dsimp [p]
    have hE_zero :
        ((E ⟨0, Submodule.zero_mem _⟩ :
          Submodule.span ℂ (Set.range w)) : Fin (d + 1) → ℂ) = 0 := by
      simp
    rw [hE_zero]
    simp [sourceComplexMinkowskiInner]
  · intro a ha
    dsimp [p]
    have hEDual_zero :
        ((EDual ⟨0, Submodule.zero_mem _⟩ :
          Submodule.span ℂ (Set.range wDual)) : Fin (d + 1) → ℂ) = 0 := by
      simp
    rw [hEDual_zero]
    simp [sourceComplexMinkowskiInner]
  · intro a b c ha hb hc hpa hpb
    dsimp [p] at hpa hpb ⊢
    have hE_add :
        ((E ⟨a + b, Submodule.add_mem _ ha hb⟩ :
          Submodule.span ℂ (Set.range w)) : Fin (d + 1) → ℂ) =
        ((E ⟨a, ha⟩ : Submodule.span ℂ (Set.range w)) :
          Fin (d + 1) → ℂ) +
        ((E ⟨b, hb⟩ : Submodule.span ℂ (Set.range w)) :
          Fin (d + 1) → ℂ) := by
      have h := congrArg
        (fun z : Submodule.span ℂ (Set.range w) =>
          (z : Fin (d + 1) → ℂ))
        (map_add E ⟨a, ha⟩ ⟨b, hb⟩)
      simpa using h
    rw [hE_add, sourceComplexMinkowskiInner_add_left,
      sourceComplexMinkowskiInner_add_left]
    rw [hpa, hpb]
  · intro a b c ha hb hc hpab hpac
    dsimp [p] at hpab hpac ⊢
    have hEDual_add :
        ((EDual ⟨b + c, Submodule.add_mem _ hb hc⟩ :
          Submodule.span ℂ (Set.range wDual)) : Fin (d + 1) → ℂ) =
        ((EDual ⟨b, hb⟩ : Submodule.span ℂ (Set.range wDual)) :
          Fin (d + 1) → ℂ) +
        ((EDual ⟨c, hc⟩ : Submodule.span ℂ (Set.range wDual)) :
          Fin (d + 1) → ℂ) := by
      have h := congrArg
        (fun z : Submodule.span ℂ (Set.range wDual) =>
          (z : Fin (d + 1) → ℂ))
        (map_add EDual ⟨b, hb⟩ ⟨c, hc⟩)
      simpa using h
    rw [hEDual_add, sourceComplexMinkowskiInner_add_right,
      sourceComplexMinkowskiInner_add_right]
    rw [hpab, hpac]
  · intro r a b ha hb hp
    dsimp [p] at hp ⊢
    have hE_smul :
        ((E ⟨r • a, Submodule.smul_mem _ r ha⟩ :
          Submodule.span ℂ (Set.range w)) : Fin (d + 1) → ℂ) =
        r • ((E ⟨a, ha⟩ : Submodule.span ℂ (Set.range w)) :
          Fin (d + 1) → ℂ) := by
      have h := congrArg
        (fun z : Submodule.span ℂ (Set.range w) =>
          (z : Fin (d + 1) → ℂ))
        (map_smul E r ⟨a, ha⟩)
      simpa using h
    rw [hE_smul, sourceComplexMinkowskiInner_smul_left,
      sourceComplexMinkowskiInner_smul_left]
    rw [hp]
  · intro r a b ha hb hp
    dsimp [p] at hp ⊢
    have hEDual_smul :
        ((EDual ⟨r • b, Submodule.smul_mem _ r hb⟩ :
          Submodule.span ℂ (Set.range wDual)) : Fin (d + 1) → ℂ) =
        r • ((EDual ⟨b, hb⟩ : Submodule.span ℂ (Set.range wDual)) :
          Fin (d + 1) → ℂ) := by
      have h := congrArg
        (fun z : Submodule.span ℂ (Set.range wDual) =>
          (z : Fin (d + 1) → ℂ))
        (map_smul EDual r ⟨b, hb⟩)
      simpa using h
    rw [hEDual_smul, sourceComplexMinkowskiInner_smul_right,
      sourceComplexMinkowskiInner_smul_right]
    rw [hp]

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

/-- An injective pairing-preserving embedding of the residual subspace sends
the source basis half of a hyperbolic completion to an independent isotropic
target frame, and that target frame admits an isotropic dual frame in the
target nondegenerate subspace. -/
theorem imageFrame_dualFrameIn
    {d : ℕ}
    {Nsrc Ntgt R : Submodule ℂ (Fin (d + 1) → ℂ)}
    (D : ComplexMinkowskiIsotropicSubspaceBasisDualFrameData d Nsrc R)
    (hNtgt : ComplexMinkowskiNondegenerateSubspace d Ntgt)
    (E : R →ₗ[ℂ] (Fin (d + 1) → ℂ))
    (hE_inj : Function.Injective E)
    (hE_mem : ∀ x : R, E x ∈ Ntgt)
    (hE_preserves :
      ∀ x y : R,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d
            (x : Fin (d + 1) → ℂ) (y : Fin (d + 1) → ℂ)) :
    let targetFrame : Fin D.k → Fin (d + 1) → ℂ :=
      fun c => E ⟨D.frame c, D.frame_mem_R c⟩
    ∃ targetDual : Fin D.k → Fin (d + 1) → ℂ,
      (∀ c, targetFrame c ∈ Ntgt) ∧
      LinearIndependent ℂ targetFrame ∧
      (∀ c c',
        sourceComplexMinkowskiInner d (targetFrame c) (targetFrame c') = 0) ∧
      (∀ c, targetDual c ∈ Ntgt) ∧
      (∀ c c',
        sourceComplexMinkowskiInner d (targetDual c) (targetDual c') = 0) ∧
      ∀ c c',
        sourceComplexMinkowskiInner d (targetFrame c) (targetDual c') =
          if c = c' then (1 : ℂ) else 0 := by
  intro targetFrame
  have htarget_mem : ∀ c, targetFrame c ∈ Ntgt := by
    intro c
    exact hE_mem ⟨D.frame c, D.frame_mem_R c⟩
  have htarget_pair_zero :
      ∀ c c',
        sourceComplexMinkowskiInner d (targetFrame c) (targetFrame c') = 0 := by
    intro c c'
    calc
      sourceComplexMinkowskiInner d (targetFrame c) (targetFrame c') =
          sourceComplexMinkowskiInner d
            (D.frame c) (D.frame c') := by
            exact hE_preserves
              ⟨D.frame c, D.frame_mem_R c⟩
              ⟨D.frame c', D.frame_mem_R c'⟩
      _ = 0 := D.frame_pair_zero c c'
  have htarget_independent : LinearIndependent ℂ targetFrame := by
    rw [Fintype.linearIndependent_iff]
    intro a hsum c
    let rFrame : Fin D.k → R := fun i => ⟨D.frame i, D.frame_mem_R i⟩
    have hE_sum :
        E (∑ i : Fin D.k, a i • rFrame i) = 0 := by
      calc
        E (∑ i : Fin D.k, a i • rFrame i) =
            ∑ i : Fin D.k, a i • E (rFrame i) := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [map_smul]
        _ = ∑ i : Fin D.k, a i • targetFrame i := rfl
        _ = 0 := hsum
    have hsum_R : (∑ i : Fin D.k, a i • rFrame i) = 0 :=
      hE_inj (by simpa using hE_sum)
    have hsum_V :
        ∑ i : Fin D.k, a i • D.frame i = 0 := by
      have h := congrArg
        (fun x : R => (x : Fin (d + 1) → ℂ)) hsum_R
      simpa [rFrame] using h
    exact
      (Fintype.linearIndependent_iff.mp D.frame_independent a hsum_V) c
  rcases complexMinkowski_isotropicFrame_dualFrameIn
      (d := d) (s := D.k) (N := Ntgt) (q := targetFrame)
      hNtgt htarget_mem htarget_independent htarget_pair_zero with
    ⟨targetDual, htargetDual_mem, htargetDual_pair_zero, htarget_dual⟩
  exact ⟨targetDual, htarget_mem, htarget_independent,
    htarget_pair_zero, htargetDual_mem, htargetDual_pair_zero, htarget_dual⟩

end ComplexMinkowskiIsotropicSubspaceBasisDualFrameData

end BHW
