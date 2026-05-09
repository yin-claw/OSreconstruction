import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOriented

/-!
# Real points in the oriented source invariant space

This file adds the real-source entry points for the oriented route.  It is
pure finite-coordinate algebra: real configurations are embedded into complex
source space and then mapped by the already checked oriented invariant.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Real configurations mapped to oriented source Gram-plus-determinant data. -/
def sourceRealOrientedMinkowskiInvariant
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    SourceOrientedGramData d n :=
  sourceOrientedMinkowskiInvariant d n (realEmbed x)

/-- The real embedding of source configurations is continuous. -/
theorem continuous_realEmbed_sourceNPoint
    (d n : ℕ) :
    Continuous
      (fun x : Fin n → Fin (d + 1) → ℝ => realEmbed x) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro μ
  exact
    Complex.continuous_ofReal.comp
      ((continuous_apply μ).comp (continuous_apply i))

/-- The real oriented source invariant is continuous. -/
theorem continuous_sourceRealOrientedMinkowskiInvariant
    (d n : ℕ) :
    Continuous (sourceRealOrientedMinkowskiInvariant d n) := by
  exact
    (continuous_sourceOrientedMinkowskiInvariant (d := d) (n := n)).comp
      (continuous_realEmbed_sourceNPoint d n)

/-- Every real oriented invariant is a point of the oriented source variety. -/
theorem sourceRealOrientedMinkowskiInvariant_mem_variety
    (d n : ℕ)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceRealOrientedMinkowskiInvariant d n x ∈
      sourceOrientedGramVariety d n := by
  exact ⟨realEmbed x, rfl⟩

/-- Permuting real source labels permutes their oriented source invariant. -/
theorem sourceRealOrientedMinkowskiInvariant_perm
    (d n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceRealOrientedMinkowskiInvariant d n (fun k => x (σ k)) =
      sourcePermuteOrientedGram d n σ
        (sourceRealOrientedMinkowskiInvariant d n x) := by
  change
    sourceOrientedMinkowskiInvariant d n
        (realEmbed (fun k => x (σ k))) =
      sourcePermuteOrientedGram d n σ
        (sourceOrientedMinkowskiInvariant d n (realEmbed x))
  simpa [realEmbed, permAct] using
    sourceOrientedMinkowskiInvariant_permAct
      (d := d) (n := n) σ (realEmbed x)

/-- The adjacent-right real source used in OS45 is the oriented permutation
of the left real source. -/
theorem sourceRealOrientedMinkowskiInvariant_perm_mul
    (d n : ℕ)
    (π τ : Equiv.Perm (Fin n))
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceRealOrientedMinkowskiInvariant d n (fun k => x ((π * τ) k)) =
      sourcePermuteOrientedGram d n τ
        (sourceRealOrientedMinkowskiInvariant d n (fun k => x (π k))) := by
  simpa [Equiv.Perm.mul_apply] using
    sourceRealOrientedMinkowskiInvariant_perm
      (d := d) (n := n) τ (fun k => x (π k))

/-- A real source patch is a uniqueness set for oriented
germ-holomorphic source representatives. -/
def sourceOrientedDistributionalUniquenessPatch
    (d n : ℕ)
    (E : Set (Fin n → Fin (d + 1) → ℝ)) : Prop :=
  E.Nonempty ∧
    ∀ (U : Set (SourceOrientedGramData d n))
      (Φ Ψ : SourceOrientedGramData d n → ℂ),
      IsRelOpenInSourceOrientedGramVariety d n U →
      IsConnected U →
      (∀ x ∈ E, sourceRealOrientedMinkowskiInvariant d n x ∈ U) →
      SourceOrientedVarietyGermHolomorphicOn d n Φ U →
      SourceOrientedVarietyGermHolomorphicOn d n Ψ U →
      (∀ x ∈ E,
        Φ (sourceRealOrientedMinkowskiInvariant d n x) =
          Ψ (sourceRealOrientedMinkowskiInvariant d n x)) →
      Set.EqOn Φ Ψ U

/-- Enlarging a uniqueness real patch preserves the uniqueness property. -/
theorem sourceOrientedDistributionalUniquenessPatch_mono
    {d n : ℕ}
    {E V : Set (Fin n → Fin (d + 1) → ℝ)}
    (hE : sourceOrientedDistributionalUniquenessPatch d n E)
    (hEV : E ⊆ V)
    (hV_ne : V.Nonempty) :
    sourceOrientedDistributionalUniquenessPatch d n V := by
  refine ⟨hV_ne, ?_⟩
  intro U Φ Ψ hU_rel hU_conn hV_U hΦ hΨ hEqV
  exact hE.2 U Φ Ψ hU_rel hU_conn
    (fun x hx => hV_U x (hEV hx)) hΦ hΨ
    (fun x hx => hEqV x (hEV hx))

/-- Permuting real source labels is a homeomorphism of the finite real source
configuration space. -/
noncomputable def realSourcePermuteHomeomorph
    (d n : ℕ)
    (π : Equiv.Perm (Fin n)) :
    (Fin n → Fin (d + 1) → ℝ) ≃ₜ
      (Fin n → Fin (d + 1) → ℝ) where
  toEquiv :=
    { toFun := fun x k => x (π k)
      invFun := fun y k => y (π.symm k)
      left_inv := by
        intro x
        ext k μ
        simp
      right_inv := by
        intro y
        ext k μ
        simp }
  continuous_toFun := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact (continuous_apply μ).comp (continuous_apply (π k))
  continuous_invFun := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact (continuous_apply μ).comp (continuous_apply (π.symm k))

/-- The image of an open real source patch under a finite source permutation is
open. -/
theorem isOpen_realSourcePermuteImage
    (d n : ℕ)
    (π : Equiv.Perm (Fin n))
    {E : Set (Fin n → Fin (d + 1) → ℝ)}
    (hE_open : IsOpen E) :
    IsOpen {y | ∃ x ∈ E, y = fun k => x (π k)} := by
  let H := realSourcePermuteHomeomorph d n π
  have hImage :
      {y | ∃ x ∈ E, y = fun k => x (π k)} = H '' E := by
    ext y
    constructor
    · rintro ⟨x, hxE, rfl⟩
      exact ⟨x, hxE, rfl⟩
    · rintro ⟨x, hxE, rfl⟩
      exact ⟨x, hxE, rfl⟩
  rw [hImage]
  exact H.isOpenMap E hE_open

/-- The image of a nonempty real source patch under a finite source
permutation is nonempty. -/
theorem nonempty_realSourcePermuteImage
    (d n : ℕ)
    (π : Equiv.Perm (Fin n))
    {E : Set (Fin n → Fin (d + 1) → ℝ)}
    (hE_ne : E.Nonempty) :
    {y | ∃ x ∈ E, y = fun k => x (π k)}.Nonempty := by
  rcases hE_ne with ⟨x, hxE⟩
  exact ⟨fun k => x (π k), x, hxE, rfl⟩

/-- The real selected full-frame matrix. -/
def sourceRealFullFrameMatrix
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun a μ => x (ι a) μ

/-- The real selected full-frame determinant. -/
def sourceRealFullFrameDet
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) : ℝ :=
  (sourceRealFullFrameMatrix d n ι x).det

/-- The real selected full-frame matrix depends continuously on the real
source configuration. -/
theorem continuous_sourceRealFullFrameMatrix
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Continuous (sourceRealFullFrameMatrix d n ι) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro μ
  exact (continuous_apply μ).comp (continuous_apply (ι a))

/-- The real selected full-frame determinant is continuous. -/
theorem continuous_sourceRealFullFrameDet
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Continuous (sourceRealFullFrameDet d n ι) := by
  exact (continuous_sourceRealFullFrameMatrix d n ι).matrix_det

/-- Complexifying the real selected full-frame matrix gives the complex
selected full-frame matrix of the real embedding. -/
theorem sourceFullFrameMatrix_realEmbed
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceFullFrameMatrix d n ι (realEmbed x) =
      (sourceRealFullFrameMatrix d n ι x).map Complex.ofReal := by
  ext a μ
  rfl

/-- Complexifying the real selected full-frame determinant gives the complex
full-frame determinant of the real embedding. -/
theorem sourceFullFrameDet_realEmbed
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceFullFrameDet d n ι (realEmbed x) =
      (sourceRealFullFrameDet d n ι x : ℂ) := by
  rw [sourceFullFrameDet, sourceRealFullFrameDet,
    sourceFullFrameMatrix_realEmbed]
  exact
    (RingHom.map_det Complex.ofRealHom
      (sourceRealFullFrameMatrix d n ι x)).symm

/-- The nonvanishing locus of a real full-frame determinant is open. -/
theorem sourceRealFullFrameDet_nonzero_isOpen
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    IsOpen
      {x : Fin n → Fin (d + 1) → ℝ |
        sourceRealFullFrameDet d n ι x ≠ 0} := by
  have hclosed : IsClosed ({0} : Set ℝ) := isClosed_singleton
  have hopen : IsOpen (({0} : Set ℝ)ᶜ) := hclosed.isOpen_compl
  have hpre :
      IsOpen ((sourceRealFullFrameDet d n ι) ⁻¹' (({0} : Set ℝ)ᶜ)) :=
    hopen.preimage (continuous_sourceRealFullFrameDet d n ι)
  simpa [Set.preimage] using hpre

/-- The real source direction which adds the identity matrix to the selected
full-frame rows. -/
def sourceRealFullFrameUnitTemplate
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Fin n → Fin (d + 1) → ℝ :=
  fun k μ =>
    ∑ a : Fin (d + 1),
      if ι a = k ∧ a = μ then (1 : ℝ) else 0

@[simp]
theorem sourceRealFullFrameUnitTemplate_selected
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (a μ : Fin (d + 1)) :
    sourceRealFullFrameUnitTemplate d n ι (ι a) μ =
      if a = μ then (1 : ℝ) else 0 := by
  classical
  by_cases h : a = μ
  · subst μ
    rw [sourceRealFullFrameUnitTemplate]
    simp
  · rw [sourceRealFullFrameUnitTemplate]
    have hzero :
        (∑ b : Fin (d + 1),
          if ι b = ι a ∧ b = μ then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b _hb
      by_cases hcond : ι b = ι a ∧ b = μ
      · have hba : b = a := ι.injective hcond.1
        have haμ : a = μ := by rw [← hba, hcond.2]
        exact False.elim (h haμ)
      · by_cases hba : b = a
        · have hbμ : b ≠ μ := by
            intro hbμ
            apply h
            rw [← hba, hbμ]
          simp [hba, h]
        · simp [hba]
    rw [hzero]
    simp [h]

/-- Along the unit-template line, the selected real full-frame matrix is
translated by `t • 1`. -/
theorem sourceRealFullFrameMatrix_add_unitTemplate
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ)
    (t : ℝ) :
    sourceRealFullFrameMatrix d n ι
        (x + t • sourceRealFullFrameUnitTemplate d n ι) =
      sourceRealFullFrameMatrix d n ι x +
        t • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := by
  ext a μ
  by_cases h : a = μ
  · subst μ
    simp [sourceRealFullFrameMatrix, Pi.add_apply, Pi.smul_apply]
  · simp [sourceRealFullFrameMatrix, Pi.add_apply, Pi.smul_apply, h]

/-- The selected full-frame determinant along the unit-template line. -/
def sourceRealFullFrameDetLinePolynomial
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) : Polynomial ℝ :=
  Matrix.det ((Polynomial.X : Polynomial ℝ) •
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) (Polynomial ℝ)) +
    (sourceRealFullFrameMatrix d n ι x).map Polynomial.C)

/-- The selected full-frame determinant line polynomial has leading
coefficient one. -/
theorem sourceRealFullFrameDetLinePolynomial_leadingCoeff
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    Polynomial.leadingCoeff
      (sourceRealFullFrameDetLinePolynomial d n ι x) = 1 := by
  simpa [sourceRealFullFrameDetLinePolynomial] using
    Polynomial.leadingCoeff_det_X_one_add_C
      (A := sourceRealFullFrameMatrix d n ι x)

/-- The selected full-frame determinant line polynomial is not zero. -/
theorem sourceRealFullFrameDetLinePolynomial_ne_zero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceRealFullFrameDetLinePolynomial d n ι x ≠ 0 := by
  intro hp
  have hlead :=
    sourceRealFullFrameDetLinePolynomial_leadingCoeff d n ι x
  have hlead0 := congrArg Polynomial.leadingCoeff hp
  rw [hlead] at hlead0
  norm_num at hlead0

/-- Evaluating the selected full-frame determinant line polynomial gives the
determinant on the corresponding real source line. -/
theorem sourceRealFullFrameDetLinePolynomial_eval
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ)
    (t : ℝ) :
    (sourceRealFullFrameDetLinePolynomial d n ι x).eval t =
      sourceRealFullFrameDet d n ι
        (x + t • sourceRealFullFrameUnitTemplate d n ι) := by
  unfold sourceRealFullFrameDetLinePolynomial sourceRealFullFrameDet
  rw [Matrix.det_apply', Polynomial.eval_finset_sum, Matrix.det_apply',
    sourceRealFullFrameMatrix_add_unitTemplate]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Polynomial.eval_mul, Polynomial.eval_intCast]
  congr 1
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : σ i = i
  · have hdiag : (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i (σ i) = 1 := by
      simp [Matrix.one_apply, h]
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, h,
      add_comm]
  · have hoff : (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i (σ i) = 0 := by
      have h' : i ≠ σ i := by
        intro hi
        exact h hi.symm
      simp [h']
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, h,
      add_comm]

/-- The nonvanishing locus of any selected real full-frame determinant is
dense. -/
theorem sourceRealFullFrameDet_nonzero_dense
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Dense {x : Fin n → Fin (d + 1) → ℝ |
      sourceRealFullFrameDet d n ι x ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU hU_nonempty
  rcases hU_nonempty with ⟨x, hxU⟩
  let line : ℝ → Fin n → Fin (d + 1) → ℝ :=
    fun t => x + t • sourceRealFullFrameUnitTemplate d n ι
  let p := sourceRealFullFrameDetLinePolynomial d n ι x
  have hp_ne : p ≠ 0 := by
    simpa [p] using
      sourceRealFullFrameDetLinePolynomial_ne_zero d n ι x
  have hroots_finite : ({t : ℝ | p.eval t = 0}).Finite := by
    apply Set.Finite.subset (p.roots.toFinset.finite_toSet)
    intro t ht
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset] at ht ⊢
    exact (Polynomial.mem_roots hp_ne).mpr ht
  have hdense : Dense (Set.univ \ {t : ℝ | p.eval t = 0}) := by
    simpa using
      (Dense.diff_finite (s := (Set.univ : Set ℝ)) dense_univ hroots_finite)
  have hline_cont : Continuous line := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hpre_open : IsOpen (line ⁻¹' U) := hU.preimage hline_cont
  have hpre_nonempty : (line ⁻¹' U).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [line] using hxU
  obtain ⟨t, htgood, htU⟩ :=
    hdense.exists_mem_open hpre_open hpre_nonempty
  have hp_eval_ne : p.eval t ≠ 0 := by
    have ht_not : t ∉ {t : ℝ | p.eval t = 0} := by
      simpa [Set.mem_diff, p] using htgood
    simpa using ht_not
  refine ⟨line t, htU, ?_⟩
  have heval : p.eval t =
      sourceRealFullFrameDet d n ι (line t) := by
    simpa [p, line] using
      sourceRealFullFrameDetLinePolynomial_eval d n ι x t
  exact fun h => hp_eval_ne (by rwa [heval])

/-- Every nonempty open real source patch contains a point where a selected
full-frame determinant is nonzero. -/
theorem nonempty_open_inter_sourceRealFullFrameDet_nonzero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {E : Set (Fin n → Fin (d + 1) → ℝ)}
    (hE_open : IsOpen E)
    (hE_ne : E.Nonempty) :
    (E ∩
      {x : Fin n → Fin (d + 1) → ℝ |
        sourceRealFullFrameDet d n ι x ≠ 0}).Nonempty := by
  rcases
    (sourceRealFullFrameDet_nonzero_dense d n ι).exists_mem_open
      hE_open hE_ne with
    ⟨x, hxdet, hxE⟩
  exact ⟨x, hxE, hxdet⟩

/-- The canonical head full-frame embedding when the source has at least
`d + 1` labels. -/
def sourceRealHeadFullFrameEmbedding
    (d n : ℕ)
    (hn : d + 1 ≤ n) :
    Fin (d + 1) ↪ Fin n where
  toFun := fun a => ⟨a.val, lt_of_lt_of_le a.isLt hn⟩
  inj' := by
    intro a b hab
    exact Fin.ext (congrArg (fun x : Fin n => x.val) hab)

end BHW
