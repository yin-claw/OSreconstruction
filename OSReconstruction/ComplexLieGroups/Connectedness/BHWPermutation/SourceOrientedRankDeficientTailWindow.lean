import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientTailRadius
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedTailSmallRealization
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientNormalImage

/-!
# Tail windows for rank-deficient source Schur charts

The rank-deficient local-image proof uses a target-shaped tail window, not a
same-radius compatible invariant/coordinate polydisc.  The window stores a
coordinate radius for the realizing shifted-tail tuple and a residual-data
radius from the checked one-way shifted-tail realization theorem.  The
parameter set itself includes the residual-data inequalities, making forward
containment a membership condition.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Tail-window data for the source-oriented rank-deficient normal
parameters.  The `tailRealize` field is exactly the checked one-way shifted
tail realization theorem at the chosen coordinate radius. -/
structure SourceOrientedRankDeficientTailWindowChoice
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) where
  tailCoordRadius : ℝ
  tailCoordRadius_pos : 0 < tailCoordRadius
  tailEta : ℝ
  tailEta_pos : 0 < tailEta
  tailRealize :
    ∀ T : SourceShiftedTailOrientedData d r hrD (n - r),
      T ∈ sourceShiftedTailOrientedVariety d r hrD (n - r) →
      (∀ u v, ‖T.gram u v‖ < tailEta) →
      (∀ ι, ‖T.det ι‖ < tailEta) →
      ∃ q : Fin (n - r) → Fin (d + 1 - r) → ℂ,
        (∀ u μ, ‖q u μ‖ < tailCoordRadius) ∧
        sourceShiftedTailOrientedInvariant d r hrD (n - r) q = T

/-- The target-shaped tail window on normal parameters.  It combines the raw
tail-coordinate bound needed for ambient shrink estimates with the shifted
tail invariant bounds needed for forward Schur containment. -/
def sourceOrientedRankDeficientTailWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    Set (SourceOrientedRankDeficientNormalParameter d n r hrD hrn) :=
  {p |
    (∀ u μ, ‖p.tail u μ‖ < Tail.tailCoordRadius) ∧
    (∀ u v,
      ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail).gram u v‖ <
        Tail.tailEta) ∧
    (∀ ι,
      ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail).det ι‖ <
        Tail.tailEta)}

@[simp]
theorem sourceTailEmbed_smul
    (d r : ℕ)
    (hrD : r < d + 1)
    (a : ℂ)
    (q : Fin (d + 1 - r) → ℂ) :
    sourceTailEmbed d r hrD (fun μ => a * q μ) =
      fun μ => a * sourceTailEmbed d r hrD q μ := by
  ext μ
  by_cases h : r ≤ μ.val
  · simp [sourceTailEmbed, h]
  · simp [sourceTailEmbed, h]

@[simp]
theorem sourceShiftedTailGram_smul
    (d r m : ℕ)
    (hrD : r < d + 1)
    (a : ℂ)
    (q : Fin m → Fin (d + 1 - r) → ℂ)
    (u v : Fin m) :
    sourceShiftedTailGram d r hrD m (fun u μ => a * q u μ) u v =
      a * a * sourceShiftedTailGram d r hrD m q u v := by
  rw [sourceShiftedTailGram_apply, sourceShiftedTailGram_apply]
  rw [sourceTailEmbed_smul, sourceTailEmbed_smul]
  rw [sourceVectorMinkowskiInner_smul_left, sourceVectorMinkowskiInner_smul_right]
  ring

@[simp]
theorem sourceShiftedTailOrientedInvariant_smul_gram
    (d r m : ℕ)
    (hrD : r < d + 1)
    (a : ℂ)
    (q : Fin m → Fin (d + 1 - r) → ℂ)
    (u v : Fin m) :
    (sourceShiftedTailOrientedInvariant d r hrD m
        (fun u μ => a * q u μ)).gram u v =
      a * a * (sourceShiftedTailOrientedInvariant d r hrD m q).gram u v := by
  exact sourceShiftedTailGram_smul d r m hrD a q u v

@[simp]
theorem sourceShiftedTailOrientedInvariant_smul_det
    (d r m : ℕ)
    (hrD : r < d + 1)
    (a : ℂ)
    (q : Fin m → Fin (d + 1 - r) → ℂ)
    (ι : Fin (d + 1 - r) ↪ Fin m) :
    (sourceShiftedTailOrientedInvariant d r hrD m
        (fun u μ => a * q u μ)).det ι =
      a ^ (d + 1 - r) *
        (sourceShiftedTailOrientedInvariant d r hrD m q).det ι := by
  let M : Matrix (Fin (d + 1 - r)) (Fin (d + 1 - r)) ℂ :=
    fun u μ => q (ι u) μ
  change (a • M).det = a ^ (d + 1 - r) * M.det
  rw [Matrix.det_smul]
  simp

/-- Scaling a tail tuple toward zero preserves membership in the target-shaped
tail window inequalities. -/
theorem sourceShiftedTailWindow_scaled
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn)
    {q : Fin (n - r) → Fin (d + 1 - r) → ℂ}
    (hq_coord : ∀ u μ, ‖q u μ‖ < Tail.tailCoordRadius)
    (hq_gram :
      ∀ u v,
        ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ <
          Tail.tailEta)
    (hq_det :
      ∀ ι,
        ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ <
          Tail.tailEta)
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 1) :
    (∀ u μ, ‖(t : ℂ) * q u μ‖ < Tail.tailCoordRadius) ∧
      (∀ u v,
        ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r)
            (fun u μ => (t : ℂ) * q u μ)).gram u v‖ < Tail.tailEta) ∧
      (∀ ι,
        ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r)
            (fun u μ => (t : ℂ) * q u μ)).det ι‖ < Tail.tailEta) := by
  have ht_norm : ‖(t : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
    exact ht_le
  constructor
  · intro u μ
    calc
      ‖(t : ℂ) * q u μ‖ = ‖(t : ℂ)‖ * ‖q u μ‖ := norm_mul _ _
      _ ≤ 1 * ‖q u μ‖ := mul_le_mul_of_nonneg_right ht_norm (norm_nonneg _)
      _ = ‖q u μ‖ := one_mul _
      _ < Tail.tailCoordRadius := hq_coord u μ
  constructor
  · intro u v
    calc
      ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r)
            (fun u μ => (t : ℂ) * q u μ)).gram u v‖ =
          ‖(t : ℂ) * (t : ℂ) *
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ := by
            rw [sourceShiftedTailOrientedInvariant_smul_gram]
      _ = ‖(t : ℂ)‖ * ‖(t : ℂ)‖ *
            ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ := by
            rw [norm_mul, norm_mul, mul_assoc]
      _ ≤ 1 * 1 *
            ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ := by
            gcongr
      _ = ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ := by
            ring
      _ < Tail.tailEta := hq_gram u v
  · intro ι
    have hpow_norm : ‖(t : ℂ) ^ (d + 1 - r)‖ ≤ 1 := by
      calc
        ‖(t : ℂ) ^ (d + 1 - r)‖ = ‖(t : ℂ)‖ ^ (d + 1 - r) := norm_pow _ _
        _ ≤ 1 ^ (d + 1 - r) := pow_le_pow_left₀ (norm_nonneg _) ht_norm _
        _ = 1 := one_pow _
    calc
      ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r)
            (fun u μ => (t : ℂ) * q u μ)).det ι‖ =
          ‖(t : ℂ) ^ (d + 1 - r) *
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ := by
            rw [sourceShiftedTailOrientedInvariant_smul_det]
      _ = ‖(t : ℂ) ^ (d + 1 - r)‖ *
            ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ :=
            norm_mul _ _
      _ ≤ 1 *
            ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ := by
            exact mul_le_mul_of_nonneg_right hpow_norm (norm_nonneg _)
      _ = ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ :=
            one_mul _
      _ < Tail.tailEta := hq_det ι

/-- The target-shaped window on shifted-tail tuples alone. -/
def sourceShiftedTailTupleWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    Set (Fin (n - r) → Fin (d + 1 - r) → ℂ) :=
  {q |
    (∀ u μ, ‖q u μ‖ < Tail.tailCoordRadius) ∧
    (∀ u v,
      ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v‖ <
        Tail.tailEta) ∧
    (∀ ι,
      ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι‖ <
        Tail.tailEta)}

/-- The shifted-tail tuple window is connected: it is star-shaped from zero. -/
theorem isConnected_sourceShiftedTailTupleWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsConnected (sourceShiftedTailTupleWindow d n r hrD hrn Tail) := by
  have hzero : (0 : Fin (n - r) → Fin (d + 1 - r) → ℂ) ∈
      sourceShiftedTailTupleWindow d n r hrD hrn Tail := by
    constructor
    · intro u μ
      simp [Tail.tailCoordRadius_pos]
    constructor
    · intro u v
      simp [sourceShiftedTailOrientedInvariant, sourceShiftedTailGram,
        sourceVectorMinkowskiInner, Tail.tailEta_pos]
    · intro ι
      have hDtail : 0 < d + 1 - r := by omega
      have hnonempty : Nonempty (Fin (d + 1 - r)) :=
        Fin.pos_iff_nonempty.mp hDtail
      have hdet0 :
          (sourceShiftedTailOrientedInvariant d r hrD (n - r)
            (0 : Fin (n - r) → Fin (d + 1 - r) → ℂ)).det ι = 0 := by
        simpa [sourceShiftedTailOrientedInvariant] using
          (Matrix.det_zero (n := Fin (d + 1 - r)) (R := ℂ) hnonempty)
      rw [hdet0, norm_zero]
      exact Tail.tailEta_pos
  have hstar : StarConvex ℝ
      (0 : Fin (n - r) → Fin (d + 1 - r) → ℂ)
      (sourceShiftedTailTupleWindow d n r hrD hrn Tail) := by
    rw [starConvex_iff_segment_subset]
    intro q hq
    rw [segment_subset_iff]
    intro a b ha0 hb0 hab
    have hb1 : b ≤ 1 := by linarith
    dsimp [sourceShiftedTailTupleWindow] at hq ⊢
    have hscaled :=
      sourceShiftedTailWindow_scaled d n r hrD hrn Tail
        hq.1 hq.2.1 hq.2.2 hb0 hb1
    have hseg :
        a • (0 : Fin (n - r) → Fin (d + 1 - r) → ℂ) + b • q =
          fun u μ => (b : ℂ) * q u μ := by
      ext u μ
      simp
    simpa [hseg] using hscaled
  exact (hstar.isPathConnected hzero).isConnected

/-- The tail window is open in the finite normal-parameter topology. -/
theorem isOpen_sourceOrientedRankDeficientTailWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    IsOpen (sourceOrientedRankDeficientTailWindow d n r hrD hrn Tail) := by
  let P := SourceOrientedRankDeficientNormalParameter d n r hrD hrn
  have htail_cont : Continuous (fun p : P => p.tail) :=
    continuous_sourceOrientedNormalParameter_tail
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  have hcoord_open :
      IsOpen {p : P | ∀ u μ, ‖p.tail u μ‖ < Tail.tailCoordRadius} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun u : Fin (n - r) =>
      isOpen_iInter_of_finite fun μ : Fin (d + 1 - r) =>
        isOpen_lt
          ((continuous_norm.comp
            ((continuous_apply μ).comp ((continuous_apply u).comp htail_cont))))
          continuous_const
  have hgram_open :
      IsOpen {p : P |
        ∀ u v,
          ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail).gram u v‖ <
            Tail.tailEta} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun u : Fin (n - r) =>
      isOpen_iInter_of_finite fun v : Fin (n - r) => by
        have hgram_q :
            Continuous (fun q : Fin (n - r) → Fin (d + 1 - r) → ℂ =>
              (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).gram u v) := by
          simpa [sourceShiftedTailOrientedInvariant] using
            (continuous_apply v).comp
              ((continuous_apply u).comp
                (continuous_sourceShiftedTailGram d r (n - r) hrD))
        exact
          isOpen_lt (continuous_norm.comp (hgram_q.comp htail_cont))
            continuous_const
  have hdet_open :
      IsOpen {p : P |
        ∀ ι,
          ‖(sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail).det ι‖ <
            Tail.tailEta} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun ι : Fin (d + 1 - r) ↪ Fin (n - r) => by
      have hdet_q :
          Continuous (fun q : Fin (n - r) → Fin (d + 1 - r) → ℂ =>
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) q).det ι) := by
        fun_prop
      exact
        isOpen_lt (continuous_norm.comp (hdet_q.comp htail_cont))
          continuous_const
  simpa [sourceOrientedRankDeficientTailWindow, Set.setOf_and] using
    hcoord_open.inter (hgram_open.inter hdet_open)

/-- The normal center lies in every positive tail window. -/
theorem sourceOrientedNormalCenterParameter_mem_tailWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    sourceOrientedNormalCenterParameter d n r hrD hrn ∈
      sourceOrientedRankDeficientTailWindow d n r hrD hrn Tail := by
  constructor
  · intro u μ
    simp [sourceOrientedNormalCenterParameter, Tail.tailCoordRadius_pos]
  constructor
  · intro u v
    simp [sourceOrientedNormalCenterParameter, sourceShiftedTailOrientedInvariant,
      sourceShiftedTailGram, sourceVectorMinkowskiInner, Tail.tailEta_pos]
  · intro ι
    have hDtail : 0 < d + 1 - r := by omega
    have hnonempty : Nonempty (Fin (d + 1 - r)) :=
      Fin.pos_iff_nonempty.mp hDtail
    have hdet0 :
        (sourceShiftedTailOrientedInvariant d r hrD (n - r)
          (sourceOrientedNormalCenterParameter d n r hrD hrn).tail).det ι = 0 := by
      simpa [sourceOrientedNormalCenterParameter, sourceShiftedTailOrientedInvariant] using
        (Matrix.det_zero (n := Fin (d + 1 - r)) (R := ℂ) hnonempty)
    rw [hdet0, norm_zero]
    exact Tail.tailEta_pos

/-- Build a tail-window choice from the checked one-way shifted-tail small
realization theorem. -/
def sourceOriented_rankDeficient_tailWindowChoice
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {tailCoordRadius : ℝ}
    (htailCoordRadius : 0 < tailCoordRadius) :
    SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn := by
  classical
  let hrealization :=
    sourceShiftedTailSmallRealization d r (n - r) hrD htailCoordRadius
  let tailEta := Classical.choose hrealization
  have htailEta_spec := Classical.choose_spec hrealization
  exact
    { tailCoordRadius := tailCoordRadius
      tailCoordRadius_pos := htailCoordRadius
      tailEta := tailEta
      tailEta_pos := htailEta_spec.1
      tailRealize := htailEta_spec.2 }

namespace SourceOrientedRankDeficientTailWindowChoice

/-- Window membership supplies Schur residual-tail smallness for normal
parameters with invertible head. -/
theorem normalParam_tail_small
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hH : IsUnit p.head.det)
    (hp : p ∈ sourceOrientedRankDeficientTailWindow d n r hrD hrn Tail) :
    SourceOrientedSchurTailSmallFor d n r hrD hrn Tail.tailEta
      (sourceOrientedMinkowskiInvariant d n
        (sourceOrientedNormalParameterVector d n r hrD hrn p))
      p.head := by
  have htail_eq :
      sourceOrientedSchurResidualTailData d n r hrD hrn
          (sourceOrientedMinkowskiInvariant d n
            (sourceOrientedNormalParameterVector d n r hrD hrn p))
          p.head =
        sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail :=
    sourceOrientedSchurResidualTailData_normalParameter
      d n r hrD hrn p hH
  exact
    { gram_bound := by
        intro u v
        have h := hp.2.1 u v
        simpa [htail_eq] using h
      det_bound := by
        intro ι
        have h := hp.2.2 ι
        simpa [htail_eq] using h }

end SourceOrientedRankDeficientTailWindowChoice

end BHW
