import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputACommonBoundary
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

private def centerSlot_local (μ : Fin (d + 1)) : Fin (2 * (d + 1)) :=
  finProdFinEquiv (⟨0, by omega⟩, μ)

private def diffSlot_local (μ : Fin (d + 1)) : Fin (2 * (d + 1)) :=
  finProdFinEquiv (⟨1, by omega⟩, μ)

/-- For `k = 2`, matching diff-block slots means the corresponding
`fromDiffFlat` configurations differ by a common complex translation of both
configuration points. -/
private theorem fromDiffFlat_eq_add_of_same_diffBlock_local
    (u v : Fin (2 * (d + 1)) → ℂ)
    (hdiff :
      ∀ μ : Fin (d + 1),
        u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) :
    let a : Fin (d + 1) → ℂ := fun μ =>
      u (centerSlot_local (d := d) μ) - v (centerSlot_local (d := d) μ)
    BHW.fromDiffFlat 2 d u =
      fun i =>
        (BHW.fromDiffFlat 2 d v) i + a := by
  intro a
  ext i μ
  fin_cases i
  · simp [BHW.fromDiffFlat, BHW.diffCoordEquiv_symm_apply, BHW.unflattenCfg,
      centerSlot_local, a]
  · have hμ := hdiff μ
    simp [BHW.fromDiffFlat, BHW.diffCoordEquiv_symm_apply, BHW.unflattenCfg,
      centerSlot_local, a]
    change
      u (centerSlot_local (d := d) μ) + u (diffSlot_local (d := d) μ) =
        v (centerSlot_local (d := d) μ) + v (diffSlot_local (d := d) μ) +
          (u (centerSlot_local (d := d) μ) - v (centerSlot_local (d := d) μ))
    calc
      u (centerSlot_local (d := d) μ) + u (diffSlot_local (d := d) μ)
          = u (centerSlot_local (d := d) μ) + v (diffSlot_local (d := d) μ) := by
              exact congrArg (fun z : ℂ => u (centerSlot_local (d := d) μ) + z) hμ
      _ = v (centerSlot_local (d := d) μ) + v (diffSlot_local (d := d) μ) +
            (u (centerSlot_local (d := d) μ) - v (centerSlot_local (d := d) μ)) := by
            ring

/-- Exact payoff theorem for the diff-block route: if the ACR(1) witness on
configurations is invariant under common complex translations of all points,
then the flattened witness `G := S₁ ∘ fromDiffFlat` depends only on the full
diff block. This isolates the precise extra structure still missing from the
current `schwinger_continuation_base_step_timeParametric` interface. -/
theorem diffBlockDependence_of_fromDiffFlat_translationInvariant_local
    (S₁ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hS₁_trans :
      ∀ (z : Fin 2 → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S₁ (fun i => z i + a) = S₁ z) :
    let G : (Fin (2 * (d + 1)) → ℂ) → ℂ := fun u => S₁ (BHW.fromDiffFlat 2 d u)
    ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
      G u = G v := by
  intro G u v hdiff
  dsimp [G]
  let a : Fin (d + 1) → ℂ := fun μ =>
    u (centerSlot_local (d := d) μ) - v (centerSlot_local (d := d) μ)
  have hcfg :
      BHW.fromDiffFlat 2 d u =
        fun i => (BHW.fromDiffFlat 2 d v) i + a := by
    simpa [a] using
      (fromDiffFlat_eq_add_of_same_diffBlock_local (d := d) u v hdiff)
  rw [hcfg, hS₁_trans]

/-- On the concrete zero-center section, the shifted real two-point kernel is
exactly the fixed-time center/difference kernel. This is the direct common-side
analogue of the probe representative identity, but with the center slot frozen
at `0` instead of an arbitrary translated center. -/
theorem k2TimeParametricKernel_eq_twoPointFixedTimeCenterDiffKernel_on_zeroCenterSection_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℝ)
    (ξ : SpacetimeDim d) :
    k2TimeParametricKernel (d := d) G
        ![(0 : SpacetimeDim d), ξ + timeShiftVec d t] =
      twoPointFixedTimeCenterDiffKernel_local
        (d := d) G ((t : ℂ) * Complex.I) ![(0 : SpacetimeDim d), ξ] := by
  rw [k2TimeParametricKernel, twoPointFixedTimeCenterDiffKernel_local]
  congr 1
  ext p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective p
  rcases q with ⟨i, μ⟩
  fin_cases i
  ·
    by_cases hμ : μ = 0
    ·
      subst hμ
      simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
        finProdFinEquiv.symm_apply_apply, wickRotatePoint, timeShiftVec, Function.update]
    ·
      simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
        finProdFinEquiv.symm_apply_apply, wickRotatePoint, timeShiftVec, Function.update, hμ]
  ·
    by_cases hμ : μ = 0
    ·
      subst hμ
      simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
        finProdFinEquiv.symm_apply_apply, wickRotatePoint, timeShiftVec, Function.update]
      ring
    ·
      simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
        finProdFinEquiv.symm_apply_apply, wickRotatePoint, timeShiftVec, Function.update, hμ]

/-- Under diff-block dependence, the lifted common slice is the ordinary
`k = 2` time-parametric kernel evaluated on the concrete positive-time section
`![(0), ξ + timeShiftVec (2s)]`. This rewrites the remaining strip-bound seam
as a bound question for the standard real-section kernel, rather than for the
artificial lifted slice itself. -/
theorem commonLiftedDifferenceSliceKernel_eq_k2TimeParametricKernel_on_zeroCenterShift_of_diffBlockDependence_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v)
    (s : ℝ)
    (ξ : SpacetimeDim d) :
    commonLiftedDifferenceSliceKernel_local (d := d) G s ξ =
      k2TimeParametricKernel (d := d) G
        ![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)] := by
  calc
    commonLiftedDifferenceSliceKernel_local (d := d) G s ξ
        =
      twoPointFixedTimeCenterDiffKernel_local
        (d := d) G ((((s + s) : ℂ) * Complex.I)) ![(0 : SpacetimeDim d), ξ] := by
          symm
          exact
            twoPointFixedTimeCenterDiffKernel_eq_commonLiftedDifferenceSlice_of_diffBlockDependence_local
              (d := d) G hG_diff s ![(0 : SpacetimeDim d), ξ]
    _ =
      k2TimeParametricKernel (d := d) G
        ![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)] := by
          symm
          simpa using
            k2TimeParametricKernel_eq_twoPointFixedTimeCenterDiffKernel_on_zeroCenterSection_local
              (d := d) G (s + s) ξ

/-- The current frontier strip-bound seam can equivalently be paid on the
ordinary `k2TimeParametricKernel` along the concrete zero-center shifted
section. This is the cleanest reduction of the common-`G` analytic gap: once
the real-section kernel is polynomially bounded on `!(0, ξ + 2s e₀)`, the
lifted-slice strip bound follows formally. -/
theorem exists_common_lifted_difference_slice_strip_bound_of_k2TimeParametricKernel_zeroCenterShift_bound_of_diffBlockDependence_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v)
    (s : ℝ)
    (C_bd : ℝ) (N : ℕ)
    (hC : 0 < C_bd)
    (hK_bound : ∀ ξ : SpacetimeDim d, -(s + s) < ξ 0 →
      ‖k2TimeParametricKernel (d := d) G
          ![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)]‖ ≤
        C_bd * (1 + ‖ξ‖) ^ N) :
    ∃ (C_bd' : ℝ) (N' : ℕ),
      0 < C_bd' ∧
      ∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)‖ ≤
          C_bd' * (1 + ‖z‖) ^ N' := by
  refine ⟨C_bd, N, hC, ?_⟩
  intro z hz
  have hsec :
      ‖k2TimeParametricKernel (d := d) G
          ![(0 : SpacetimeDim d), z 1 + timeShiftVec d (s + s)]‖ ≤
        C_bd * (1 + ‖z 1‖) ^ N :=
    hK_bound (z 1) hz
  rw [← commonLiftedDifferenceSliceKernel_eq_k2TimeParametricKernel_on_zeroCenterShift_of_diffBlockDependence_local
      (d := d) G hG_diff s (z 1)] at hsec
  have hz1_le : ‖z 1‖ ≤ ‖z‖ := norm_le_pi_norm z 1
  exact le_trans hsec <| by
    gcongr

/-- Conditional strip-bound transfer from the concrete zero-center section to
an arbitrary comparison kernel on the positive strip.

This theorem is intentionally neutral about the source of the comparison
kernel. It isolates the genuinely reusable logical step: once the common
zero-center section is pointwise identified with some one-variable comparison
kernel that already has a strip polynomial bound, the common lifted slice
inherits the same bound under diff-block dependence. -/
theorem exists_common_lifted_difference_slice_strip_bound_of_zeroCenterShift_eq_comparison_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v)
    (K_cmp : SpacetimeDim d → ℂ)
    (s : ℝ)
    (C_bd : ℝ) (N : ℕ)
    (hC : 0 < C_bd)
    (hK_bound : ∀ ξ : SpacetimeDim d, -(s + s) < ξ 0 →
      ‖K_cmp ξ‖ ≤ C_bd * (1 + ‖ξ‖) ^ N)
    (hsec_eq : ∀ ξ : SpacetimeDim d, -(s + s) < ξ 0 →
      k2TimeParametricKernel (d := d) G
          ![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)] =
        K_cmp ξ) :
    ∃ (C_bd : ℝ) (N : ℕ),
      0 < C_bd ∧
      ∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)‖ ≤
          C_bd * (1 + ‖z‖) ^ N := by
  have hsection_bound :
      ∀ ξ : SpacetimeDim d, -(s + s) < ξ 0 →
        ‖k2TimeParametricKernel (d := d) G
            ![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)]‖ ≤
          C_bd * (1 + ‖ξ‖) ^ N := by
    intro ξ hz
    simpa [hsec_eq ξ hz] using hK_bound ξ hz
  exact
    exists_common_lifted_difference_slice_strip_bound_of_k2TimeParametricKernel_zeroCenterShift_bound_of_diffBlockDependence_local
      (d := d) G hG_diff s C_bd N hC hsection_bound

/-- A continuous kernel that is bounded almost everywhere by a constant is in
fact bounded everywhere by the same constant. We use this to upgrade the
standard fixed-time kernel bound package to a pointwise strip bound after
transporting through the center/difference kernel and diff-block dependence. -/
private theorem norm_le_of_continuous_ae_const_bound_local
    (K : NPointDomain d 2 → ℂ)
    (hK_cont : Continuous K)
    (C_bd : ℝ)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume, ‖K x‖ ≤ C_bd) :
    ∀ x : NPointDomain d 2, ‖K x‖ ≤ C_bd := by
  intro x
  by_contra hx
  let U : Set (NPointDomain d 2) := {y | C_bd < ‖K y‖}
  have hU_open : IsOpen U := by
    simpa [U] using isOpen_lt continuous_const (continuous_norm.comp hK_cont)
  have hU_ae_empty : U =ᵐ[volume] (∅ : Set (NPointDomain d 2)) := by
    filter_upwards [hK_bound] with y hy
    apply propext
    simp only [U, Set.mem_setOf_eq, Set.mem_empty_iff_false]
    constructor
    · intro hy'
      exact (not_lt_of_ge hy) hy'
    · intro hfalse
      exact False.elim hfalse
  have hU_eq_empty : U = (∅ : Set (NPointDomain d 2)) := by
    exact (hU_open.ae_eq_empty_iff_eq (μ := volume)).mp hU_ae_empty
  have hxU : x ∈ U := by
    simpa [U] using hx
  have hx_notU : x ∉ U := by
    simpa [hU_eq_empty]
  exact hx_notU hxU

/-- Direct zero-center-section payoff from the ordinary fixed-time kernel
const-bound package.

This matches the sharpened frontier surface exactly: once the common witness has
the standard fixed-time kernel continuity/measurability/constant-bound package
at time `2s`, the remaining root Input-A theorem is paid on the explicit
section `![(0), ξ + 2s e₀]` without any additional slice geometry. -/
theorem exists_common_k2TimeParametricKernel_zeroCenterShift_bound_of_twoPointFixedTimeKernel_constBound_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (s : ℝ)
    (C_bd : ℝ)
    (hC : 0 < C_bd)
    (hK_cont : Continuous
      (twoPointFixedTimeKernel (d := d) G ((((s + s) : ℂ) * Complex.I))))
    (hK_meas : AEStronglyMeasurable
      (twoPointFixedTimeKernel (d := d) G ((((s + s) : ℂ) * Complex.I))) volume)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeKernel (d := d) G ((((s + s) : ℂ) * Complex.I)) x‖ ≤ C_bd) :
    ∃ (C_bd' : ℝ) (N : ℕ),
      0 < C_bd' ∧
      ∀ ξ : SpacetimeDim d, -(s + s) < ξ 0 →
        ‖k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)] : NPointDomain d 2)‖ ≤
          C_bd' * (1 + ‖ξ‖) ^ N := by
  obtain ⟨hK₂_cont, _hK₂_meas, hK₂_bound_ae⟩ :=
    exists_constBound_package_twoPointFixedTimeCenterDiffKernel_local
      (d := d) G ((((s + s) : ℂ) * Complex.I)) hK_cont hK_meas C_bd hK_bound
  have hK₂_bound :
      ∀ z : NPointDomain d 2,
        ‖twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z‖ ≤ C_bd :=
    norm_le_of_continuous_ae_const_bound_local
      (d := d)
      (twoPointFixedTimeCenterDiffKernel_local
        (d := d) G ((((s + s) : ℂ) * Complex.I)))
      hK₂_cont C_bd hK₂_bound_ae
  refine ⟨C_bd, 0, hC, ?_⟩
  intro ξ _hξ
  have hbase :
      ‖twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I))
          (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)‖ ≤ C_bd :=
    hK₂_bound ![(0 : SpacetimeDim d), ξ]
  rw [k2TimeParametricKernel_eq_twoPointFixedTimeCenterDiffKernel_on_zeroCenterSection_local
      (d := d) G (s + s) ξ]
  simpa using hbase

/-- If the common witness already depends only on the full diff block, then the
common-`G` root Input-A seam reduces to the strip bound alone: the reflected
product-shell pairing is automatic from the existing common-boundary support. -/
theorem exists_common_lifted_difference_slice_strip_bound_and_productShell_pairing_of_diffBlockDependence_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v)
    (s : ℝ)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
      ‖commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)‖ ≤
        C_bd * (1 + ‖z‖) ^ N) :
    ∃ (C_bd' : ℝ) (N' : ℕ),
      0 < C_bd' ∧
      (∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)‖ ≤
          C_bd' * (1 + ‖z‖) ^ N') ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) := by
  refine ⟨C_bd, N, hC, hK_bound, ?_⟩
  intro n
  exact
    commonLiftedDifferenceSlice_productShell_pairing_of_diffBlockDependence_local
      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n) G hG_diff s

/-- If the ordinary fixed-time kernel of a diff-block-dependent witness has the
usual continuity plus uniform a.e. constant bound, then the lifted common slice
already satisfies the strip-bound theorem surface used by the current frontier.

This isolates the remaining analytic Input A gap more sharply: after the
upstream translation-invariant witness is fixed, it is enough to prove the
standard fixed-time kernel const-bound package. -/
theorem exists_common_lifted_difference_slice_strip_bound_of_twoPointFixedTimeKernel_constBound_of_diffBlockDependence_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v)
    (s : ℝ)
    (C_bd : ℝ)
    (hC : 0 < C_bd)
    (hK_cont : Continuous
      (twoPointFixedTimeKernel (d := d) G ((((s + s) : ℂ) * Complex.I))))
    (hK_meas : AEStronglyMeasurable
      (twoPointFixedTimeKernel (d := d) G ((((s + s) : ℂ) * Complex.I))) volume)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeKernel (d := d) G ((((s + s) : ℂ) * Complex.I)) x‖ ≤ C_bd) :
    ∃ (C_bd' : ℝ) (N : ℕ),
      0 < C_bd' ∧
      ∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)‖ ≤
          C_bd' * (1 + ‖z‖) ^ N := by
  obtain ⟨hK₂_cont, _hK₂_meas, hK₂_bound_ae⟩ :=
    exists_constBound_package_twoPointFixedTimeCenterDiffKernel_local
      (d := d) G ((((s + s) : ℂ) * Complex.I)) hK_cont hK_meas C_bd hK_bound
  have hK₂_bound :
      ∀ z : NPointDomain d 2,
        ‖twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z‖ ≤ C_bd :=
    norm_le_of_continuous_ae_const_bound_local
      (d := d)
      (twoPointFixedTimeCenterDiffKernel_local
        (d := d) G ((((s + s) : ℂ) * Complex.I)))
      hK₂_cont C_bd hK₂_bound_ae
  refine ⟨C_bd, 0, hC, ?_⟩
  intro z _hz
  have hEq :=
    twoPointFixedTimeCenterDiffKernel_eq_commonLiftedDifferenceSlice_of_diffBlockDependence_local
      (d := d) G hG_diff s z
  simpa [hEq] using hK₂_bound z

/-- Bundled common-`G` package matching the current frontier surface once
diff-block dependence is available for the chosen witness. -/
theorem exists_common_lifted_difference_slice_productShell_package_of_diffBlockDependence_local
    (OS : OsterwalderSchraderAxioms d)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v)
    (s : ℝ)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
      ‖commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)‖ ≤
        C_bd * (1 + ‖z‖) ^ N) :
    ∃ (G' : (Fin (2 * (d + 1)) → ℂ) → ℂ) (C_bd' : ℝ) (N' : ℕ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G' ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G' (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      0 < C_bd' ∧
      (∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖commonLiftedDifferenceSliceKernel_local (d := d) G' s (z 1)‖ ≤
          C_bd' * (1 + ‖z‖) ^ N') ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G' ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.commonLiftedDifferenceSliceKernel_local (d := d) G' s (z 1) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) := by
  refine ⟨G, C_bd, N, hG_holo, hG_euclid, hC, hK_bound, ?_⟩
  intro n
  exact
    commonLiftedDifferenceSlice_productShell_pairing_of_diffBlockDependence_local
      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n) G hG_diff s

/-- Direct common-side packaging of the corrected Input-A route.

Once the chosen diff-block-dependent common witness carries a global
flat-tempered polynomial bound on the positive-time-difference tube, the whole
current common-`G` package follows automatically: the strip bound is provided by
`InputACommonBoundary`, and the reflected product-shell pairing is then derived
formally from diff-block dependence. -/
theorem exists_common_lifted_difference_slice_productShell_package_of_flat_tempered_global_and_diffBlockDependence_local
    (OS : OsterwalderSchraderAxioms d)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v)
    (s : ℝ)
    (C_bd : ℝ) (N : ℕ)
    (hC : 0 < C_bd)
    (hflat_bound :
      ∀ (x y : Fin (2 * (d + 1)) → ℝ),
        y ∈ FlatPositiveTimeDiffReal 2 d →
        ‖G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ≤
          C_bd * (1 + ‖x‖) ^ N) :
    ∃ (G' : (Fin (2 * (d + 1)) → ℂ) → ℂ) (C_bd' : ℝ) (N' : ℕ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G' ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G' (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      0 < C_bd' ∧
      (∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖commonLiftedDifferenceSliceKernel_local (d := d) G' s (z 1)‖ ≤
          C_bd' * (1 + ‖z‖) ^ N') ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G' ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.commonLiftedDifferenceSliceKernel_local (d := d) G' s (z 1) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) := by
  obtain ⟨C_bd', N', hC', hK_bound⟩ :=
    exists_common_lifted_difference_slice_strip_bound_of_flat_tempered_global_local
      (d := d) G s C_bd N hC hflat_bound
  exact
    exists_common_lifted_difference_slice_productShell_package_of_diffBlockDependence_local
      (d := d) OS φ_seq hφ_compact hφ_neg G hG_holo hG_euclid hG_diff s
      C_bd' N' hC' hK_bound

/-- If a diff-block-dependent witness has the standard fixed-time kernel
continuity/measurability/constant-bound package, then the full common-`G`
Input-A package used by the current frontier follows automatically. This is the
exact support theorem behind the corrected strip-bound seam: the remaining
analytic work can be paid at the ordinary fixed-time kernel level. -/
theorem exists_common_lifted_difference_slice_productShell_package_of_twoPointFixedTimeKernel_constBound_of_diffBlockDependence_local
    (OS : OsterwalderSchraderAxioms d)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v)
    (s : ℝ)
    (C_bd : ℝ)
    (hC : 0 < C_bd)
    (hK_cont : Continuous
      (twoPointFixedTimeKernel (d := d) G ((((s + s) : ℂ) * Complex.I))))
    (hK_meas : AEStronglyMeasurable
      (twoPointFixedTimeKernel (d := d) G ((((s + s) : ℂ) * Complex.I))) volume)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeKernel (d := d) G ((((s + s) : ℂ) * Complex.I)) x‖ ≤ C_bd) :
    ∃ (G' : (Fin (2 * (d + 1)) → ℂ) → ℂ) (C_bd' : ℝ) (N' : ℕ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G' ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G' (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      0 < C_bd' ∧
      (∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖commonLiftedDifferenceSliceKernel_local (d := d) G' s (z 1)‖ ≤
          C_bd' * (1 + ‖z‖) ^ N') ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G' ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.commonLiftedDifferenceSliceKernel_local (d := d) G' s (z 1) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) := by
  obtain ⟨C_bd', N', hC', hK_bound'⟩ :=
    exists_common_lifted_difference_slice_strip_bound_of_twoPointFixedTimeKernel_constBound_of_diffBlockDependence_local
      (d := d) G hG_diff s C_bd hC hK_cont hK_meas hK_bound
  exact
    exists_common_lifted_difference_slice_productShell_package_of_diffBlockDependence_local
      (d := d) OS φ_seq hφ_compact hφ_neg G hG_holo hG_euclid hG_diff s
      C_bd' N' hC' hK_bound'

/-- Equivalent packaging of the current common-`G` Input-A seam using the
ordinary `k = 2` time-parametric kernel on the concrete zero-center shifted
section. Once that real-section kernel is polynomially bounded, the whole
common lifted-slice package follows formally under diff-block dependence. -/
theorem exists_common_lifted_difference_slice_productShell_package_of_k2TimeParametricKernel_zeroCenterShift_bound_of_diffBlockDependence_local
    (OS : OsterwalderSchraderAxioms d)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v)
    (s : ℝ)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ ξ : SpacetimeDim d, -(s + s) < ξ 0 →
      ‖k2TimeParametricKernel (d := d) G
          ![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)]‖ ≤
        C_bd * (1 + ‖ξ‖) ^ N) :
    ∃ (G' : (Fin (2 * (d + 1)) → ℂ) → ℂ) (C_bd' : ℝ) (N' : ℕ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G' ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G' (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      0 < C_bd' ∧
      (∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖commonLiftedDifferenceSliceKernel_local (d := d) G' s (z 1)‖ ≤
          C_bd' * (1 + ‖z‖) ^ N') ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G' ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.commonLiftedDifferenceSliceKernel_local (d := d) G' s (z 1) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) := by
  obtain ⟨C_bd', N', hC', hK_bound'⟩ :=
    exists_common_lifted_difference_slice_strip_bound_of_k2TimeParametricKernel_zeroCenterShift_bound_of_diffBlockDependence_local
      (d := d) G hG_diff s C_bd N hC hK_bound
  exact
    exists_common_lifted_difference_slice_productShell_package_of_diffBlockDependence_local
      (d := d) OS φ_seq hφ_compact hφ_neg G hG_holo hG_euclid hG_diff s
      C_bd' N' hC' hK_bound'

/-- Repackage the current diff-block fallback at the upstream `ACR(1)` witness
surface: if the configuration-space witness `S₁` is invariant under common
complex translations of both points, then the current common-`G` root seam
reduces to the strip bound alone. -/
theorem exists_common_lifted_difference_slice_strip_bound_and_productShell_pairing_of_fromDiffFlat_translationInvariant_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (S₁ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hS₁_trans :
      ∀ (z : Fin 2 → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S₁ (fun i => z i + a) = S₁ z)
    (s : ℝ)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
      ‖commonLiftedDifferenceSliceKernel_local
          (d := d) (fun u => S₁ (BHW.fromDiffFlat 2 d u)) s (z 1)‖ ≤
        C_bd * (1 + ‖z‖) ^ N) :
    ∃ (C_bd' : ℝ) (N' : ℕ),
      0 < C_bd' ∧
      (∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖commonLiftedDifferenceSliceKernel_local
            (d := d) (fun u => S₁ (BHW.fromDiffFlat 2 d u)) s (z 1)‖ ≤
          C_bd' * (1 + ‖z‖) ^ N') ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) (fun u => S₁ (BHW.fromDiffFlat 2 d u))
            ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.commonLiftedDifferenceSliceKernel_local
            (d := d) (fun u => S₁ (BHW.fromDiffFlat 2 d u)) s (z 1) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) := by
  let G : (Fin (2 * (d + 1)) → ℂ) → ℂ := fun u => S₁ (BHW.fromDiffFlat 2 d u)
  have hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v := by
    simpa [G] using
      (diffBlockDependence_of_fromDiffFlat_translationInvariant_local
        (d := d) S₁ hS₁_trans)
  refine
    exists_common_lifted_difference_slice_strip_bound_and_productShell_pairing_of_diffBlockDependence_local
      (d := d) φ_seq hφ_compact hφ_neg G hG_diff s C_bd N hC ?_
  simpa [G] using hK_bound

/-- Fixed imaginary-time shift used to move the zero-anchor Euclidean section
strictly into `ACR(1)` without changing the common witness value. -/
private def unitImagTimeShift_local : Fin (d + 1) → ℂ :=
  fun μ => if μ = 0 then Complex.I else 0

/-- The zero-anchor Euclidean section translated by a common imaginary time
shift. This is the interior configuration on which the upstream `ACR(1)` growth
bound is applied. -/
private def zeroAnchorSectionShiftedToAcr_local
    (ξ : SpacetimeDim d) : Fin 2 → Fin (d + 1) → ℂ :=
  fun i => wickRotatePoint (![(0 : SpacetimeDim d), ξ] i) + unitImagTimeShift_local (d := d)

private theorem wickRotatePoint_component_norm_eq_local
    (x : SpacetimeDim d) (μ : Fin (d + 1)) :
    ‖wickRotatePoint x μ‖ = ‖x μ‖ := by
  by_cases hμ : μ = 0
  · subst hμ
    rw [wickRotatePoint, if_pos rfl, Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
  · rw [wickRotatePoint, if_neg hμ, Complex.norm_real]

private theorem wickRotatePoint_zero_local :
    wickRotatePoint (0 : SpacetimeDim d) = 0 := by
  ext μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [wickRotatePoint]
  · simp [wickRotatePoint, hμ]

private theorem norm_wickRotatePoint_le_local
    (ξ : SpacetimeDim d) :
    ‖wickRotatePoint ξ‖ ≤ ‖ξ‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg ξ)]
  intro μ
  rw [wickRotatePoint_component_norm_eq_local (d := d)]
  exact norm_le_pi_norm ξ μ

private theorem norm_unitImagTimeShift_le_local :
    ‖unitImagTimeShift_local (d := d)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 1)]
  intro μ
  by_cases hμ0 : μ = 0
  · subst hμ0
    simp [unitImagTimeShift_local]
  · simp [unitImagTimeShift_local, hμ0]

private theorem zeroAnchorSectionShiftedToAcr_mem_local
    (ξ : SpacetimeDim d) (hξ : 0 < ξ 0) :
    zeroAnchorSectionShiftedToAcr_local (d := d) ξ ∈
      AnalyticContinuationRegion d 2 1 := by
  simp only [AnalyticContinuationRegion, Set.mem_setOf_eq]
  intro i μ hμ
  have hμ0 : μ = 0 := Fin.ext (Nat.eq_zero_of_le_zero hμ)
  subst hμ0
  fin_cases i
  · simp [zeroAnchorSectionShiftedToAcr_local, unitImagTimeShift_local, wickRotatePoint]
  · simp [zeroAnchorSectionShiftedToAcr_local, unitImagTimeShift_local, wickRotatePoint]
    simpa using hξ

private theorem norm_zeroAnchorSectionShiftedToAcr_le_local
    (ξ : SpacetimeDim d) :
    ‖zeroAnchorSectionShiftedToAcr_local (d := d) ξ‖ ≤ 1 + ‖ξ‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖)]
  intro i
  fin_cases i
  ·
    calc
      ‖zeroAnchorSectionShiftedToAcr_local (d := d) ξ 0‖
          = ‖unitImagTimeShift_local (d := d)‖ := by
              simp [zeroAnchorSectionShiftedToAcr_local, wickRotatePoint_zero_local]
      _ ≤ 1 := norm_unitImagTimeShift_le_local (d := d)
      _ ≤ 1 + ‖ξ‖ := by nlinarith [norm_nonneg ξ]
  ·
    calc
      ‖zeroAnchorSectionShiftedToAcr_local (d := d) ξ 1‖
          = ‖wickRotatePoint ξ + unitImagTimeShift_local (d := d)‖ := by
              simp [zeroAnchorSectionShiftedToAcr_local]
      _ ≤ ‖wickRotatePoint ξ‖ + ‖unitImagTimeShift_local (d := d)‖ := norm_add_le _ _
      _ ≤ ‖ξ‖ + 1 := by
            nlinarith [norm_wickRotatePoint_le_local (d := d) ξ,
              norm_unitImagTimeShift_le_local (d := d)]
      _ = 1 + ‖ξ‖ := by ring

theorem schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      (∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v) ∧
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ ξ : SpacetimeDim d, 0 < ξ 0 →
          ‖k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)‖ ≤
            C_bd * (1 + ‖ξ‖) ^ N := by
  let hS_pack :=
    _root_.schwinger_continuation_base_step_acrOne_assembly_with_translationInvariant
      (d := d) OS lgc 2
  let S₁ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ := Classical.choose hS_pack
  have hS₁_hol :
      DifferentiableOn ℂ S₁ (AnalyticContinuationRegion d 2 1) :=
    (Classical.choose_spec hS_pack).1
  have hS₁_euclid :
      ∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          S₁ (fun j => wickRotatePoint (x j)) * (f.1 x) :=
    (Classical.choose_spec hS_pack).2.1
  have hS₁_trans :
      ∀ (z : Fin 2 → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S₁ (fun j => z j + a) = S₁ z :=
    (Classical.choose_spec hS_pack).2.2.2.1
  obtain ⟨C₁, N, hC₁, hS₁_growth⟩ :=
    (Classical.choose_spec hS_pack).2.2.2.2
  let G : (Fin (2 * (d + 1)) → ℂ) → ℂ := fun u => S₁ (BHW.fromDiffFlat 2 d u)
  have hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G := by
    refine ⟨?_, ?_⟩
    · intro u hu
      have hfrom_maps :
          Set.MapsTo (BHW.fromDiffFlat 2 d)
            (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d))
            (AnalyticContinuationRegion d 2 1) := by
        intro v hv
        rw [acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff]
        simpa [BHW.toDiffFlat_fromDiffFlat] using hv
      have hS₁_cont : ContinuousOn S₁ (AnalyticContinuationRegion d 2 1) :=
        hS₁_hol.continuousOn
      have hG_cont : ContinuousOn G (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d)) :=
        hS₁_cont.comp (differentiable_fromDiffFlat_local 2 d).continuous.continuousOn hfrom_maps
      exact hG_cont u hu
    · intro z hz i
      let idx : Fin (2 * (d + 1)) := finProdFinEquiv (i, (0 : Fin (d + 1)))
      let φ : ℂ → (Fin 2 → Fin (d + 1) → ℂ) := fun w =>
        BHW.fromDiffFlat 2 d (Function.update z idx w)
      have hupdate_diff : Differentiable ℂ (fun w : ℂ => Function.update z idx w) := by
        rw [differentiable_pi]
        intro j
        by_cases hj : j = idx
        · subst hj
          simpa using differentiable_id
        · simpa [Function.update, hj] using differentiable_const (z j)
      have hφ_maps :
          Set.MapsTo φ {w : ℂ | 0 < w.im} (AnalyticContinuationRegion d 2 1) := by
        intro w hw
        rw [acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff]
        rw [BHW.toDiffFlat_fromDiffFlat]
        rw [mem_tubeDomain_flatPositiveTimeDiffReal_iff]
        intro j
        by_cases hj : j = i
        · subst hj
          simpa [φ, idx]
        · have hzj :=
            (mem_tubeDomain_flatPositiveTimeDiffReal_iff (z := z)).mp hz j
          simpa [φ, idx, Function.update, hj] using hzj
      simpa [G, φ, idx] using
        (hS₁_hol.comp
          ((differentiable_fromDiffFlat_local 2 d).comp hupdate_diff).differentiableOn
          hφ_maps)
  have hG_euclid :
      ∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x) := by
    intro f
    simpa [G, BHW.fromDiffFlat_toDiffFlat] using hS₁_euclid f
  have hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v := by
    simpa [G] using
      (diffBlockDependence_of_fromDiffFlat_translationInvariant_local
        (d := d) S₁ hS₁_trans)
  refine ⟨G, hG_holo, hG_euclid, hG_diff, C₁ * (2 : ℝ) ^ N, N, ?_, ?_⟩
  · positivity
  · intro ξ hξ
    let zShifted : Fin 2 → Fin (d + 1) → ℂ := zeroAnchorSectionShiftedToAcr_local (d := d) ξ
    have hz_mem : zShifted ∈ AnalyticContinuationRegion d 2 1 :=
      zeroAnchorSectionShiftedToAcr_mem_local (d := d) ξ hξ
    have hz_norm : ‖zShifted‖ ≤ 1 + ‖ξ‖ :=
      norm_zeroAnchorSectionShiftedToAcr_le_local (d := d) ξ
    have htrans_eq :
        k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2) = S₁ zShifted := by
      calc
        k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)
            = S₁ (fun i => wickRotatePoint (![(0 : SpacetimeDim d), ξ] i)) := by
                simp [G, k2TimeParametricKernel, BHW.fromDiffFlat_toDiffFlat]
        _ = S₁ zShifted := by
            symm
            simpa [zShifted, zeroAnchorSectionShiftedToAcr_local, unitImagTimeShift_local] using
              hS₁_trans
                (fun i => wickRotatePoint (![(0 : SpacetimeDim d), ξ] i))
                (unitImagTimeShift_local (d := d))
    have hbound0 : ‖S₁ zShifted‖ ≤ C₁ * (1 + ‖zShifted‖) ^ N :=
      hS₁_growth zShifted hz_mem
    calc
      ‖k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)‖
          = ‖S₁ zShifted‖ := by rw [htrans_eq]
      _ ≤ C₁ * (1 + ‖zShifted‖) ^ N := hbound0
      _ ≤ C₁ * (1 + (1 + ‖ξ‖)) ^ N := by
            gcongr
      _ = C₁ * (2 + ‖ξ‖) ^ N := by ring
      _ ≤ C₁ * ((2 : ℝ) * (1 + ‖ξ‖)) ^ N := by
            apply mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₁)
            exact pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg ξ]) N
      _ = (C₁ * (2 : ℝ) ^ N) * (1 + ‖ξ‖) ^ N := by
            rw [mul_assoc, mul_pow]
      _ = (C₁ * (2 : ℝ) ^ N) * (1 + ‖ξ‖) ^ N := rfl

/-- Stable `k = 2` common-witness package together with the upstream E3 swap
symmetry transported to the raw Euclidean section.

This companion theorem keeps the older pos-section-bound surface intact while
exposing one genuinely new fact needed only by the final DuBois endgame:
the chosen common witness is pointwise invariant under swapping the two raw
Euclidean arguments. -/
theorem schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_and_swapEq_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      (∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v) ∧
      (∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ ξ : SpacetimeDim d, 0 < ξ 0 →
          ‖k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)‖ ≤
            C_bd * (1 + ‖ξ‖) ^ N) ∧
      (∀ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G
          (fun i => x ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) i)) =
        k2TimeParametricKernel (d := d) G x) := by
  let hS_pack :=
    _root_.schwinger_continuation_base_step_acrOne_assembly_with_translationInvariant
      (d := d) OS lgc 2
  let S₁ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ := Classical.choose hS_pack
  have hS₁_hol :
      DifferentiableOn ℂ S₁ (AnalyticContinuationRegion d 2 1) :=
    (Classical.choose_spec hS_pack).1
  have hS₁_euclid :
      ∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          S₁ (fun j => wickRotatePoint (x j)) * (f.1 x) :=
    (Classical.choose_spec hS_pack).2.1
  have hS₁_perm :
      ∀ (σ : Equiv.Perm (Fin 2)) (z : Fin 2 → Fin (d + 1) → ℂ),
        S₁ (fun j => z (σ j)) = S₁ z :=
    (Classical.choose_spec hS_pack).2.2.1
  have hS₁_trans :
      ∀ (z : Fin 2 → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S₁ (fun j => z j + a) = S₁ z :=
    (Classical.choose_spec hS_pack).2.2.2.1
  obtain ⟨C₁, N, hC₁, hS₁_growth⟩ :=
    (Classical.choose_spec hS_pack).2.2.2.2
  let G : (Fin (2 * (d + 1)) → ℂ) → ℂ := fun u => S₁ (BHW.fromDiffFlat 2 d u)
  have hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G := by
    refine ⟨?_, ?_⟩
    · intro u hu
      have hfrom_maps :
          Set.MapsTo (BHW.fromDiffFlat 2 d)
            (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d))
            (AnalyticContinuationRegion d 2 1) := by
        intro v hv
        rw [acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff]
        simpa [BHW.toDiffFlat_fromDiffFlat] using hv
      have hS₁_cont : ContinuousOn S₁ (AnalyticContinuationRegion d 2 1) :=
        hS₁_hol.continuousOn
      have hG_cont : ContinuousOn G (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d)) :=
        hS₁_cont.comp (differentiable_fromDiffFlat_local 2 d).continuous.continuousOn hfrom_maps
      exact hG_cont u hu
    · intro z hz i
      let idx : Fin (2 * (d + 1)) := finProdFinEquiv (i, (0 : Fin (d + 1)))
      let φ : ℂ → (Fin 2 → Fin (d + 1) → ℂ) := fun w =>
        BHW.fromDiffFlat 2 d (Function.update z idx w)
      have hupdate_diff : Differentiable ℂ (fun w : ℂ => Function.update z idx w) := by
        rw [differentiable_pi]
        intro j
        by_cases hj : j = idx
        · subst hj
          simpa using differentiable_id
        · simpa [Function.update, hj] using differentiable_const (z j)
      have hφ_maps :
          Set.MapsTo φ {w : ℂ | 0 < w.im} (AnalyticContinuationRegion d 2 1) := by
        intro w hw
        rw [acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff]
        rw [BHW.toDiffFlat_fromDiffFlat]
        rw [mem_tubeDomain_flatPositiveTimeDiffReal_iff]
        intro j
        by_cases hj : j = i
        · subst hj
          simpa [φ, idx]
        · have hzj :=
            (mem_tubeDomain_flatPositiveTimeDiffReal_iff (z := z)).mp hz j
          simpa [φ, idx, Function.update, hj] using hzj
      simpa [G, φ, idx] using
        (hS₁_hol.comp
          ((differentiable_fromDiffFlat_local 2 d).comp hupdate_diff).differentiableOn
          hφ_maps)
  have hG_euclid :
      ∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x) := by
    intro f
    simpa [G, BHW.fromDiffFlat_toDiffFlat] using hS₁_euclid f
  have hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v := by
    simpa [G] using
      (diffBlockDependence_of_fromDiffFlat_translationInvariant_local
        (d := d) S₁ hS₁_trans)
  have hG_bound :
      ∀ ξ : SpacetimeDim d, 0 < ξ 0 →
        ‖k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)‖ ≤
          (C₁ * (2 : ℝ) ^ N) * (1 + ‖ξ‖) ^ N := by
    intro ξ hξ
    let zShifted : Fin 2 → Fin (d + 1) → ℂ := zeroAnchorSectionShiftedToAcr_local (d := d) ξ
    have hz_mem : zShifted ∈ AnalyticContinuationRegion d 2 1 :=
      zeroAnchorSectionShiftedToAcr_mem_local (d := d) ξ hξ
    have hz_norm : ‖zShifted‖ ≤ 1 + ‖ξ‖ :=
      norm_zeroAnchorSectionShiftedToAcr_le_local (d := d) ξ
    have htrans_eq :
        k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2) = S₁ zShifted := by
      calc
        k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)
            = S₁ (fun i => wickRotatePoint (![(0 : SpacetimeDim d), ξ] i)) := by
                simp [G, k2TimeParametricKernel, BHW.fromDiffFlat_toDiffFlat]
        _ = S₁ zShifted := by
            symm
            simpa [zShifted, zeroAnchorSectionShiftedToAcr_local, unitImagTimeShift_local] using
              hS₁_trans
                (fun i => wickRotatePoint (![(0 : SpacetimeDim d), ξ] i))
                (unitImagTimeShift_local (d := d))
    have hbound0 : ‖S₁ zShifted‖ ≤ C₁ * (1 + ‖zShifted‖) ^ N :=
      hS₁_growth zShifted hz_mem
    calc
      ‖k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)‖
          = ‖S₁ zShifted‖ := by rw [htrans_eq]
      _ ≤ C₁ * (1 + ‖zShifted‖) ^ N := hbound0
      _ ≤ C₁ * (1 + (1 + ‖ξ‖)) ^ N := by
            gcongr
      _ = C₁ * (2 + ‖ξ‖) ^ N := by ring
      _ ≤ C₁ * ((2 : ℝ) * (1 + ‖ξ‖)) ^ N := by
            apply mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₁)
            exact pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg ξ]) N
      _ = (C₁ * (2 : ℝ) ^ N) * (1 + ‖ξ‖) ^ N := by
            rw [mul_assoc, mul_pow]
      _ = (C₁ * (2 : ℝ) ^ N) * (1 + ‖ξ‖) ^ N := rfl
  have hswap_eq :
      ∀ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G
          (fun i => x ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) i)) =
        k2TimeParametricKernel (d := d) G x := by
    intro x
    calc
      k2TimeParametricKernel (d := d) G
          (fun i => x ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) i))
          = S₁ (fun j =>
              wickRotatePoint ((fun i => x ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) i)) j)) := by
                simp [G, k2TimeParametricKernel, BHW.fromDiffFlat_toDiffFlat]
      _ = S₁ (fun j => wickRotatePoint (x ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) j))) := by rfl
      _ = S₁ (fun j => wickRotatePoint (x j)) := by
            simpa using
              (hS₁_perm (Equiv.swap (0 : Fin 2) (1 : Fin 2))
                (fun j => wickRotatePoint (x j)))
      _ = k2TimeParametricKernel (d := d) G x := by
            simp [G, k2TimeParametricKernel, BHW.fromDiffFlat_toDiffFlat]
  refine ⟨G, hG_holo, hG_euclid, hG_diff, ⟨C₁ * (2 : ℝ) ^ N, N, ?_, hG_bound⟩, hswap_eq⟩
  positivity

/-- Exact `k = 2` payoff of the strengthened upstream `ACR(1)` witness surface.

This is the older interface used downstream: witness, Euclidean reproduction,
and diff-block dependence. It is now obtained by forgetting the additional
positive-time section bound proved above. -/
theorem schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      (∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (diffSlot_local (d := d) μ) = v (diffSlot_local (d := d) μ)) →
        G u = G v) := by
  obtain ⟨G, hG_holo, hG_euclid, hG_diff, _hG_bound⟩ :=
    schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
      (d := d) OS lgc
  exact ⟨G, hG_holo, hG_euclid, hG_diff⟩

end OSReconstruction
