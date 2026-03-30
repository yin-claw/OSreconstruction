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

/-- Exact `k = 2` payoff of the strengthened upstream `ACR(1)` witness surface.

If the chosen `ACR(1)` witness is exported together with common complex
translation invariance, then the corresponding flattened time-parametric
witness already satisfies the global diff-block dependence needed by the
current common-boundary fallback. -/
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
  obtain ⟨S₁, hS₁_hol, hS₁_euclid, hS₁_trans⟩ :=
    _root_.schwinger_continuation_base_step_acrOne_assembly_with_translationInvariant
      (d := d) OS lgc 2
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
  exact ⟨G, hG_holo, hG_euclid, hG_diff⟩

end OSReconstruction
