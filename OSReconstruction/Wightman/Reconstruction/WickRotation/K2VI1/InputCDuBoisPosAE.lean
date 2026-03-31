import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCDuBoisAE
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputADiffBlock
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCSwapSymmetry

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- If `K` is continuous and polynomially bounded on a measurable region `U`,
then it is integrable against any Schwartz test supported in `U`. This is the
support-restricted integrability input needed by the final DuBois route. -/
private theorem integrable_mul_schwartz_of_continuousOn_bound_on_support_local
    (K : NPointDomain d 2 → ℂ)
    (U : Set (NPointDomain d 2))
    (hU_meas : MeasurableSet U)
    (hK_cont : ContinuousOn K U)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ x ∈ U, ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (f : SchwartzNPoint d 2)
    (hf_supp : Function.support (f : NPointDomain d 2 → ℂ) ⊆ U) :
    Integrable (fun x => K x * f x) volume := by
  let K' : NPointDomain d 2 → ℂ := Set.indicator U K
  have hK'_eq : ∀ x, K' x * f x = K x * f x := by
    intro x
    by_cases hx : x ∈ U
    · simp [K', hx]
    · have hfx : (f : NPointDomain d 2 → ℂ) x = 0 := by
        by_contra h
        exact hx (hf_supp (Function.mem_support.mpr h))
      simp [K', hx, hfx]
  have hK'_bound : ∀ᵐ x ∂volume, ‖K' x‖ ≤ C_bd * (1 + ‖x‖) ^ N := by
    filter_upwards with x
    by_cases hx : x ∈ U
    · simpa [K', hx] using hK_bound x hx
    · simp [K', hx]
      positivity
  have hK'_meas : AEStronglyMeasurable K' volume := by
    rw [aestronglyMeasurable_indicator_iff hU_meas]
    exact hK_cont.aestronglyMeasurable hU_meas
  have hint :=
    schwartz_polynomial_kernel_integrable K' hK'_meas C_bd N hC hK'_bound f
  rwa [show (fun x => K' x * f x) = (fun x => K x * f x) from funext hK'_eq] at hint

/-- DuBois-Reymond closure on the positive sector from sector-local continuity
and polynomial bounds for the raw Euclidean witness kernel and its swapped
counterpart. This packages the full endgame once the common witness admits the
needed raw/swap positive-sector package. -/
theorem swapDelta_ae_eq_zero_on_posTimeSector_of_posSectorPackages_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G x * (f.1 x))
    (hG_cont : ContinuousOn
      (fun x : NPointDomain d 2 => k2TimeParametricKernel (d := d) G x)
      (posTimeSector_local (d := d)))
    (hG_swap_cont : ContinuousOn
      (fun x : NPointDomain d 2 =>
        k2TimeParametricKernel (d := d) G
          (swapTwoPointAssembly_local (d := d) x))
      (posTimeSector_local (d := d)))
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ x ∈ posTimeSector_local (d := d),
      ‖k2TimeParametricKernel (d := d) G x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hK_swap_bound : ∀ x ∈ posTimeSector_local (d := d),
      ‖k2TimeParametricKernel (d := d) G
          (swapTwoPointAssembly_local (d := d) x)‖ ≤
        C_bd * (1 + ‖x‖) ^ N) :
    ∀ᵐ x : NPointDomain d 2 ∂volume,
      x ∈ posTimeSector_local (d := d) →
        swapDelta_local (d := d) G x = 0 := by
  have hΔ_loc : LocallyIntegrableOn (swapDelta_local (d := d) G)
      (posTimeSector_local (d := d)) volume := by
    show LocallyIntegrableOn
      (fun x =>
        k2TimeParametricKernel (d := d) G x -
          k2TimeParametricKernel (d := d) G
            (swapTwoPointAssembly_local (d := d) x))
      (posTimeSector_local (d := d)) volume
    exact (hG_cont.sub hG_swap_cont).locallyIntegrableOn
      (isOpen_posTimeSector_local (d := d)).measurableSet
  exact
    ae_eq_zero_on_posTimeSector_of_zeroDiagonal_pairing_eq_zero_local
      (d := d) (swapDelta_local (d := d) G) hΔ_loc
      (fun f hf_supp => by
        have hU_meas := (isOpen_posTimeSector_local (d := d)).measurableSet
        have hf_supp' : Function.support (f.1 : NPointDomain d 2 → ℂ) ⊆
            posTimeSector_local (d := d) :=
          Function.support_subset_iff'.mpr fun x hx => by
            by_contra h
            exact hx (hf_supp (Function.mem_support.mpr h))
        have hIntA :
            Integrable
              (fun x =>
                k2TimeParametricKernel (d := d) G x * (f.1 x)) :=
          integrable_mul_schwartz_of_continuousOn_bound_on_support_local
            (d := d)
            (fun x => k2TimeParametricKernel (d := d) G x)
            (posTimeSector_local (d := d)) hU_meas hG_cont C_bd N hC hK_bound
            f.1 hf_supp'
        have hIntB :
            Integrable
              (fun x =>
                k2TimeParametricKernel (d := d) G
                  (swapTwoPointAssembly_local (d := d) x) * (f.1 x)) :=
          integrable_mul_schwartz_of_continuousOn_bound_on_support_local
            (d := d)
            (fun x =>
              k2TimeParametricKernel (d := d) G
                (swapTwoPointAssembly_local (d := d) x))
            (posTimeSector_local (d := d)) hU_meas hG_swap_cont C_bd N hC
            hK_swap_bound f.1 hf_supp'
        show ∫ x, swapDelta_local (d := d) G x * (f.1 x) = 0
        show
          ∫ x,
            (k2TimeParametricKernel (d := d) G x -
              k2TimeParametricKernel (d := d) G
                (swapTwoPointAssembly_local (d := d) x)) * (f.1 x) = 0
        simp only [sub_mul]
        rw [integral_sub hIntA hIntB, sub_eq_zero]
        exact
          k2TimeParametricKernel_integral_eq_swap_integral_local
            (d := d) OS G hG_euclid f)

/-- Honest final positive-sector package for the common `k = 2` witness used
in the DuBois endgame.

Instead of trying to retrofit extra properties onto an arbitrary
`Classical.choose` witness, we package an explicit common witness built from the
upstream translation-invariant `ACR(1)` theorem. The only genuinely new input
needed beyond the stable Input-A package is the pointwise E3 swap symmetry of
the raw Euclidean section, which immediately implies `swapDelta = 0` on the
positive sector. -/
theorem exists_commonDiffWitness_swapDelta_ae_zero_on_pos_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G x * (f.1 x)) ∧
      (∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (finProdFinEquiv (⟨1, by omega⟩, μ)) =
            v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
        G u = G v) ∧
      (∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ ξ : SpacetimeDim d, 0 < ξ 0 →
          ‖k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)‖ ≤
            C_bd * (1 + ‖ξ‖) ^ N) ∧
      (∀ᵐ x : NPointDomain d 2 ∂volume,
        x ∈ posTimeSector_local (d := d) →
          swapDelta_local (d := d) G x = 0) := by
  obtain ⟨G, hG_holo, hG_euclid, hG_diff, hG_bound, hswap_eq⟩ :=
    schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_and_swapEq_local
      (d := d) OS lgc
  refine ⟨G, hG_holo, ?_, hG_diff, hG_bound, ?_⟩
  · intro f
    simpa [k2TimeParametricKernel] using hG_euclid f
  · filter_upwards with x hx
    have hswap :
        k2TimeParametricKernel (d := d) G (swapTwoPointAssembly_local (d := d) x) =
          k2TimeParametricKernel (d := d) G x := by
      simpa [swapTwoPointAssembly_local] using hswap_eq x
    rw [swapDelta_local, hswap, sub_self]

end OSReconstruction
