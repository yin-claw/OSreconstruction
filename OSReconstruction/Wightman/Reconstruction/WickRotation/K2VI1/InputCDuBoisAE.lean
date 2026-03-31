import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCDuBoisFinal

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

private def twoPointSwapMeasurableEquiv_ae_local :
    NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Fin 2 => SpacetimeDim d)
    (Equiv.swap (0 : Fin 2) (1 : Fin 2))

private theorem twoPointSwapMeasurableEquiv_ae_eq_local :
    ((twoPointSwapMeasurableEquiv_ae_local (d := d)) :
      NPointDomain d 2 → NPointDomain d 2) =
        swapTwoPointAssembly_local (d := d) := by
  funext x
  let x' :
      (a : Fin 2) →
        (fun _ : Fin 2 => SpacetimeDim d) ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) a) := x
  funext i
  fin_cases i
  · simpa [twoPointSwapMeasurableEquiv_ae_local, swapTwoPointAssembly_local] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (e := Equiv.swap (0 : Fin 2) (1 : Fin 2))
        (β := fun _ : Fin 2 => SpacetimeDim d)
        (x := x') (i := (1 : Fin 2)))
  · simpa [twoPointSwapMeasurableEquiv_ae_local, swapTwoPointAssembly_local] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (e := Equiv.swap (0 : Fin 2) (1 : Fin 2))
        (β := fun _ : Fin 2 => SpacetimeDim d)
        (x := x') (i := (0 : Fin 2)))

/-- Swapping the two Euclidean arguments flips the sign of the raw swap
difference `swapDelta_local`. -/
theorem swapDelta_swap_eq_neg_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (x : NPointDomain d 2) :
    swapDelta_local (d := d) G (swapTwoPointAssembly_local (d := d) x) =
      -swapDelta_local (d := d) G x := by
  have hswap :
      swapTwoPointAssembly_local (d := d)
          (swapTwoPointAssembly_local (d := d) x) = x := by
    ext i
    fin_cases i <;> simp [swapTwoPointAssembly_local]
  simp [swapDelta_local, hswap, sub_eq_add_neg, add_comm]

/-- The equal-time hyperplane `{x | x 0 0 = x 1 0}` has Lebesgue measure zero. -/
theorem ae_twoPoint_ne_time_local :
    ∀ᵐ (x : NPointDomain d 2) ∂(volume : Measure (NPointDomain d 2)),
      x 0 0 ≠ x 1 0 := by
  let L : NPointDomain d 2 →ₗ[ℝ] ℝ :=
    { toFun := fun x => x 0 0 - x 1 0
      map_add' := by
        intro x y
        simp
        ring
      map_smul' := by
        intro a x
        simp
        ring }
  have hset :
      {x : NPointDomain d 2 | x 0 0 = x 1 0} = (LinearMap.ker L : Set (NPointDomain d 2)) := by
    ext x
    simp [L, LinearMap.mem_ker, sub_eq_zero]
  have hker_ne_top : LinearMap.ker L ≠ ⊤ := by
    intro htop
    have hzero : L = 0 := LinearMap.ker_eq_top.mp htop
    have hval : L (fun k μ => if k = (0 : Fin 2) ∧ μ = 0 then (1 : ℝ) else 0) = 0 := by
      simpa using congrArg
        (fun f => f (fun k μ => if k = (0 : Fin 2) ∧ μ = 0 then (1 : ℝ) else 0)) hzero
    have : (1 : ℝ) = 0 := by
      simp [L] at hval
    norm_num at this
  have hs0 :
      MeasureTheory.volume {x : NPointDomain d 2 | x 0 0 = x 1 0} = 0 := by
    rw [hset]
    exact
      MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume (LinearMap.ker L) hker_ne_top
  exact
    Filter.mem_of_superset
      (MeasureTheory.compl_mem_ae_iff.mpr hs0)
      (by
        intro x hx
        simpa [Set.mem_setOf_eq, Set.compl_setOf] using hx)

/-- If the raw swap difference vanishes a.e. on the positive time-ordering
sector, then it also vanishes a.e. on the negative sector by swap symmetry. -/
theorem swapDelta_ae_eq_zero_on_negTimeSector_of_pos_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hΔ_pos : ∀ᵐ x : NPointDomain d 2 ∂volume,
      x ∈ posTimeSector_local (d := d) →
        swapDelta_local (d := d) G x = 0) :
    ∀ᵐ x : NPointDomain d 2 ∂volume,
      x ∈ negTimeSector_local (d := d) →
        swapDelta_local (d := d) G x = 0 := by
  let e := twoPointSwapMeasurableEquiv_ae_local (d := d)
  have he : MeasureTheory.MeasurePreserving e volume volume := by
    simpa [e, twoPointSwapMeasurableEquiv_ae_local] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Fin 2 => SpacetimeDim d)
        (Equiv.swap (0 : Fin 2) (1 : Fin 2)))
  have hswap :
      ∀ᵐ x : NPointDomain d 2 ∂volume,
        swapTwoPointAssembly_local (d := d) x ∈ posTimeSector_local (d := d) →
          swapDelta_local (d := d) G
            (swapTwoPointAssembly_local (d := d) x) = 0 := by
    simpa [e, twoPointSwapMeasurableEquiv_ae_eq_local (d := d)] using
      (he.quasiMeasurePreserving.tendsto_ae.eventually hΔ_pos)
  filter_upwards [hswap] with x hxswap hxneg
  have hswap_pos :
      swapTwoPointAssembly_local (d := d) x ∈ posTimeSector_local (d := d) := by
    simpa [negTimeSector_local, posTimeSector_local, swapTwoPointAssembly_local] using hxneg
  have hswap_zero := hxswap hswap_pos
  have hanti := swapDelta_swap_eq_neg_local (d := d) G x
  rw [hanti] at hswap_zero
  simpa using hswap_zero

/-- Once the raw swap difference vanishes a.e. on the positive sector, the
common sectorwise kernel agrees a.e. with the raw Euclidean kernel. -/
theorem commonK2TimeParametricKernel_real_ae_eq_k2TimeParametricKernel_of_swapDelta_ae_zero_on_pos_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) =
          v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (hΔ_pos : ∀ᵐ x : NPointDomain d 2 ∂volume,
      x ∈ posTimeSector_local (d := d) →
        swapDelta_local (d := d) G x = 0) :
    ∀ᵐ x : NPointDomain d 2 ∂volume,
      commonK2TimeParametricKernel_real_local (d := d) G x =
        k2TimeParametricKernel (d := d) G x := by
  have hΔ_neg :=
    swapDelta_ae_eq_zero_on_negTimeSector_of_pos_local (d := d) G hΔ_pos
  filter_upwards [hΔ_pos, hΔ_neg, ae_twoPoint_ne_time_local (d := d)] with x hxpos hxneg hne
  rcases lt_or_gt_of_ne hne with hpos | hneg
  · exact commonK2TimeParametricKernel_real_eq_of_pos_local (d := d) G hG_diff x hpos
  · have hΔ_zero := hxneg hneg
    have hk2eq :
        k2TimeParametricKernel (d := d) G x =
          k2TimeParametricKernel (d := d) G (swapTwoPointAssembly_local (d := d) x) := by
      have hdef :
          swapDelta_local (d := d) G x =
            k2TimeParametricKernel (d := d) G x -
              k2TimeParametricKernel (d := d) G (swapTwoPointAssembly_local (d := d) x) := rfl
      rwa [hΔ_zero, eq_comm, sub_eq_zero] at hdef
    rw [commonK2TimeParametricKernel_real_eq_of_neg_local (d := d) G hG_diff x hneg]
    exact hk2eq.symm

/-- Shell-level Schwinger reproduction from the a.e. positive-sector vanishing
of the raw swap difference. This isolates the final production endgame from the
remaining analytic `swapDelta` input. -/
theorem commonK2TimeParametricKernel_real_eq_schwinger_of_swapDelta_ae_zero_on_pos_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G x * (f.1 x))
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) =
          v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (hΔ_pos : ∀ᵐ x : NPointDomain d 2 ∂volume,
      x ∈ posTimeSector_local (d := d) →
        swapDelta_local (d := d) G x = 0)
    (f : ZeroDiagonalSchwartz d 2) :
    ∫ x : NPointDomain d 2,
      commonK2TimeParametricKernel_real_local (d := d) G x * (f.1 x) =
        OS.S 2 f := by
  exact
    commonK2TimeParametricKernel_real_eq_schwinger_of_ae_eq_k2TimeParametricKernel_local
      (d := d) OS G hG_euclid
      (commonK2TimeParametricKernel_real_ae_eq_k2TimeParametricKernel_of_swapDelta_ae_zero_on_pos_local
        (d := d) G hG_diff hΔ_pos)
      f

end OSReconstruction
