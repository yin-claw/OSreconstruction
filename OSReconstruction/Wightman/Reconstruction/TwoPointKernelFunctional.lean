import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.CenterSpatialTranslationInvariant
import OSReconstruction.Wightman.Reconstruction.TwoPointDescent
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms

noncomputable section

open scoped Topology
open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The spacetime vector with zero time component and prescribed spatial part. -/
def centerSpatialVec (a : Fin d → ℝ) : SpacetimeDim d :=
  Fin.cases 0 a

@[simp] theorem centerSpatialVec_time (a : Fin d → ℝ) :
    centerSpatialVec (d := d) a 0 = 0 := by
  simp [centerSpatialVec]

@[simp] theorem centerSpatialVec_space (a : Fin d → ℝ) (i : Fin d) :
    centerSpatialVec (d := d) a i.succ = a i := by
  simp [centerSpatialVec]

/-- Translate only the center-spatial part of a two-point center/difference
configuration `(u, ξ)`. -/
def twoPointCenterSpatialTranslate (a : Fin d → ℝ) :
    NPointDomain d 2 → NPointDomain d 2 :=
  fun z i =>
    Fin.cases (z 0 + centerSpatialVec (d := d) a)
      (fun _ => z 1) i

@[simp] theorem twoPointCenterSpatialTranslate_zero
    (a : Fin d → ℝ) (z : NPointDomain d 2) :
    twoPointCenterSpatialTranslate (d := d) a z 0 =
      z 0 + centerSpatialVec (d := d) a := by
  simp [twoPointCenterSpatialTranslate]

@[simp] theorem twoPointCenterSpatialTranslate_one
    (a : Fin d → ℝ) (z : NPointDomain d 2) :
    twoPointCenterSpatialTranslate (d := d) a z 1 = z 1 := by
  change Fin.cases (z 0 + centerSpatialVec (d := d) a)
      (fun _ => z 1) (Fin.succ 0) = z 1
  rfl

private def twoPointCenterSpatialTranslate_measurableEquiv
    (a : Fin d → ℝ) :
    NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
  let eprod : NPointDomain d 2 ≃ᵐ (SpacetimeDim d × SpacetimeDim d) :=
    MeasurableEquiv.finTwoArrow
  let etrans : SpacetimeDim d ≃ᵐ SpacetimeDim d :=
    (Homeomorph.addRight (centerSpatialVec (d := d) a)).toMeasurableEquiv
  eprod.trans ((MeasurableEquiv.prodCongr etrans (MeasurableEquiv.refl _)).trans eprod.symm)

@[simp] private theorem twoPointCenterSpatialTranslate_measurableEquiv_apply
    (a : Fin d → ℝ) (z : NPointDomain d 2) :
    twoPointCenterSpatialTranslate_measurableEquiv (d := d) a z =
      twoPointCenterSpatialTranslate (d := d) a z := by
  ext i μ
  fin_cases i
  · simp [twoPointCenterSpatialTranslate_measurableEquiv, twoPointCenterSpatialTranslate,
      centerSpatialVec, MeasurableEquiv.prodCongr]
  · change z 1 μ = z 1 μ
    rfl

private theorem twoPointCenterSpatialTranslate_measurePreserving
    (a : Fin d → ℝ) :
    MeasureTheory.MeasurePreserving
      (twoPointCenterSpatialTranslate_measurableEquiv (d := d) a)
      MeasureTheory.volume MeasureTheory.volume := by
  let eprod : NPointDomain d 2 ≃ᵐ (SpacetimeDim d × SpacetimeDim d) :=
    MeasurableEquiv.finTwoArrow
  have heprod :
      MeasureTheory.MeasurePreserving eprod
        MeasureTheory.volume MeasureTheory.volume := by
    simpa [eprod] using
      (MeasureTheory.volume_preserving_finTwoArrow (SpacetimeDim d))
  have hprod :
      MeasureTheory.MeasurePreserving
        (Prod.map (fun x : SpacetimeDim d => x + centerSpatialVec (d := d) a) id)
        MeasureTheory.volume MeasureTheory.volume :=
    (translate_spacetime_measurePreserving (d := d) (centerSpatialVec (d := d) a)).prod
      (MeasureTheory.MeasurePreserving.id
        (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
  simpa [twoPointCenterSpatialTranslate_measurableEquiv]
    using heprod.symm.comp (hprod.comp heprod)

@[simp] private theorem centerSpatialShift_castAdd_zero
    (a : Fin d → ℝ) :
    centerSpatialShift d a (Fin.castAdd (d + 1) (0 : Fin (d + 1))) = 0 := by
  have htail :
      splitLast d (d + 2) (zeroTailBlockShift (m := d) (n := d + 2) a) = 0 := by
    simpa using splitLast_zeroTailBlockShift_eq_zero (m := d) (n := d + 2) a
  have := congrArg (fun v : Fin (d + 2) → ℝ => v 0) htail
  simpa [OSReconstruction.centerSpatialShift,
    OSReconstruction.centerSpatialFirstPerm_symm_castAdd_zero, splitLast] using this

@[simp] private theorem centerSpatialShift_castAdd_succ
    (a : Fin d → ℝ) (i : Fin d) :
    centerSpatialShift d a (Fin.castAdd (d + 1) i.succ) = a i := by
  have hhead :
      splitFirst d (d + 2) (zeroTailBlockShift (m := d) (n := d + 2) a) = a := by
    simpa using splitFirst_zeroTailBlockShift_eq (m := d) (n := d + 2) a
  have := congrArg (fun v : Fin d → ℝ => v i) hhead
  simpa [OSReconstruction.centerSpatialShift,
    OSReconstruction.centerSpatialFirstPerm_symm_castAdd_succ, splitFirst] using this

@[simp] private theorem centerSpatialShift_natAdd
    (a : Fin d → ℝ) (i : Fin (d + 1)) :
    centerSpatialShift d a (Fin.natAdd (d + 1) i) = 0 := by
  have htail :
      splitLast d (d + 2) (zeroTailBlockShift (m := d) (n := d + 2) a) = 0 := by
    simpa using splitLast_zeroTailBlockShift_eq_zero (m := d) (n := d + 2) a
  have := congrArg (fun v : Fin (d + 2) → ℝ => v i.succ) htail
  rw [OSReconstruction.centerSpatialShift,
    OSReconstruction.centerSpatialFirstPerm_symm_natAdd]
  simpa [splitLast] using this

private theorem centerSpatialShift_eq_addCases
    (a : Fin d → ℝ) :
    centerSpatialShift d a =
      Fin.addCases (centerSpatialVec (d := d) a) (fun _ : Fin (d + 1) => 0) := by
  funext i
  cases i using Fin.addCases with
  | left i =>
      cases i using Fin.cases with
      | zero =>
          rw [Fin.addCases_left]
          simpa using centerSpatialShift_castAdd_zero (d := d) a
      | succ j =>
          rw [Fin.addCases_left]
          simpa using centerSpatialShift_castAdd_succ (d := d) a j
  | right i =>
      rw [Fin.addCases_right]
      exact centerSpatialShift_natAdd (d := d) a i

/-- A polynomial-growth kernel on `NPointDomain d 2` induces a continuous scalar
Schwartz functional on the flattened two-point real coordinate space. -/
def twoPointFlatKernelCLM
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ := by
  let A : SchwartzNPoint d 2 →L[ℂ] ℂ :=
    { toLinearMap :=
        { toFun := fun f => ∫ x : NPointDomain d 2, K x * f x
          map_add' := by
            intro f g
            simp only [SchwartzMap.add_apply, mul_add]
            exact integral_add
              (schwartz_polynomial_kernel_integrable K hK_meas C_bd N hC hK_bound f)
              (schwartz_polynomial_kernel_integrable K hK_meas C_bd N hC hK_bound g)
          map_smul' := by
            intro a f
            simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
            simp_rw [show ∀ x : NPointDomain d 2, K x * (a * f x) = a * (K x * f x) by
              intro x
              ring]
            exact integral_const_mul a _ }
      cont := schwartz_polynomial_kernel_continuous K hK_meas C_bd N hC hK_bound }
  let e : 2 * (d + 1) = (d + 1) + (d + 1) := by ring
  let B : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] SchwartzNPoint d 2 :=
    (unflattenSchwartzNPoint (d := d)).comp (reindexSchwartzFin e.symm)
  exact A.comp B

/-- The inclusion of the zero-diagonal two-point Schwartz space into the full
two-point Schwartz space. -/
def zeroDiagonalTwoPointValCLM :
    ZeroDiagonalSchwartz d 2 →L[ℂ] SchwartzNPoint d 2 where
  toLinearMap := (zeroDiagonalSubmodule d 2).subtype
  cont := continuous_subtype_val

@[simp] theorem zeroDiagonalTwoPointValCLM_apply
    (f : ZeroDiagonalSchwartz d 2) :
    zeroDiagonalTwoPointValCLM (d := d) f = f.1 := rfl

/-- A polynomial-growth kernel on `NPointDomain d 2` induces a continuous
linear functional on the zero-diagonal two-point Schwartz space. -/
def twoPointZeroDiagonalKernelCLM
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    ZeroDiagonalSchwartz d 2 →L[ℂ] ℂ :=
  (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound).comp
    ((reindexSchwartzFin (by ring)).comp
      ((flattenSchwartzNPoint (d := d)).comp
        (zeroDiagonalTwoPointValCLM (d := d))))

theorem twoPointFlatKernelCLM_apply_reindex_flatten
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (F : SchwartzNPoint d 2) :
    twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
        (reindexSchwartzFin (by ring) (flattenSchwartzNPoint (d := d) F)) =
      ∫ x : NPointDomain d 2, K x * F x := by
  let e : 2 * (d + 1) = (d + 1) + (d + 1) := by ring
  have hreindex :
      reindexSchwartzFin e.symm
          (reindexSchwartzFin e (flattenSchwartzNPoint (d := d) F)) =
        flattenSchwartzNPoint (d := d) F := by
    ext y
    change
      flattenSchwartzNPoint (d := d) F
          (((castFinCLE e).symm) (((castFinCLE e).symm.symm) y)) =
        flattenSchwartzNPoint (d := d) F y
    simpa using
      congrArg (flattenSchwartzNPoint (d := d) F) ((castFinCLE e).symm_apply_apply y)
  have hunflat_flat :
      unflattenSchwartzNPoint (d := d) (flattenSchwartzNPoint (d := d) F) = F := by
    ext x
    simp
  simp [twoPointFlatKernelCLM, hreindex, hunflat_flat]

theorem twoPointZeroDiagonalKernelCLM_apply
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (f : ZeroDiagonalSchwartz d 2) :
    twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound f =
      ∫ x : NPointDomain d 2, K x * (f.1 x) := by
  simpa [twoPointZeroDiagonalKernelCLM] using
    twoPointFlatKernelCLM_apply_reindex_flatten
      (d := d) (K := K) hK_meas C_bd N hC hK_bound f.1

/-- Evaluate a flat witness kernel on a two-point center/difference
configuration after fixing the time-difference coordinate by `t`. -/
def twoPointFixedTimeKernel
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ) : NPointDomain d 2 → ℂ :=
  fun z =>
    G (Function.update
      (BHW.flattenCfg 2 d (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i)))
      (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
      (BHW.flattenCfg 2 d (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
        (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) + t))

theorem twoPointFixedTimeKernelCLM_apply_productLift
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (hK_meas : AEStronglyMeasurable (twoPointFixedTimeKernel (d := d) G t) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeKernel (d := d) G t x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (χ g : SchwartzSpacetime d) :
    twoPointFlatKernelCLM (d := d) (twoPointFixedTimeKernel (d := d) G t)
        hK_meas C_bd N hC hK_bound
        (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeKernel (d := d) G t z * (χ (z 0) * g (z 0 + z 1)) := by
  simpa [twoPointFixedTimeKernel] using
    twoPointFlatKernelCLM_apply_reindex_flatten
      (d := d) (K := twoPointFixedTimeKernel (d := d) G t)
      hK_meas C_bd N hC hK_bound
      (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g))

theorem twoPointFixedTimeKernelCLM_apply_differenceLift
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (hK_meas : AEStronglyMeasurable (twoPointFixedTimeKernel (d := d) G t) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeKernel (d := d) G t x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (χ : SchwartzSpacetime d) (h : SchwartzSpacetime d) :
    twoPointFlatKernelCLM (d := d) (twoPointFixedTimeKernel (d := d) G t)
        hK_meas C_bd N hC hK_bound
        (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeKernel (d := d) G t z * (χ (z 0) * h (z 1)) := by
  simpa [twoPointFixedTimeKernel] using
    twoPointFlatKernelCLM_apply_reindex_flatten
      (d := d) (K := twoPointFixedTimeKernel (d := d) G t)
      hK_meas C_bd N hC hK_bound
      (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h))

/-- Package the generic two-point kernel-functional route: once the kernel CLM
is center-spatial translation invariant and its descended reduced functional is
head-translation invariant, it produces the witness surface needed to compare
the product shell and the admissible difference shell. -/
theorem exists_twoPointFlatKernel_centerSpatialWitness
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (χ : SchwartzSpacetime d) (g h : SchwartzSpacetime d)
    (hT : OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d
      (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound))
    (φ : SchwartzMap (Fin d → ℝ) ℂ) (hφ : ∫ u : Fin d → ℝ, φ u = 1)
    (hTred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d
        (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ))
    (ψ : SchwartzMap ℝ ℂ) (hψ : ∫ s : ℝ, ψ s = 1) :
    ∃ T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ,
      OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d T ∧
      ∃ φ : SchwartzMap (Fin d → ℝ) ℂ, (∫ u : Fin d → ℝ, φ u = 1) ∧
        OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
          (OSReconstruction.centerSpatialDescentCLM d T φ) ∧
        ∃ ψ : SchwartzMap ℝ ℂ, (∫ s : ℝ, ψ s = 1) ∧
          T (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointProductLift χ g)))) =
            ∫ z : NPointDomain d 2, K z * (χ (z 0) * g (z 0 + z 1)) ∧
          T (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χ h)))) =
            ∫ z : NPointDomain d 2, K z * (χ (z 0) * h (z 1)) := by
  refine ⟨twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound, hT,
    φ, hφ, hTred, ψ, hψ, ?_, ?_⟩
  · simpa using
      twoPointFlatKernelCLM_apply_reindex_flatten
        (d := d) (K := K) hK_meas C_bd N hC hK_bound
        (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g))
  · simpa using
      twoPointFlatKernelCLM_apply_reindex_flatten
        (d := d) (K := K) hK_meas C_bd N hC hK_bound
        (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h))

end OSReconstruction
