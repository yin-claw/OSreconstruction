import OSReconstruction.Wightman.Reconstruction.SchwartzPartialEval
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

noncomputable section

open SchwartzMap
open scoped FourierTransform

namespace OSReconstruction

variable (d n : ℕ) [NeZero d]

/-- Split an `n`-point spacetime configuration into its `n` time coordinates and
its combined `n*d` spatial block. -/
noncomputable def nPointTimeSpatialCLE :
    NPointDomain d n ≃L[ℝ] (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d) := by
  let e : NPointDomain d n ≃ₗ[ℝ] (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d) :=
    { toFun := fun x =>
        ( fun i => x i 0
        , (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)).symm
            (fun p => x p.1 (Fin.succ p.2)) )
      invFun := fun y i =>
        Fin.cons (y.1 i)
          (fun j => (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) y.2) (i, j))
      map_add' := by
        intro x y
        ext i <;> simp
      map_smul' := by
        intro c x
        ext i <;> simp
      left_inv := by
        intro x
        ext i j
        refine Fin.cases ?_ ?_ j
        · rfl
        · intro k
          simp
      right_inv := by
        intro y
        ext i <;> simp }
  exact e.toContinuousLinearEquiv

/-- The Schwartz-space lift of `nPointTimeSpatialCLE`. -/
noncomputable def nPointTimeSpatialSchwartzCLE :
    SchwartzNPoint d n ≃L[ℂ]
      SchwartzMap ((Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) ℂ := by
  let e := nPointTimeSpatialCLE (d := d) n
  let toFwd :
      SchwartzNPoint d n →L[ℂ]
        SchwartzMap ((Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  let toInv :
      SchwartzMap ((Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) ℂ →L[ℂ]
        SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  exact
    { toLinearEquiv :=
        { toFun := toFwd
          map_add' := toFwd.map_add
          map_smul' := toFwd.map_smul
          invFun := toInv
          left_inv := by
            intro f
            ext x
            simp [toFwd, toInv, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e]
          right_inv := by
            intro f
            ext x
            simp [toFwd, toInv, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e] }
      continuous_toFun := toFwd.continuous
      continuous_invFun := toInv.continuous }

/-- The swapped version of `nPointTimeSpatialCLE`, so the spatial block appears
first and the time block second. This is the correct product order for
`SchwartzMap.partialEval₂`, which fixes the second factor. -/
noncomputable def nPointSpatialTimeCLE :
    NPointDomain d n ≃L[ℝ] EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) :=
  (nPointTimeSpatialCLE (d := d) n).trans
    (ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) (EuclideanSpace ℝ (Fin n × Fin d)))

/-- The Schwartz-space lift of `nPointSpatialTimeCLE`. -/
noncomputable def nPointSpatialTimeSchwartzCLE :
    SchwartzNPoint d n ≃L[ℂ]
      SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ)) ℂ := by
  let e := nPointSpatialTimeCLE (d := d) n
  let toFwd :
      SchwartzNPoint d n →L[ℂ]
        SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  let toInv :
      SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ)) ℂ →L[ℂ]
        SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  exact
    { toLinearEquiv :=
        { toFun := toFwd
          map_add' := toFwd.map_add
          map_smul' := toFwd.map_smul
          invFun := toInv
          left_inv := by
            intro f
            ext x
            simp [toFwd, toInv, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e]
          right_inv := by
            intro f
            ext x
            simp [toFwd, toInv, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e] }
      continuous_toFun := toFwd.continuous
      continuous_invFun := toInv.continuous }

omit [NeZero d] in
@[simp] theorem nPointSpatialTimeSchwartzCLE_apply
    (f : SchwartzNPoint d n)
    (η : EuclideanSpace ℝ (Fin n × Fin d)) (t : Fin n → ℝ) :
    nPointSpatialTimeSchwartzCLE (d := d) (n := n) f (η, t) =
      nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (t, η) := by
  simp [nPointSpatialTimeSchwartzCLE, nPointTimeSpatialCLE, nPointSpatialTimeCLE,
    nPointTimeSpatialSchwartzCLE, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- Split a product-valued iterated-derivative direction family into its two
coordinate direction families. -/
noncomputable def productDirectionSplit
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : ℕ) :
    (Fin l → E × F) ≃L[ℝ] (Fin l → E) × (Fin l → F) := by
  let e : (Fin l → E × F) ≃ₗ[ℝ] (Fin l → E) × (Fin l → F) :=
    { toFun := fun m => (fun i => (m i).1, fun i => (m i).2)
      invFun := fun m i => (m.1 i, m.2 i)
      map_add' := by
        intro x y
        ext i <;> rfl
      map_smul' := by
        intro c x
        ext i <;> rfl
      left_inv := by
        intro m
        funext i
        simp
      right_inv := by
        intro m
        ext i <;> rfl }
  exact
    { toLinearEquiv := e
      continuous_toFun := by
        refine Continuous.prodMk ?_ ?_
        · exact continuous_pi fun i => (continuous_apply i).fst
        · exact continuous_pi fun i => (continuous_apply i).snd
      continuous_invFun := by
        refine continuous_pi ?_
        intro i
        refine Continuous.prodMk ?_ ?_
        · exact (continuous_apply i).comp continuous_fst
        · exact (continuous_apply i).comp continuous_snd }

/-- The concrete pointwise partial spatial Fourier transform used in theorem-3
branch `3b`: fix the time block and Fourier-transform only the spatial block. -/
noncomputable def partialFourierSpatial_fun
    (f : SchwartzNPoint d n) :
    (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d) → ℂ :=
  fun p =>
    let slice :=
      SchwartzMap.partialEval₂ (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f) p.1
    (SchwartzMap.fourierTransformCLM ℂ slice) p.2

omit [NeZero d] in
theorem partialFourierSpatial_integrable
    (f : SchwartzNPoint d n)
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) :
    MeasureTheory.Integrable (fun η : EuclideanSpace ℝ (Fin n × Fin d) =>
      𝐞 (-(inner ℝ η p.2)) • nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (p.1, η)) := by
  let slice : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d)) ℂ :=
    SchwartzMap.partialEval₂ (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f) p.1
  have hslice : MeasureTheory.Integrable
      (slice : EuclideanSpace ℝ (Fin n × Fin d) → ℂ) := slice.integrable
  simpa [slice, SchwartzMap.partialEval₂, nPointSpatialTimeSchwartzCLE_apply] using
    (Real.fourierIntegral_convergent_iff (f := (slice : EuclideanSpace ℝ (Fin n × Fin d) → ℂ))
      (w := p.2)).2 hslice

omit [NeZero d] in
theorem partialFourierSpatial_fun_eq_integral
    (f : SchwartzNPoint d n)
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) :
    partialFourierSpatial_fun (d := d) (n := n) f p =
      ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
        𝐞 (-(inner ℝ η p.2)) •
          nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (p.1, η) := by
  simpa [partialFourierSpatial_fun, SchwartzMap.fourierTransformCLM_apply,
    SchwartzMap.partialEval₂, nPointSpatialTimeSchwartzCLE_apply] using
    (Real.fourier_eq
      (((SchwartzMap.partialEval₂
          (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f) p.1 :
            SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d)) ℂ) :
          EuclideanSpace ℝ (Fin n × Fin d) → ℂ))
      p.2)

end OSReconstruction
