/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernel
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Euclidean Weyl Infrastructure

This file starts the pure Euclidean analysis package used by the localized
Weyl lemma in the distributional edge-of-the-wedge route.  The declarations
here contain no OS, Wightman, or EOW-specific data: they only record
translation and support bookkeeping for compactly supported Schwartz kernels
on finite-dimensional Euclidean spaces.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter
open scoped LineDeriv

namespace SCV

/-- Translation on Euclidean Schwartz space as a continuous linear map:
`(euclideanTranslateSchwartzCLM a φ)(x) = φ (x + a)`. -/
noncomputable def euclideanTranslateSchwartzCLM
    {ι : Type*} [Fintype ι]
    (a : EuclideanSpace ℝ ι) :
    SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ ι) ℂ := by
  let g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x => x + a
  have hg : g.HasTemperateGrowth := by
    fun_prop
  have hg_upper :
      ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k := by
    refine ⟨1, 1 + ‖a‖, ?_⟩
    intro x
    have htri : ‖x‖ ≤ ‖g x‖ + ‖a‖ := by
      calc
        ‖x‖ = ‖(x + a) - a‖ := by simp
        _ ≤ ‖g x‖ + ‖a‖ := by simpa [g] using norm_sub_le (x + a) a
    have hfac : ‖g x‖ + ‖a‖ ≤ (1 + ‖a‖) * (1 + ‖g x‖) := by
      nlinarith [norm_nonneg (g x), norm_nonneg a]
    have hpow : (1 + ‖g x‖) ^ (1 : ℕ) = 1 + ‖g x‖ := by simp
    rw [hpow]
    exact le_trans htri hfac
  exact SchwartzMap.compCLM (𝕜 := ℂ) (g := g) hg hg_upper

@[simp]
theorem euclideanTranslateSchwartz_apply
    {ι : Type*} [Fintype ι]
    (a : EuclideanSpace ℝ ι)
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x : EuclideanSpace ℝ ι) :
    euclideanTranslateSchwartzCLM a φ x = φ (x + a) := rfl

/-- Euclidean translations of a Schwartz function have polynomial seminorm
growth in the translation parameter. -/
theorem seminorm_euclideanTranslateSchwartz_le
    {ι : Type*} [Fintype ι]
    (k l : ℕ) (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a : EuclideanSpace ℝ ι,
      (SchwartzMap.seminorm ℂ k l) (euclideanTranslateSchwartzCLM a f) ≤
        D * (1 + ‖a‖) ^ k := by
  obtain ⟨Ck, hCk⟩ := f.decay' k l
  obtain ⟨C0, hC0⟩ := f.decay' 0 l
  have hC0' :
      ∀ y : EuclideanSpace ℝ ι, ‖iteratedFDeriv ℝ l (⇑f) y‖ ≤ C0 := by
    intro y
    have hy := hC0 y
    simp [pow_zero] at hy
    simpa using hy
  have hCk_nn : 0 ≤ Ck :=
    le_trans (mul_nonneg (pow_nonneg (norm_nonneg _) k) (norm_nonneg _)) (hCk 0)
  have hC0_nn : 0 ≤ C0 := le_trans (norm_nonneg _) (hC0' 0)
  set D := 2 ^ (k - 1) * (Ck + C0)
  have hD_nn : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (by linarith)
  refine ⟨D, hD_nn, fun a => ?_⟩
  apply SchwartzMap.seminorm_le_bound ℂ k l _ <| mul_nonneg hD_nn
    (pow_nonneg (by linarith [norm_nonneg a]) k)
  intro x
  have hcoe :
      (⇑(euclideanTranslateSchwartzCLM a f) :
        EuclideanSpace ℝ ι → ℂ) = fun z => f (z + a) :=
    funext fun _ => rfl
  rw [hcoe, iteratedFDeriv_comp_add_right]
  have hnorm_x : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
    calc
      ‖x‖ = ‖(x + a) - a‖ := by simp
      _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
  have h1a : 1 ≤ 1 + ‖a‖ := le_add_of_nonneg_right (norm_nonneg a)
  have hkey : Ck + ‖a‖ ^ k * C0 ≤ (1 + ‖a‖) ^ k * (Ck + C0) := by
    rw [mul_add]
    apply add_le_add
    · exact le_mul_of_one_le_left hCk_nn (one_le_pow₀ h1a)
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg a) (le_add_of_nonneg_left zero_le_one) k) hC0_nn
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x + a)‖
        ≤ (‖x + a‖ + ‖a‖) ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x + a)‖ := by
          gcongr
    _ ≤ (2 ^ (k - 1) * (‖x + a‖ ^ k + ‖a‖ ^ k)) *
          ‖iteratedFDeriv ℝ l (⇑f) (x + a)‖ := by
          gcongr
          exact add_pow_le (norm_nonneg _) (norm_nonneg _) k
    _ = 2 ^ (k - 1) *
          (‖x + a‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x + a)‖ +
            ‖a‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x + a)‖) := by
          ring
    _ ≤ 2 ^ (k - 1) * (Ck + ‖a‖ ^ k * C0) := by
          gcongr
          · exact hCk (x + a)
          · exact hC0' (x + a)
    _ ≤ 2 ^ (k - 1) * ((1 + ‖a‖) ^ k * (Ck + C0)) := by
          gcongr
    _ = D * (1 + ‖a‖) ^ k := by
          simp only [D]
          ring

/-- The reflected translate of a Euclidean Schwartz kernel:
`euclideanReflectedTranslate x ρ y = ρ (y - x)`. -/
noncomputable def euclideanReflectedTranslate
    {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
  euclideanTranslateSchwartzCLM (-x) ρ

@[simp]
theorem euclideanReflectedTranslate_apply
    {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℝ ι)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    euclideanReflectedTranslate x ρ y = ρ (y - x) := by
  simp [euclideanReflectedTranslate, sub_eq_add_neg]

/-- If a reflected Euclidean kernel of radius `r` is centered at a point whose
closed `r`-ball lies in `V`, then the reflected translate is compactly
supported in `V`. -/
theorem supportsInOpen_euclideanReflectedTranslate_of_kernelSupport
    {ι : Type*} [Fintype ι]
    {V : Set (EuclideanSpace ℝ ι)}
    {x : EuclideanSpace ℝ ι} {r : ℝ}
    {ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ}
    (hx : Metric.closedBall x r ⊆ V)
    (hρ : tsupport (ρ : EuclideanSpace ℝ ι → ℂ) ⊆
      Metric.closedBall 0 r) :
    SupportsInOpen
      (euclideanReflectedTranslate x ρ :
        EuclideanSpace ℝ ι → ℂ) V := by
  let e : EuclideanSpace ℝ ι ≃ₜ EuclideanSpace ℝ ι := Homeomorph.addRight (-x)
  have hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ) := by
    exact IsCompact.of_isClosed_subset
      (isCompact_closedBall 0 r) (isClosed_tsupport _) hρ
  constructor
  · change HasCompactSupport fun y : EuclideanSpace ℝ ι => ρ (e y)
    exact hρ_compact.comp_homeomorph e
  · have htsupport :
        tsupport
          (euclideanReflectedTranslate x ρ :
            EuclideanSpace ℝ ι → ℂ) =
          e ⁻¹' tsupport (ρ : EuclideanSpace ℝ ι → ℂ) := by
      simpa [e, euclideanReflectedTranslate, sub_eq_add_neg] using
        (tsupport_comp_eq_preimage
          (g := (ρ : EuclideanSpace ℝ ι → ℂ)) e)
    intro y hy
    have hyρ : y - x ∈ tsupport (ρ : EuclideanSpace ℝ ι → ℂ) := by
      simpa [htsupport, e, sub_eq_add_neg] using hy
    have hyball0 : y - x ∈ Metric.closedBall (0 : EuclideanSpace ℝ ι) r :=
      hρ hyρ
    have hyball : y ∈ Metric.closedBall x r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hyball0
    exact hx hyball

private theorem iteratedFDeriv_sub_euclidean_schwartz
    {ι : Type*} [Fintype ι]
    (f g : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (n : ℕ) (x : EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ n (⇑(f - g)) x =
      iteratedFDeriv ℝ n (⇑f) x - iteratedFDeriv ℝ n (⇑g) x := by
  have hf : ContDiff ℝ n (⇑f) := f.smooth n
  have hg : ContDiff ℝ n (⇑g) := g.smooth n
  have hfg :
      (⇑(f - g) : EuclideanSpace ℝ ι → ℂ) =
        (⇑f) + fun x => -(⇑g x) := by
    ext y
    simp [sub_eq_add_neg]
  have hneg : (fun x => -(⇑g x)) = -⇑g := rfl
  rw [hfg, iteratedFDeriv_add_apply hf.contDiffAt hg.neg.contDiffAt,
    hneg, iteratedFDeriv_neg_apply]
  simp [sub_eq_add_neg]

/-- Euclidean directional derivatives of Schwartz functions commute. -/
theorem euclideanLineDerivOp_comm
    {ι : Type*} [Fintype ι]
    (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (v w : EuclideanSpace ℝ ι) :
    ∂_{v} ((∂_{w} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)) =
      ∂_{w} ((∂_{v} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)) := by
  ext x
  have hsym :=
    (f.contDiffAt (2 : ℕ∞) (x := x)).isSymmSndFDerivAt
      (n := (2 : WithTop ℕ∞)) (by simp)
  calc
    (∂_{v} ((∂_{w} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ))) x =
        (∂^{![v, w]} f) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]
    _ = iteratedFDeriv ℝ 2
          (f : EuclideanSpace ℝ ι → ℂ) x ![v, w] := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![v, w]) (x := x))
    _ = iteratedFDeriv ℝ 2
          (f : EuclideanSpace ℝ ι → ℂ) x ![w, v] := by
      exact hsym.iteratedFDeriv_cons
    _ = (∂^{![w, v]} f) x := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![w, v]) (x := x)).symm
    _ = (∂_{w} ((∂_{v} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ))) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]

/-- A single Euclidean directional derivative commutes past an iterated
directional derivative. -/
theorem euclideanLineDerivOp_iterated_comm
    {ι : Type*} [Fintype ι] {n : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (v : EuclideanSpace ℝ ι)
    (u : Fin n → EuclideanSpace ℝ ι) :
    ∂_{v} (∂^{u} f) = ∂^{u} (∂_{v} f) := by
  induction n generalizing f with
  | zero =>
      ext x
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_right,
        LineDeriv.iteratedLineDerivOp_succ_right]
      rw [ih (f := ∂_{u (Fin.last n)} f)]
      congr 1
      exact euclideanLineDerivOp_comm f v (u (Fin.last n))

/-- Differentiating an iterated Euclidean derivative in direction `v` is the
same as iterating after the line derivative `∂_v`. -/
theorem fderiv_iteratedFDeriv_eq_iteratedFDeriv_euclideanLineDeriv
    {ι : Type*} [Fintype ι] {n : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (v x : EuclideanSpace ℝ ι) :
    fderiv ℝ (iteratedFDeriv ℝ n
        (f : EuclideanSpace ℝ ι → ℂ)) x v =
      iteratedFDeriv ℝ n
        (((∂_{v} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
          EuclideanSpace ℝ ι → ℂ)) x := by
  ext u
  calc
    (fderiv ℝ (iteratedFDeriv ℝ n
        (f : EuclideanSpace ℝ ι → ℂ)) x v) u =
        iteratedFDeriv ℝ (n + 1)
          (f : EuclideanSpace ℝ ι → ℂ) x (Fin.cons v u) := by
      simp [iteratedFDeriv_succ_apply_left]
    _ = (∂^{Fin.cons v u} f) x := by
      symm
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := Fin.cons v u) (x := x))
    _ = (∂_{v} (∂^{u} f)) x := by
      simpa using
        (congrArg (fun g : SchwartzMap (EuclideanSpace ℝ ι) ℂ => g x)
          (LineDeriv.iteratedLineDerivOp_succ_left
            (m := Fin.cons v u) (f := f)))
    _ = (∂^{u} (∂_{v} f)) x := by
      rw [euclideanLineDerivOp_iterated_comm (f := f) (v := v) (u := u)]
    _ = iteratedFDeriv ℝ n
          (((∂_{v} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
            EuclideanSpace ℝ ι → ℂ)) x u := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := (∂_{v} f : SchwartzMap (EuclideanSpace ℝ ι) ℂ))
          (m := u) (x := x))

/-- A first-order Euclidean translation estimate in Schwartz seminorms. -/
theorem exists_seminorm_euclideanTranslateSchwartz_sub_le_linear
    {ι : Type*} [Fintype ι]
    (g : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (v : EuclideanSpace ℝ ι) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, |t| ≤ 1 →
        SchwartzMap.seminorm ℝ k n
          (euclideanTranslateSchwartzCLM (t • v) g - g) ≤ C * |t| := by
  obtain ⟨D, hD_nonneg, hD⟩ :=
    seminorm_euclideanTranslateSchwartz_le k (n + 1) g
  let C : ℝ := ‖v‖ * D * (1 + ‖v‖) ^ k
  refine ⟨C, by positivity, ?_⟩
  intro t ht
  refine SchwartzMap.seminorm_le_bound ℝ k n
      (euclideanTranslateSchwartzCLM (t • v) g - g)
      (by positivity) ?_
  intro x
  let H :
      EuclideanSpace ℝ ι →
        ContinuousMultilinearMap ℝ
          (fun _ : Fin n => EuclideanSpace ℝ ι) ℂ :=
    iteratedFDeriv ℝ n (g : EuclideanSpace ℝ ι → ℂ)
  let hxFun : ℝ →
      ContinuousMultilinearMap ℝ
        (fun _ : Fin n => EuclideanSpace ℝ ι) ℂ :=
    fun s => ‖x‖ ^ k • H (x + s • (t • v))
  have hH_diff : Differentiable ℝ H := by
    simpa [H] using
      (g.smooth (n + 1)).differentiable_iteratedFDeriv (by
        exact_mod_cast Nat.lt_succ_self n)
  have hxFun_hasDeriv :
      ∀ s : ℝ,
        HasDerivAt hxFun
          (‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))) s := by
    intro s
    have hgamma :
        HasDerivAt
          (fun r : ℝ => x + r • (t • v)) (t • v) s := by
      let L : ℝ →L[ℝ] ℝ := 1
      let Lsmul : ℝ →L[ℝ] EuclideanSpace ℝ ι :=
        ContinuousLinearMap.smulRight L (t • v)
      simpa [L, Lsmul, ContinuousLinearMap.smulRight_apply, one_smul,
        add_comm, add_left_comm, add_assoc] using (Lsmul.hasDerivAt).const_add x
    have hcomp :
        HasDerivAt (fun r : ℝ => H (x + r • (t • v)))
          ((fderiv ℝ H (x + s • (t • v))) (t • v)) s := by
      exact (hH_diff (x + s • (t • v))).hasFDerivAt.comp_hasDerivAt s hgamma
    simpa [hxFun] using hcomp.const_smul (‖x‖ ^ k)
  have hxFun_bound :
      ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))‖ ≤ C * |t| := by
    intro s hs
    have hs_abs : |s| ≤ 1 := by
      have hs0 : 0 ≤ s := hs.1
      have hs1 : s ≤ 1 := le_of_lt hs.2
      rw [abs_of_nonneg hs0]
      exact hs1
    have hstv_norm : ‖s • (t • v)‖ ≤ ‖v‖ := by
      calc
        ‖s • (t • v)‖ = |s| * (|t| * ‖v‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * (1 * ‖v‖) := by
          gcongr
        _ = ‖v‖ := by ring
    have hone_pow :
        (1 + ‖s • (t • v)‖) ^ k ≤ (1 + ‖v‖) ^ k := by
      gcongr
    have hseminorm0 :
        ‖x‖ ^ k *
            ‖iteratedFDeriv ℝ (n + 1)
              (⇑(euclideanTranslateSchwartzCLM (s • (t • v)) g)) x‖ ≤
          D * (1 + ‖s • (t • v)‖) ^ k := by
      exact le_trans (SchwartzMap.le_seminorm ℂ k (n + 1) _ x) (hD (s • (t • v)))
    have hseminorm :
        ‖x‖ ^ k *
            ‖iteratedFDeriv ℝ (n + 1)
              (g : EuclideanSpace ℝ ι → ℂ) (x + s • (t • v))‖ ≤
          D * (1 + ‖s • (t • v)‖) ^ k := by
      have htrans :
          iteratedFDeriv ℝ (n + 1)
            (⇑(euclideanTranslateSchwartzCLM (s • (t • v)) g)) x =
          iteratedFDeriv ℝ (n + 1)
            (g : EuclideanSpace ℝ ι → ℂ) (x + s • (t • v)) := by
        simpa using
          (iteratedFDeriv_comp_add_right
            (f := (g : EuclideanSpace ℝ ι → ℂ)) (n + 1) (s • (t • v)) x)
      simpa [htrans] using hseminorm0
    have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
    calc
      ‖‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))‖
          = ‖x‖ ^ k * ‖(fderiv ℝ H (x + s • (t • v))) (t • v)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hxpow_nonneg]
      _ ≤ ‖x‖ ^ k * (‖fderiv ℝ H (x + s • (t • v))‖ * ‖t • v‖) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm _ _
      _ = (‖x‖ ^ k * ‖fderiv ℝ H (x + s • (t • v))‖) * ‖t • v‖ := by
            ring
      _ = (‖x‖ ^ k *
            ‖iteratedFDeriv ℝ (n + 1)
              (g : EuclideanSpace ℝ ι → ℂ) (x + s • (t • v))‖) *
            ‖t • v‖ := by
            rw [norm_fderiv_iteratedFDeriv]
      _ ≤ (D * (1 + ‖s • (t • v)‖) ^ k) * ‖t • v‖ := by
            gcongr
      _ ≤ (D * (1 + ‖v‖) ^ k) * ‖t • v‖ := by
            gcongr
      _ = (D * (1 + ‖v‖) ^ k) * (|t| * ‖v‖) := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = C * |t| := by
            dsimp [C]
            ring
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := hxFun)
      (f' := fun s => ‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v)))
      (fun s hs => (hxFun_hasDeriv s).hasDerivWithinAt)
      hxFun_bound
  have hiter_eq :
      iteratedFDeriv ℝ n
        (⇑(euclideanTranslateSchwartzCLM (t • v) g - g)) x =
        H (x + t • v) - H x := by
    have htrans :
        iteratedFDeriv ℝ n
          (⇑(euclideanTranslateSchwartzCLM (t • v) g)) x =
          H (x + t • v) := by
      simpa [H] using
        (iteratedFDeriv_comp_add_right
          (f := (g : EuclideanSpace ℝ ι → ℂ)) n (t • v) x)
    rw [iteratedFDeriv_sub_euclidean_schwartz]
    rw [htrans]
  have hxFun_diff :
      hxFun 1 - hxFun 0 = ‖x‖ ^ k • (H (x + t • v) - H x) := by
    simp [hxFun, smul_sub]
  calc
    ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (⇑(euclideanTranslateSchwartzCLM (t • v) g - g)) x‖
        = ‖hxFun 1 - hxFun 0‖ := by
            rw [hxFun_diff, hiter_eq, norm_smul, Real.norm_eq_abs]
            have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
            simp [abs_of_nonneg hxpow_nonneg]
    _ ≤ C * |t| := by simpa [sub_eq_add_neg] using hmv

/-- Compactly supported Euclidean translations are continuous in the Schwartz
topology. -/
theorem tendsto_euclideanTranslateSchwartz_nhds_of_isCompactSupport
    {ι : Type*} [Fintype ι]
    (ψ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hψ_compact : HasCompactSupport (ψ : EuclideanSpace ℝ ι → ℂ))
  (a0 : EuclideanSpace ℝ ι) :
    Tendsto (fun a : EuclideanSpace ℝ ι => euclideanTranslateSchwartzCLM a ψ)
      (𝓝 a0) (𝓝 (euclideanTranslateSchwartzCLM a0 ψ)) := by
  let K : Set (EuclideanSpace ℝ ι) :=
    tsupport (ψ : EuclideanSpace ℝ ι → ℂ)
  rw [(schwartz_withSeminorms ℝ (EuclideanSpace ℝ ι) ℂ).tendsto_nhds _ _]
  intro ⟨k, n⟩ ε hε
  let J : Set (EuclideanSpace ℝ ι) := Metric.closedBall a0 1
  have ha0J : a0 ∈ J := Metric.mem_closedBall_self (by positivity)
  have hJ_compact : IsCompact J := isCompact_closedBall _ _
  let Ktrans : Set (EuclideanSpace ℝ ι) :=
    (fun p : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) => p.1 - p.2) '' (K ×ˢ J)
  have hKtrans_compact : IsCompact Ktrans := by
    refine (hψ_compact.prod hJ_compact).image ?_
    exact continuous_fst.sub continuous_snd
  let q : EuclideanSpace ℝ ι → ℝ := fun x => ‖x‖ ^ k
  have hq_cont : Continuous q := continuous_norm.pow k
  obtain ⟨B, hB⟩ :=
    hKtrans_compact.exists_bound_of_continuousOn (f := q) hq_cont.continuousOn
  let M : ℝ := max 1 B
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let H : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ ι) ℂ :=
    fun p => iteratedFDeriv ℝ n (⇑ψ) (p.1 + p.2)
  have hH_cont : Continuous H := by
    let A : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) →
        EuclideanSpace ℝ ι := fun p => p.1 + p.2
    have hA : Continuous A := continuous_fst.add continuous_snd
    exact ((ψ.smooth n).continuous_iteratedFDeriv le_rfl).comp hA
  have hH_uc : UniformContinuousOn H (Ktrans ×ˢ J) :=
    (hKtrans_compact.prod hJ_compact).uniformContinuousOn_of_continuous hH_cont.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp hH_uc (ε / (2 * M)) (by positivity) with
    ⟨δ, hδ, hHδ⟩
  have hJ_nhds : J ∈ 𝓝 a0 := Metric.closedBall_mem_nhds _ (by positivity)
  have hball_nhds : Metric.ball a0 δ ∈ 𝓝 a0 := Metric.ball_mem_nhds _ hδ
  filter_upwards [inter_mem hJ_nhds hball_nhds] with a ha
  have haJ : a ∈ J := ha.1
  have hadist : dist a a0 < δ := ha.2
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℝ k n
      (euclideanTranslateSchwartzCLM a ψ - euclideanTranslateSchwartzCLM a0 ψ)
      (by positivity) ?_
  intro x
  by_cases hx : x ∈ Ktrans
  · have hpair_a : (x, a) ∈ Ktrans ×ˢ J := ⟨hx, haJ⟩
    have hpair_a0 : (x, a0) ∈ Ktrans ×ˢ J := ⟨hx, ha0J⟩
    have hpair_dist : dist (x, a) (x, a0) < δ := by
      simpa [Prod.dist_eq] using hadist
    have hderiv_close : ‖H (x, a) - H (x, a0)‖ < ε / (2 * M) := by
      simpa [H, dist_eq_norm] using hHδ _ hpair_a _ hpair_a0 hpair_dist
    have hnormx : ‖x‖ ^ k ≤ M := by
      have hBx : ‖q x‖ ≤ B := hB x hx
      have hqx : ‖q x‖ = ‖x‖ ^ k := by
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg (pow_nonneg (norm_nonneg x) k)
      rw [hqx] at hBx
      exact le_trans hBx (le_max_right _ _)
    have hEq :
        iteratedFDeriv ℝ n
          (⇑(euclideanTranslateSchwartzCLM a ψ -
            euclideanTranslateSchwartzCLM a0 ψ)) x =
          H (x, a) - H (x, a0) := by
      have htrans_a :
          iteratedFDeriv ℝ n (⇑(euclideanTranslateSchwartzCLM a ψ)) x =
            H (x, a) := by
        simpa [H] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n a x)
      have htrans_a0 :
          iteratedFDeriv ℝ n (⇑(euclideanTranslateSchwartzCLM a0 ψ)) x =
            H (x, a0) := by
        simpa [H] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n a0 x)
      rw [iteratedFDeriv_sub_euclidean_schwartz, htrans_a, htrans_a0]
    rw [hEq]
    have hhalf : M * (ε / (2 * M)) = ε / 2 := by
      field_simp [hMpos.ne']
    calc
      ‖x‖ ^ k * ‖H (x, a) - H (x, a0)‖
          ≤ ‖x‖ ^ k * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_left (le_of_lt hderiv_close) (by positivity)
      _ ≤ M * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_right hnormx (by positivity)
      _ = ε / 2 := hhalf
  · have hsupport_deriv :
        Function.support (iteratedFDeriv ℝ n (⇑ψ)) ⊆ K := by
      intro y hy
      have hy' := support_iteratedFDeriv_subset (𝕜 := ℝ) (n := n) (f := ⇑ψ) hy
      simpa [K] using hy'
    have hx_not_a : x + a ∉ K := by
      intro hxa
      exact hx ⟨(x + a, a), ⟨hxa, haJ⟩, by simp⟩
    have hx_not_a0 : x + a0 ∉ K := by
      intro hxa0
      exact hx ⟨(x + a0, a0), ⟨hxa0, ha0J⟩, by simp⟩
    have hzero_a : iteratedFDeriv ℝ n (⇑ψ) (x + a) = 0 := by
      by_contra hne
      exact hx_not_a (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hzero_a0 : iteratedFDeriv ℝ n (⇑ψ) (x + a0) = 0 := by
      by_contra hne
      exact hx_not_a0 (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hEq :
        iteratedFDeriv ℝ n
          (⇑(euclideanTranslateSchwartzCLM a ψ -
            euclideanTranslateSchwartzCLM a0 ψ)) x = 0 := by
      rw [iteratedFDeriv_sub_euclidean_schwartz]
      rw [show iteratedFDeriv ℝ n (⇑(euclideanTranslateSchwartzCLM a ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + a) by
              simpa using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n a x)]
      rw [show iteratedFDeriv ℝ n (⇑(euclideanTranslateSchwartzCLM a0 ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + a0) by
              simpa using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n a0 x)]
      simp [hzero_a, hzero_a0]
    rw [hEq]
    have : (0 : ℝ) ≤ ε / 2 := by positivity
    simpa using this

/-- Applying a continuous linear functional to compactly supported Euclidean
translates gives a continuous scalar function of the translation parameter. -/
theorem continuous_apply_euclideanTranslateSchwartz_of_isCompactSupport
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ψ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hψ_compact : HasCompactSupport (ψ : EuclideanSpace ℝ ι → ℂ)) :
    Continuous
      (fun a : EuclideanSpace ℝ ι => T (euclideanTranslateSchwartzCLM a ψ)) := by
  refine continuous_iff_continuousAt.2 ?_
  intro a0
  exact T.continuous.continuousAt.tendsto.comp
    (tendsto_euclideanTranslateSchwartz_nhds_of_isCompactSupport ψ hψ_compact a0)

/-- The regularized distribution obtained by pairing a compactly supported
reflected Euclidean kernel with a continuous Schwartz functional is continuous
in the center. -/
theorem continuous_apply_euclideanReflectedTranslate_of_isCompactSupport
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ)) :
    Continuous
      (fun x : EuclideanSpace ℝ ι => T (euclideanReflectedTranslate x ρ)) := by
  have htranslate :=
    continuous_apply_euclideanTranslateSchwartz_of_isCompactSupport T ρ hρ_compact
  simpa [euclideanReflectedTranslate] using htranslate.comp continuous_neg

end SCV
