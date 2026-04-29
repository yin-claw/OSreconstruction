/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernelFactorization
import OSReconstruction.SCV.DistributionalEOWSupport

/-!
# Local Product-Kernel Descent

This file starts the scalarized local descent package used after local EOW
product-kernel covariance has been proved.  The package deliberately begins
with small continuous-linear primitives rather than a global quotient theorem:
local covariance will only be consumed under explicit support hypotheses.
-/

noncomputable section

open Complex MeasureTheory

namespace SCV

/-- Product norm is controlled by the sum of the coordinate norms. -/
private theorem norm_prod_le_fst_add_snd
    {E₁ E₂ : Type*} [SeminormedAddCommGroup E₁] [SeminormedAddCommGroup E₂]
    (x : E₁ × E₂) :
    ‖x‖ ≤ ‖x.1‖ + ‖x.2‖ := by
  rw [Prod.norm_def]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))

/-- The real embedding as a public continuous real-linear map. -/
def realEmbedContinuousLinearMap (m : ℕ) :
    (Fin m → ℝ) →L[ℝ] ComplexChartSpace m :=
  ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

@[simp]
theorem realEmbedContinuousLinearMap_apply {m : ℕ} (a : Fin m → ℝ) :
    realEmbedContinuousLinearMap m a = realEmbed a := by
  ext i
  simp [realEmbedContinuousLinearMap, realEmbed]

/-- Fixed-left mixed tensor product as a continuous linear map in the real
kernel argument. -/
def schwartzTensorProduct₂CLMLeft {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ := by
  refine SchwartzMap.mkCLM (𝕜 := ℂ)
    (fun ψ p => φ p.1 * ψ p.2)
    (fun ψ η p => by simp [mul_add])
    (fun c ψ p => by simp [smul_eq_mul, mul_left_comm])
    (fun ψ => φ.smooth'.fst'.mul ψ.smooth'.snd') ?_
  rintro ⟨k, l⟩
  let s : Finset (ℕ × ℕ) :=
    (Finset.range (l + 1)).image (fun i => ((0, l - i) : ℕ × ℕ)) ∪
      (Finset.range (l + 1)).image (fun i => ((k, l - i) : ℕ × ℕ))
  let C : ℝ :=
    (2 : ℝ) ^ k * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
      (SchwartzMap.seminorm ℂ k i φ +
        SchwartzMap.seminorm ℂ 0 i φ)
  refine ⟨s, C, by positivity, fun ψ x => ?_⟩
  have hφs := φ.smooth'.comp
    (ContinuousLinearMap.fst ℝ (ComplexChartSpace m) (Fin m → ℝ)).contDiff
  have hψs := ψ.smooth'.comp
    (ContinuousLinearMap.snd ℝ (ComplexChartSpace m) (Fin m → ℝ)).contDiff
  have hcf : ∀ j (x : ComplexChartSpace m × (Fin m → ℝ)),
      ‖iteratedFDeriv ℝ j (φ.toFun ∘ Prod.fst) x‖ ≤
        ‖iteratedFDeriv ℝ j φ.toFun x.1‖ := by
    intro j x
    rw [show φ.toFun ∘ Prod.fst =
        φ.toFun ∘ ⇑(ContinuousLinearMap.fst ℝ (ComplexChartSpace m) (Fin m → ℝ)) from rfl,
      (ContinuousLinearMap.fst ℝ (ComplexChartSpace m) (Fin m → ℝ)).iteratedFDeriv_comp_right
        φ.smooth' x (by exact_mod_cast le_top)]
    exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one (fun _ _ => norm_nonneg _)
          (fun _ _ =>
            ContinuousLinearMap.norm_fst_le ℝ (ComplexChartSpace m) (Fin m → ℝ))))
  have hcg : ∀ j (x : ComplexChartSpace m × (Fin m → ℝ)),
      ‖iteratedFDeriv ℝ j (ψ.toFun ∘ Prod.snd) x‖ ≤
        ‖iteratedFDeriv ℝ j ψ.toFun x.2‖ := by
    intro j x
    rw [show ψ.toFun ∘ Prod.snd =
        ψ.toFun ∘ ⇑(ContinuousLinearMap.snd ℝ (ComplexChartSpace m) (Fin m → ℝ)) from rfl,
      (ContinuousLinearMap.snd ℝ (ComplexChartSpace m) (Fin m → ℝ)).iteratedFDeriv_comp_right
        ψ.smooth' x (by exact_mod_cast le_top)]
    exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one (fun _ _ => norm_nonneg _)
          (fun _ _ =>
            ContinuousLinearMap.norm_snd_le ℝ (ComplexChartSpace m) (Fin m → ℝ))))
  have hLeib := norm_iteratedFDeriv_mul_le (n := l) hφs hψs x
    (WithTop.coe_le_coe.mpr (le_top (a := (l : ℕ∞))))
  have add_pow_le : (‖x.1‖ + ‖x.2‖) ^ k ≤
      (2 : ℝ) ^ k * (‖x.1‖ ^ k + ‖x.2‖ ^ k) := by
    have hmax : (max ‖x.1‖ ‖x.2‖) ^ k ≤ ‖x.1‖ ^ k + ‖x.2‖ ^ k := by
      rcases max_cases ‖x.1‖ ‖x.2‖ with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
      · rw [h]; exact le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
    have h_add_le_2max : ‖x.1‖ + ‖x.2‖ ≤ 2 * max ‖x.1‖ ‖x.2‖ := by
      linarith [le_max_left ‖x.1‖ ‖x.2‖, le_max_right ‖x.1‖ ‖x.2‖]
    calc
      (‖x.1‖ + ‖x.2‖) ^ k ≤ (2 * max ‖x.1‖ ‖x.2‖) ^ k :=
        pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) h_add_le_2max _
      _ = (2 : ℝ) ^ k * (max ‖x.1‖ ‖x.2‖) ^ k := mul_pow (2 : ℝ) _ k
      _ ≤ (2 : ℝ) ^ k * (‖x.1‖ ^ k + ‖x.2‖ ^ k) :=
        mul_le_mul_of_nonneg_left hmax (pow_nonneg (by norm_num) _)
  have h_pow : ‖x‖ ^ k ≤ (2 : ℝ) ^ k * (‖x.1‖ ^ k + ‖x.2‖ ^ k) :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_prod_le_fst_add_snd x) _).trans add_pow_le
  have h_term : ∀ i ∈ Finset.range (l + 1),
      ‖x‖ ^ k * (↑(l.choose i) * ‖iteratedFDeriv ℝ i φ.toFun x.1‖ *
        ‖iteratedFDeriv ℝ (l - i) ψ.toFun x.2‖) ≤
      (2 : ℝ) ^ k * (↑(l.choose i) *
        ((SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ 0 i φ) *
          (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ)) := by
    intro i hi
    let S : ℝ := (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ
    set a := ‖x.1‖
    set b := ‖x.2‖
    set F := ‖iteratedFDeriv ℝ i φ.toFun x.1‖
    set G := ‖iteratedFDeriv ℝ (l - i) ψ.toFun x.2‖
    have ha_nn : 0 ≤ a := norm_nonneg _
    have hb_nn : 0 ≤ b := norm_nonneg _
    have hF_nn : 0 ≤ F := norm_nonneg _
    have hG_nn : 0 ≤ G := norm_nonneg _
    have hφ1 : a ^ k * F ≤ SchwartzMap.seminorm ℂ k i φ :=
      SchwartzMap.le_seminorm ℂ k i φ x.1
    have hψ1 : G ≤ S := by
      have hψ0 : G ≤ SchwartzMap.seminorm ℂ 0 (l - i) ψ := by
        have h := SchwartzMap.le_seminorm ℂ 0 (l - i) ψ x.2
        simp only [pow_zero, one_mul] at h
        exact h
      have hmem : ((0, l - i) : ℕ × ℕ) ∈ s :=
        Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      exact hψ0.trans
        ((Finset.le_sup
          (f := schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) hmem) ψ)
    have hφ2 : F ≤ SchwartzMap.seminorm ℂ 0 i φ := by
      have h := SchwartzMap.le_seminorm ℂ 0 i φ x.1
      simp only [pow_zero, one_mul] at h
      exact h
    have hψ2 : b ^ k * G ≤ S := by
      have hψk : b ^ k * G ≤ SchwartzMap.seminorm ℂ k (l - i) ψ :=
        SchwartzMap.le_seminorm ℂ k (l - i) ψ x.2
      have hmem : ((k, l - i) : ℕ × ℕ) ∈ s :=
        Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      exact hψk.trans
        ((Finset.le_sup
          (f := schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) hmem) ψ)
    have hprod1 : a ^ k * F * G ≤
        SchwartzMap.seminorm ℂ k i φ * S :=
      mul_le_mul hφ1 hψ1 hG_nn
        (le_trans (mul_nonneg (pow_nonneg ha_nn _) hF_nn) hφ1)
    have hprod2 : b ^ k * F * G ≤
        SchwartzMap.seminorm ℂ 0 i φ * S := by
      calc
        b ^ k * F * G = F * (b ^ k * G) := by ring
        _ ≤ SchwartzMap.seminorm ℂ 0 i φ * S :=
          mul_le_mul hφ2 hψ2 (mul_nonneg (pow_nonneg hb_nn _) hG_nn)
            (le_trans hF_nn hφ2)
    have hchoose_nn : (0 : ℝ) ≤ ↑(l.choose i) := Nat.cast_nonneg _
    calc
      ‖x‖ ^ k * (↑(l.choose i) * F * G)
          ≤ ((2 : ℝ) ^ k * (a ^ k + b ^ k)) * (↑(l.choose i) * F * G) :=
        mul_le_mul_of_nonneg_right h_pow
          (mul_nonneg (mul_nonneg hchoose_nn hF_nn) hG_nn)
      _ = (2 : ℝ) ^ k * (↑(l.choose i) * (a ^ k * F * G + b ^ k * F * G)) := by
        ring
      _ ≤ (2 : ℝ) ^ k * (↑(l.choose i) *
          ((SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ 0 i φ) * S)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
        apply mul_le_mul_of_nonneg_left _ hchoose_nn
        calc
          a ^ k * F * G + b ^ k * F * G ≤
              SchwartzMap.seminorm ℂ k i φ * S +
                SchwartzMap.seminorm ℂ 0 i φ * S :=
            add_le_add hprod1 hprod2
          _ = (SchwartzMap.seminorm ℂ k i φ +
                SchwartzMap.seminorm ℂ 0 i φ) * S := by
            ring
  have hraw :
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => φ y.1 * ψ y.2) x‖ ≤
      (2 : ℝ) ^ k * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
        ((SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ 0 i φ) *
          (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ) := by
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => φ y.1 * ψ y.2) x‖
          ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (l + 1),
            ↑(l.choose i) * ‖iteratedFDeriv ℝ i (φ.toFun ∘ Prod.fst) x‖ *
            ‖iteratedFDeriv ℝ (l - i) (ψ.toFun ∘ Prod.snd) x‖ := by
        gcongr
        exact hLeib
      _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (l + 1),
            ↑(l.choose i) * ‖iteratedFDeriv ℝ i φ.toFun x.1‖ *
            ‖iteratedFDeriv ℝ (l - i) ψ.toFun x.2‖ := by
        gcongr with i hi
        · exact (hcf i x).trans le_rfl
        · exact (hcg (l - i) x).trans le_rfl
      _ = ∑ i ∈ Finset.range (l + 1),
            ‖x‖ ^ k * (↑(l.choose i) * ‖iteratedFDeriv ℝ i φ.toFun x.1‖ *
            ‖iteratedFDeriv ℝ (l - i) ψ.toFun x.2‖) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (l + 1),
          (2 : ℝ) ^ k * (↑(l.choose i) *
            ((SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ 0 i φ) *
              (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ)) :=
        Finset.sum_le_sum h_term
      _ = _ := by rw [← Finset.mul_sum]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => φ y.1 * ψ y.2) x‖
        ≤ (2 : ℝ) ^ k * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
          ((SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ 0 i φ) *
            (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ) := hraw
    _ = C * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ := by
      simp [C, mul_assoc, Finset.sum_mul]

@[simp]
theorem schwartzTensorProduct₂CLMLeft_apply {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (z : ComplexChartSpace m) (t : Fin m → ℝ) :
    schwartzTensorProduct₂CLMLeft φ ψ (z, t) = φ z * ψ t := rfl

theorem schwartzTensorProduct₂CLMLeft_eq {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    schwartzTensorProduct₂CLMLeft φ ψ =
      schwartzTensorProduct₂ φ ψ := by
  ext p
  rfl

/-- Partial evaluation of a triple mixed Schwartz test at a fixed last real
parameter, as a continuous linear map in the ambient triple test. -/
def schwartzPartialEval₂CLM {m : ℕ} (a : Fin m → ℝ) :
    SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ →L[ℂ]
        SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ := by
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let P := Fin m → ℝ
  let g : B → B × P := fun b => (b, a)
  have hg : g.HasTemperateGrowth := by
    have hconst : Function.HasTemperateGrowth
        (fun _ : B => ((0, a) : B × P)) :=
      Function.HasTemperateGrowth.const _
    have hlin : Function.HasTemperateGrowth
        (⇑(ContinuousLinearMap.inl ℝ B P)) :=
      (ContinuousLinearMap.inl ℝ B P).hasTemperateGrowth
    convert hlin.add hconst using 1
    ext b <;> simp [g, B, P, ContinuousLinearMap.inl_apply, Prod.add_def]
  have hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ b, ‖b‖ ≤ C * (1 + ‖g b‖) ^ k := by
    refine ⟨1, 1, ?_⟩
    intro b
    have hb : ‖b‖ ≤ ‖g b‖ := by
      simp [g, Prod.norm_def]
    have hnonneg : 0 ≤ ‖g b‖ := norm_nonneg _
    nlinarith
  exact SchwartzMap.compCLM (𝕜 := ℂ) (g := g) hg hg_upper

@[simp]
theorem schwartzPartialEval₂CLM_apply {m : ℕ}
    (a : Fin m → ℝ)
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ)
    (z : ComplexChartSpace m) (t : Fin m → ℝ) :
    schwartzPartialEval₂CLM a A (z, t) = A ((z, t), a) := rfl

/-- The fixed-last-variable partial evaluations vary continuously in the last
real parameter. -/
theorem continuous_schwartzPartialEval₂CLM {m : ℕ}
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ) :
    Continuous fun a : Fin m → ℝ => schwartzPartialEval₂CLM a A := by
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let P := Fin m → ℝ
  let Acomm : SchwartzMap (P × B) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.prodComm ℝ P B)) A
  have hcont : Continuous fun a : P => schwartzPartialEval₁ Acomm a :=
    continuous_schwartzPartialEval₁ Acomm
  have hfun :
      (fun a : P => schwartzPartialEval₂CLM a A) =
        fun a : P => schwartzPartialEval₁ Acomm a := by
    funext a
    ext b
    rcases b with ⟨z, t⟩
    rfl
  simpa [B, P, hfun]

/-- Singleton seminorm decay for fixed-last-variable partial evaluation.

The two source seminorms control the origin and the radial tail in the fixed
parameter. -/
private theorem schwartzPartialEval₂CLM_seminorm_decay_one_bound {m : ℕ}
    (k l : ℕ) :
    let μ : Measure (Fin m → ℝ) := volume
    let N := μ.integrablePower
    let s : Finset (ℕ × ℕ) := {((k, l) : ℕ × ℕ), (k + N, l)}
    let C : ℝ := (2 : ℝ) ^ N * 2
    0 ≤ C ∧
      ∀ (A : SchwartzMap
          ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ)
        (a : Fin m → ℝ),
        SchwartzMap.seminorm ℂ k l (schwartzPartialEval₂CLM a A) ≤
          C * (1 + ‖a‖) ^ (-(N : ℝ)) *
            s.sup (schwartzSeminormFamily ℂ
              ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ) A := by
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let P := Fin m → ℝ
  let μ : Measure P := volume
  let N := μ.integrablePower
  let s : Finset (ℕ × ℕ) := {((k, l) : ℕ × ℕ), (k + N, l)}
  let C : ℝ := (2 : ℝ) ^ N * 2
  change 0 ≤ C ∧
      ∀ (A : SchwartzMap (B × P) ℂ) (a : P),
        SchwartzMap.seminorm ℂ k l (schwartzPartialEval₂CLM a A) ≤
          C * (1 + ‖a‖) ^ (-(N : ℝ)) *
            s.sup (schwartzSeminormFamily ℂ (B × P) ℂ) A
  refine ⟨by positivity, ?_⟩
  intro A a
  let S : ℝ := s.sup (schwartzSeminormFamily ℂ (B × P) ℂ) A
  let r : ℝ := (1 + ‖a‖) ^ (-(N : ℝ))
  have hS_nonneg : 0 ≤ S := apply_nonneg _ _
  have hr_nonneg : 0 ≤ r := by positivity
  have hC₁_le : SchwartzMap.seminorm ℂ k l A ≤ S := by
    have hmem : ((k, l) : ℕ × ℕ) ∈ s := by simp [s]
    exact (show
      (schwartzSeminormFamily ℂ (B × P) ℂ ((k, l) : ℕ × ℕ)) A ≤ S from
        (Finset.le_sup (f := schwartzSeminormFamily ℂ (B × P) ℂ) hmem) A)
  have hC₂_le : SchwartzMap.seminorm ℂ (k + N) l A ≤ S := by
    have hmem : ((k + N, l) : ℕ × ℕ) ∈ s := by simp [s]
    exact (show
      (schwartzSeminormFamily ℂ (B × P) ℂ ((k + N, l) : ℕ × ℕ)) A ≤ S from
        (Finset.le_sup (f := schwartzSeminormFamily ℂ (B × P) ℂ) hmem) A)
  apply SchwartzMap.seminorm_le_bound ℂ k l _ (mul_nonneg (mul_nonneg (by positivity) hr_nonneg) hS_nonneg)
  intro b
  let D : ℝ :=
    ‖iteratedFDeriv ℝ l (fun x => (schwartzPartialEval₂CLM a A) x) b‖
  let E : ℝ := ‖iteratedFDeriv ℝ l (⇑A) (b, a)‖
  have hD_nonneg : 0 ≤ D := norm_nonneg _
  have hE_nonneg : 0 ≤ E := norm_nonneg _
  have hderiv : D ≤ E := by
    simpa [D, E, schwartzPartialEval₂CLM_apply] using
      norm_iteratedFDeriv_partialEval_le (f := A) (y := a) (l := l) (x := b)
  have hb_norm : ‖b‖ ≤ ‖(b, a)‖ := by
    rw [Prod.norm_def]
    exact le_max_left ‖b‖ ‖a‖
  have ha_norm : ‖a‖ ≤ ‖(b, a)‖ := by
    rw [Prod.norm_def]
    exact le_max_right ‖b‖ ‖a‖
  have h₁ : ‖b‖ ^ k * D ≤ SchwartzMap.seminorm ℂ k l A := by
    calc
      ‖b‖ ^ k * D ≤ ‖b‖ ^ k * E :=
        mul_le_mul_of_nonneg_left hderiv (pow_nonneg (norm_nonneg _) _)
      _ ≤ ‖(b, a)‖ ^ k * E := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hb_norm _) hE_nonneg
      _ ≤ SchwartzMap.seminorm ℂ k l A :=
        SchwartzMap.le_seminorm ℂ k l A (b, a)
  have hpow_prod : ‖a‖ ^ N * ‖b‖ ^ k ≤ ‖(b, a)‖ ^ (k + N) := by
    have ha_pow : ‖a‖ ^ N ≤ ‖(b, a)‖ ^ N :=
      pow_le_pow_left₀ (norm_nonneg _) ha_norm _
    have hb_pow : ‖b‖ ^ k ≤ ‖(b, a)‖ ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) hb_norm _
    calc
      ‖a‖ ^ N * ‖b‖ ^ k ≤ ‖(b, a)‖ ^ N * ‖(b, a)‖ ^ k :=
        mul_le_mul ha_pow hb_pow (pow_nonneg (norm_nonneg _) _)
          (pow_nonneg (norm_nonneg _) _)
      _ = ‖(b, a)‖ ^ (N + k) := by rw [pow_add]
      _ = ‖(b, a)‖ ^ (k + N) := by rw [add_comm]
  have h₂ : ‖a‖ ^ N * (‖b‖ ^ k * D) ≤
      SchwartzMap.seminorm ℂ (k + N) l A := by
    calc
      ‖a‖ ^ N * (‖b‖ ^ k * D) =
          (‖a‖ ^ N * ‖b‖ ^ k) * D := by ring
      _ ≤ ‖(b, a)‖ ^ (k + N) * E :=
        mul_le_mul hpow_prod hderiv hD_nonneg
          (pow_nonneg (norm_nonneg _) _)
      _ ≤ SchwartzMap.seminorm ℂ (k + N) l A :=
        SchwartzMap.le_seminorm ℂ (k + N) l A (b, a)
  have hmain := pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := N)
    (x := ‖a‖) (f := ‖b‖ ^ k * D)
    (C₁ := SchwartzMap.seminorm ℂ k l A)
    (C₂ := SchwartzMap.seminorm ℂ (k + N) l A)
    (norm_nonneg _) (mul_nonneg (pow_nonneg (norm_nonneg _) _) hD_nonneg)
    h₁ (by simpa using h₂)
  have hsum_le : SchwartzMap.seminorm ℂ k l A +
      SchwartzMap.seminorm ℂ (k + N) l A ≤ 2 * S := by
    linarith
  calc
    ‖b‖ ^ k *
        ‖iteratedFDeriv ℝ l (fun x => (schwartzPartialEval₂CLM a A) x) b‖
        = ‖b‖ ^ k * D := rfl
    _ ≤ (2 : ℝ) ^ N *
          (SchwartzMap.seminorm ℂ k l A +
            SchwartzMap.seminorm ℂ (k + N) l A) * r := by
      simpa [r] using hmain
    _ ≤ (2 : ℝ) ^ N * (2 * S) * r := by
      gcongr
    _ = C * r * S := by
      ring

/-- Singleton finite-seminorm decay for fixed-last-variable partial
evaluation. -/
theorem schwartzPartialEval₂CLM_seminorm_decay_one {m : ℕ} (k l : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : SchwartzMap
          ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ)
        (a : Fin m → ℝ),
        SchwartzMap.seminorm ℂ k l (schwartzPartialEval₂CLM a A) ≤
          C * (1 + ‖a‖) ^
              (-((volume : Measure (Fin m → ℝ)).integrablePower : ℝ)) *
            s.sup (schwartzSeminormFamily ℂ
              ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ) A := by
  let μ : Measure (Fin m → ℝ) := volume
  let N := μ.integrablePower
  let s : Finset (ℕ × ℕ) := {((k, l) : ℕ × ℕ), (k + N, l)}
  let C : ℝ := (2 : ℝ) ^ N * 2
  refine ⟨s, C, ?_, ?_⟩
  · exact (schwartzPartialEval₂CLM_seminorm_decay_one_bound (m := m) k l).1
  · intro A a
    simpa [μ, N, s, C] using
      (schwartzPartialEval₂CLM_seminorm_decay_one_bound (m := m) k l).2 A a

/-- Finite-family seminorm decay for fixed-last-variable partial evaluation. -/
theorem schwartzPartialEval₂CLM_finsetSeminorm_decay {m : ℕ}
    (s0 : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : SchwartzMap
          ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ)
        (a : Fin m → ℝ),
        s0.sup (schwartzSeminormFamily ℂ
            (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
            (schwartzPartialEval₂CLM a A) ≤
          C * (1 + ‖a‖) ^
              (-((volume : Measure (Fin m → ℝ)).integrablePower : ℝ)) *
            s.sup (schwartzSeminormFamily ℂ
              ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ) A := by
  let μ : Measure (Fin m → ℝ) := volume
  let N := μ.integrablePower
  let source : ℕ × ℕ → Finset (ℕ × ℕ) :=
    fun i => {i, (i.1 + N, i.2)}
  let s : Finset (ℕ × ℕ) := s0.biUnion source
  let C0 : ℝ := (2 : ℝ) ^ N * 2
  let C : ℝ := ∑ i ∈ s0, C0
  refine ⟨s, C, ?_, ?_⟩
  · exact Finset.sum_nonneg fun _ _ => by positivity
  intro A a
  let S : ℝ := s.sup (schwartzSeminormFamily ℂ
    ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ) A
  let r : ℝ := (1 + ‖a‖) ^ (-(N : ℝ))
  have hS_nonneg : 0 ≤ S := apply_nonneg _ _
  have hr_nonneg : 0 ≤ r := by positivity
  have htarget_nonneg : 0 ≤ C * r * S :=
    mul_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ => by positivity) hr_nonneg) hS_nonneg
  apply Seminorm.finset_sup_apply_le
  · simpa [μ, N, s, C, S, r, mul_assoc] using htarget_nonneg
  intro i hi
  rcases i with ⟨k, l⟩
  let sOne : Finset (ℕ × ℕ) := source (k, l)
  let SOne : ℝ := sOne.sup (schwartzSeminormFamily ℂ
    ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ) A
  have hOne := (schwartzPartialEval₂CLM_seminorm_decay_one_bound (m := m) k l).2 A a
  have hSOne_le : SOne ≤ S := by
    apply Seminorm.finset_sup_apply_le
    · exact hS_nonneg
    intro j hj
    exact (Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily ℂ
        ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ)
      (s := s) (x := A)
      (by
        exact Finset.mem_biUnion.mpr ⟨(k, l), hi, hj⟩))
  have hC0_nonneg : 0 ≤ C0 := by positivity
  have hC0_le_C : C0 ≤ C := by
    simpa [C] using Finset.single_le_sum (fun _ _ => hC0_nonneg) hi
  calc
    (schwartzSeminormFamily ℂ (ComplexChartSpace m × (Fin m → ℝ)) ℂ (k, l))
        (schwartzPartialEval₂CLM a A)
        ≤ C0 * r * SOne := by
      simpa [μ, N, C0, sOne, SOne, source, r] using hOne
    _ ≤ C0 * r * S := by
      gcongr
    _ ≤ C * r * S := by
      gcongr

end SCV
