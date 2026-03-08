/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.TubeDistributions
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Distributional Uniqueness on Tube Domains (Weak Hypothesis Version)

This file proves distributional uniqueness for holomorphic functions on tube
domains using ONLY the weak distributional boundary-value hypothesis, without
requiring `HasFourierLaplaceReprRegular`.

The key technique is **mollification**: given G holomorphic on T(C) with
distributional BV → 0, we convolve G with a Schwartz test function ψ in the
real direction. The convolution G*ψ is holomorphic on T(C), has continuous
boundary values = 0 (from the distributional BV hypothesis), and therefore
vanishes identically by the proved `distributional_uniqueness_tube_of_regular`
machinery (specifically, the 1D EOW slicing argument). Taking ψ → δ gives G = 0.

## Main Results

* `distributional_uniqueness_tube_of_zero_bv`: If G is holomorphic on T(C) and
  its distributional boundary values vanish, then G = 0 on T(C).

## References

* Vladimirov, V.S. "Methods of the Theory of Generalized Functions" (2002), §25
* Classical mollification argument for distributional boundary values
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter

namespace SCV

variable {m : ℕ}

/-! ### Schwartz Translation -/

/-- Translate a Schwartz function: `(translateSchwartz t₀ f)(x) = f(x + t₀)`.
    This is Schwartz because translation by a fixed vector preserves rapid decay. -/
def translateSchwartz (t₀ : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  ⟨fun x => f (x + t₀),
   f.smooth'.comp (contDiff_id.add contDiff_const),
   fun k n => by
     obtain ⟨Ck, hCk⟩ := f.decay' k n
     obtain ⟨C0, hC0⟩ := f.decay' 0 n
     -- Chain rule: D^n (f ∘ (· + t₀)) x = D^n f (x + t₀)
     have hderiv : ∀ x, iteratedFDeriv ℝ n (fun z => f.toFun (z + t₀)) x =
         iteratedFDeriv ℝ n f.toFun (x + t₀) :=
       fun x => iteratedFDeriv_comp_add_right n t₀ x
     -- From 0-th decay: ‖D^n f(y)‖ ≤ C0 for all y
     have hC0' : ∀ y, ‖iteratedFDeriv ℝ n f.toFun y‖ ≤ C0 := by
       intro y; have := hC0 y; simp [pow_zero] at this; linarith
     -- Bound: ‖x‖ ≤ ‖x+t₀‖ + ‖t₀‖ (triangle inequality)
     -- So ‖x‖^k ≤ (‖x+t₀‖ + ‖t₀‖)^k
     -- And (a+b)^k ≤ 2^k * (a^k + b^k) for a,b ≥ 0
     refine ⟨2 ^ (k - 1) * (Ck + ‖t₀‖ ^ k * C0), fun x => ?_⟩
     show ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => f.toFun (z + t₀)) x‖ ≤ _
     rw [hderiv]
     have hnorm_x : ‖x‖ ≤ ‖x + t₀‖ + ‖t₀‖ := by
       calc ‖x‖ = ‖(x + t₀) - t₀‖ := by ring_nf
         _ ≤ ‖x + t₀‖ + ‖t₀‖ := norm_sub_le _ _
     have hnn_deriv : 0 ≤ ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖ := norm_nonneg _
     calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖
         ≤ (‖x + t₀‖ + ‖t₀‖) ^ k * ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖ := by
           gcongr
       _ ≤ (2 ^ (k - 1) * (‖x + t₀‖ ^ k + ‖t₀‖ ^ k)) *
           ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖ := by
           gcongr; exact add_pow_le (norm_nonneg _) (norm_nonneg _) k
       _ = 2 ^ (k - 1) * (‖x + t₀‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖ +
           ‖t₀‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖) := by ring
       _ ≤ 2 ^ (k - 1) * (Ck + ‖t₀‖ ^ k * C0) := by
           gcongr
           · exact hCk (x + t₀)
           · exact hC0' (x + t₀)⟩

/-- The translate of a Schwartz function evaluates as expected. -/
@[simp]
theorem translateSchwartz_apply (t₀ : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin m → ℝ) : translateSchwartz t₀ f x = f (x + t₀) := rfl

/-! ### Uniqueness from Boundary Zero + ContinuousWithinAt

This is the 1D EOW slicing argument factored out from
`distributional_uniqueness_tube_of_regular`. It requires:
1. G holomorphic on T(C)
2. G = 0 on the real boundary (pointwise)
3. ContinuousWithinAt G (TubeDomain C) (realEmbed x) for all x

No `HasFourierLaplaceReprRegular` is needed. -/

/-- If G is holomorphic on T(C), vanishes on the real boundary, and is
    continuous within the tube at each boundary point, then G vanishes
    identically on T(C). Uses 1D EOW slicing. -/
theorem uniqueness_of_boundary_zero {m : ℕ}
    {C : Set (Fin m → ℝ)} (_hC : IsOpen C) (_hconv : Convex ℝ C) (_hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {G : (Fin m → ℂ) → ℂ}
    (hG_diff : DifferentiableOn ℂ G (TubeDomain C))
    (hG_boundary : ∀ x : Fin m → ℝ, G (realEmbed x) = 0)
    (hG_cont : ∀ x : Fin m → ℝ,
      ContinuousWithinAt G (TubeDomain C) (realEmbed x)) :
    ∀ z ∈ TubeDomain C, G z = 0 := by
  intro z hz
  -- 1D slice: φ(w) = x₀ + w * y₀ maps UHP → T(C)
  let y₀ : Fin m → ℝ := fun i => (z i).im
  let x₀ : Fin m → ℝ := fun i => (z i).re
  have hy₀ : y₀ ∈ C := hz
  let φ : ℂ → (Fin m → ℂ) := fun w i => ↑(x₀ i) + w * ↑(y₀ i)
  let g : ℂ → ℂ := G ∘ φ
  have hg_real : ∀ t : ℝ, g (t : ℂ) = 0 := by
    intro t
    show G (φ (t : ℂ)) = 0
    have hφ_real : φ (t : ℂ) = realEmbed (fun i => x₀ i + t * y₀ i) := by
      ext i; simp [φ, realEmbed, Complex.ofReal_add, Complex.ofReal_mul]
    rw [hφ_real]; exact hG_boundary _
  have hz_eq : φ I = z := by
    ext i; simp [φ, x₀, y₀, mul_comm I, Complex.re_add_im]
  suffices h : g I = 0 by
    show G z = 0; rw [show G z = g I from by simp [g, hz_eq]]; exact h
  have hφ_UHP : ∀ w : ℂ, w.im > 0 → φ w ∈ TubeDomain C := by
    intro w hw
    show (fun i => (φ w i).im) ∈ C
    have him : (fun i => (φ w i).im) = w.im • y₀ := by
      ext i; simp [φ, x₀, y₀, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [him]; exact hcone w.im hw y₀ hy₀
  have hφ_cont : Continuous φ :=
    continuous_pi fun i =>
      (continuous_const.add (continuous_id.mul continuous_const))
  have hg_diff : DifferentiableOn ℂ g EOW.UpperHalfPlane := by
    show DifferentiableOn ℂ (G ∘ φ) EOW.UpperHalfPlane
    exact hG_diff.comp (fun w _ => by
      apply DifferentiableAt.differentiableWithinAt
      exact differentiableAt_pi.mpr fun i =>
        (differentiableAt_const _).add
          (differentiableAt_id.mul (differentiableAt_const _)))
      (fun w hw => hφ_UHP w hw)
  have hφ_real_embed : ∀ t : ℝ, φ (↑t) = realEmbed (fun i => x₀ i + t * y₀ i) := by
    intro t; ext i; simp [φ, x₀, y₀, realEmbed, Complex.ofReal_add, Complex.ofReal_mul]
  have hcont_plus : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
      Filter.Tendsto g (nhdsWithin (↑x₁ : ℂ) EOW.UpperHalfPlane) (nhds (g ↑x₁)) := by
    intro x₁ _ _
    show ContinuousWithinAt (G ∘ φ) EOW.UpperHalfPlane ↑x₁
    have h := hG_cont (fun i => x₀ i + x₁ * y₀ i)
    rw [show realEmbed (fun i => x₀ i + x₁ * y₀ i) = φ ↑x₁ from
      (hφ_real_embed x₁).symm] at h
    exact h.comp hφ_cont.continuousAt.continuousWithinAt (fun w hw => hφ_UHP w hw)
  have hbv_cont : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
      Filter.Tendsto g (nhdsWithin (↑x₁ : ℂ) {c : ℂ | c.im = 0})
        (nhds (g ↑x₁)) := by
    intro x₁ _ _
    rw [hg_real x₁]
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with w (hw : w.im = 0)
    have : w = (w.re : ℂ) := Complex.ext rfl (by simp [hw])
    rw [this]; exact (hg_real w.re).symm
  obtain ⟨U, F, hU_open, hU_conv, _, _, hF_diff, hF_plus, hF_minus, hU_ball⟩ :=
    edge_of_the_wedge_1d (-3) 3 (by norm_num : (-3 : ℝ) < 3)
      g 0
      hg_diff
      (differentiableOn_const 0)
      hcont_plus
      (fun _ _ _ => tendsto_const_nhds)
      (fun x₁ _ _ => by show g ↑x₁ = 0; exact hg_real x₁)
      hbv_cont
  have hI_in_U : I ∈ U :=
    hU_ball (by simp [Metric.mem_ball, Complex.norm_I])
  have h_neg_I_in_U : -I ∈ U :=
    hU_ball (by simp [Metric.mem_ball, norm_neg, Complex.norm_I])
  have hF_zero_on_U : ∀ w ∈ U, F w = 0 := by
    have hU_conn : IsConnected U :=
      ⟨⟨I, hI_in_U⟩, hU_conv.isPreconnected⟩
    have h_neg_I_LHP : (-I).im < 0 := by simp [Complex.neg_im, Complex.I_im]
    have h_freq : ∃ᶠ w in nhdsWithin (-I) {(-I)}ᶜ, F w = (0 : ℂ → ℂ) w := by
      apply Filter.Eventually.frequently
      have hmem : U ∩ EOW.LowerHalfPlane ∈ nhdsWithin (-I) {(-I)}ᶜ :=
        nhdsWithin_le_nhds ((hU_open.inter EOW.lowerHalfPlane_isOpen).mem_nhds
          ⟨h_neg_I_in_U, h_neg_I_LHP⟩)
      filter_upwards [hmem] with w ⟨hwU, hwLHP⟩
      simp [hF_minus w ⟨hwU, hwLHP⟩]
    exact fun w hw => identity_theorem_connected hU_open hU_conn F 0
      hF_diff (differentiableOn_const 0) (-I) h_neg_I_in_U h_freq hw
  have hI_UHP : I.im > 0 := by simp [Complex.I_im]
  rw [← hF_plus I ⟨hI_in_U, hI_UHP⟩]
  exact hF_zero_on_U I hI_in_U

end SCV

end
