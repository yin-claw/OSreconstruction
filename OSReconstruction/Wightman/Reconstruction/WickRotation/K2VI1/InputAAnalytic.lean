import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAFixedTime
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

open Complex MeasureTheory Filter Topology

namespace OSReconstruction

variable {d : ℕ}

/-- One-variable identity theorem used in the common-`G` center-independence
lane.

If a holomorphic function on the upper half-plane agrees almost everywhere with
a constant along the positive imaginary axis, then it is that constant
everywhere on the upper half-plane. The almost-everywhere hypothesis is first
upgraded to pointwise equality on `(0, ∞)` using continuity on the open ray,
and then the analytic identity theorem propagates that equality to the whole
connected domain. -/
theorem analytic_constant_of_ae_constant_on_imaginary_axis
    (f : ℂ → ℂ) (c : ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hae : ∀ᵐ t : ℝ ∂volume, 0 < t → f (Complex.I * (t : ℂ)) = c) :
    ∀ z : ℂ, 0 < z.im → f z = c := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hanalytic : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im} :=
    hf.analyticOnNhd hopen
  have hcont_axis : ContinuousOn (fun t : ℝ => f (Complex.I * (t : ℂ))) (Set.Ioi 0) := by
    refine hf.continuousOn.comp ?_ ?_
    · exact (continuous_const.mul Complex.continuous_ofReal).continuousOn
    · intro t ht
      simpa using ht
  have hae_axis :
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi 0)), f (Complex.I * (t : ℂ)) = c := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with t ht
    exact ht
  have haxis : ∀ t : ℝ, 0 < t → f (Complex.I * (t : ℂ)) = c := by
    have hEqOn :
        Set.EqOn (fun t : ℝ => f (Complex.I * (t : ℂ))) (fun _ : ℝ => c) (Set.Ioi 0) := by
      exact MeasureTheory.Measure.eqOn_open_of_ae_eq
        hae_axis isOpen_Ioi hcont_axis continuousOn_const
    intro t ht
    exact hEqOn ht
  have hI_mem : Complex.I ∈ {z : ℂ | 0 < z.im} := by simp [Complex.I_im]
  have hclosure : Complex.I ∈ closure ({z : ℂ | f z = c} \ {Complex.I}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨Complex.I * (((1 + ε / 2 : ℝ) : ℂ)), ?_, ?_⟩
    · constructor
      · have ht : 0 < 1 + ε / 2 := by linarith
        simpa using haxis (1 + ε / 2) ht
      · intro hEq
        have hEq0 : Complex.I * (((1 + ε / 2 : ℝ) : ℂ)) = Complex.I := by
          simpa using hEq
        have hEq1 : Complex.I * (((1 + ε / 2 : ℝ) : ℂ)) = Complex.I * (1 : ℂ) := by
          simpa using hEq0
        have hEq' : (((1 + ε / 2 : ℝ) : ℂ)) = 1 := by
          exact mul_left_cancel₀ Complex.I_ne_zero hEq1
        have hEq'' : (1 + ε / 2 : ℝ) = 1 := by
          exact Complex.ofReal_injective hEq'
        linarith
    · rw [Complex.dist_eq]
      have hhalf_lt : ε / 2 < ε := by linarith
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, Complex.norm_mul,
        Complex.norm_I, one_mul, abs_of_pos hε] using hhalf_lt
  have hconn : IsPreconnected {z : ℂ | 0 < z.im} :=
    (Complex.isConnected_of_upperHalfPlane (r := 0) (fun _ h => h)
      (fun z (h : 0 < z.im) => le_of_lt h)).isPreconnected
  have hf_eq_const : Set.EqOn f (fun _ : ℂ => c) {z : ℂ | 0 < z.im} := by
    exact hanalytic.eqOn_of_preconnected_of_mem_closure analyticOnNhd_const
      hconn hI_mem hclosure
  intro z hz
  exact hf_eq_const hz

/-- Fiberwise analytic propagation for flat positive-time-difference witnesses.

Fix a point `z` in the flattened tube and one block-time slot `i`. If the
corresponding one-variable fiber
`w ↦ G(update z (i,0) w)` agrees almost everywhere with a constant along the
positive imaginary axis, then that fiber is identically constant on the upper
half-plane. This is the reusable midpoint between the raw one-variable identity
theorem and the eventual center/diff-block independence statements for the
common witness. -/
theorem flatPositiveTimeDiffWitness_blockTime_constant_of_ae_imaginary_axis
    {k : ℕ}
    (G : (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (z : Fin (k * (d + 1)) → ℂ)
    (hz : z ∈ SCV.TubeDomain (FlatPositiveTimeDiffReal k d))
    (i : Fin k)
    (c : ℂ)
    (hae : ∀ᵐ t : ℝ ∂volume,
      0 < t →
        G (Function.update z (finProdFinEquiv (i, (0 : Fin (d + 1)))) (Complex.I * (t : ℂ))) = c) :
    ∀ w : ℂ, 0 < w.im →
      G (Function.update z (finProdFinEquiv (i, (0 : Fin (d + 1)))) w) = c := by
  rcases hG_holo with ⟨_hG_cont, hG_diff⟩
  exact
    analytic_constant_of_ae_constant_on_imaginary_axis
      (fun w =>
        G (Function.update z (finProdFinEquiv (i, (0 : Fin (d + 1)))) w))
      c
      (hG_diff z hz i)
      hae

end OSReconstruction
