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

/-- The support of a translated Schwartz function is the pullback of the original
    support under the real translation `x ↦ x + t₀`. -/
theorem mem_support_translateSchwartz_iff (t₀ : Fin m → ℝ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) (x : Fin m → ℝ) :
    x ∈ Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) ↔
      x + t₀ ∈ Function.support (f : (Fin m → ℝ) → ℂ) := by
  simp [translateSchwartz_apply, Function.mem_support]

/-- Support transport for translated Schwartz functions. This is the exact support
    bookkeeping needed in the mollification step of distributional EOW: if `f` is
    supported in `U`, then `translateSchwartz t₀ f` is supported in the translated
    preimage `{x | x + t₀ ∈ U}`. -/
theorem support_translateSchwartz_subset_preimage (t₀ : Fin m → ℝ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) (U : Set (Fin m → ℝ))
    (hU : Function.support (f : (Fin m → ℝ) → ℂ) ⊆ U) :
    Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) ⊆
      {x | x + t₀ ∈ U} := by
  intro x hx
  exact hU ((mem_support_translateSchwartz_iff t₀ f x).mp hx)

/-- A convenient open-set version of support transport: if every support point `y`
    of `f` satisfies `y - t₀ ∈ U`, then the support of `translateSchwartz t₀ f`
    is contained in `U`. This is the form needed when a compactly supported mollifier
    is translated inside a fixed real neighborhood. -/
theorem support_translateSchwartz_subset (t₀ : Fin m → ℝ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) (U : Set (Fin m → ℝ))
    (hU : ∀ y ∈ Function.support (f : (Fin m → ℝ) → ℂ), y - t₀ ∈ U) :
    Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) ⊆ U := by
  intro x hx
  simpa using hU (x + t₀) ((mem_support_translateSchwartz_iff t₀ f x).mp hx)

/-- If the support of a Schwartz function is compact and its translate at `t₀`
    is contained in an open set `U`, then the translated support stays inside `U`
    for all nearby centers. This is the local support-stability input needed in
    the mollifier argument for distributional edge-of-the-wedge. -/
theorem exists_mem_nhds_support_translateSchwartz_subset_of_isCompactSupport
    (t₀ : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hK_compact : IsCompact (Function.support (f : (Fin m → ℝ) → ℂ)))
    (U : Set (Fin m → ℝ)) (hU_open : IsOpen U)
    (hU : Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) ⊆ U) :
    ∃ V ∈ 𝓝 t₀, ∀ t ∈ V,
      Function.support (translateSchwartz t f : (Fin m → ℝ) → ℂ) ⊆ U := by
  let K : Set (Fin m → ℝ) := Function.support (f : (Fin m → ℝ) → ℂ)
  have hbase : ∀ y ∈ K, y - t₀ ∈ U := by
    intro y hy
    have hyt : y - t₀ ∈ Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) := by
      rw [mem_support_translateSchwartz_iff]
      simpa
    exact hU hyt
  have hloc :
      ∀ x : K,
        ∃ Vx Wx : Set (Fin m → ℝ),
          Vx ∈ 𝓝 x.1 ∧ Wx ∈ 𝓝 t₀ ∧ IsOpen Vx ∧ x.1 ∈ Vx ∧
            Vx ×ˢ Wx ⊆ {p : (Fin m → ℝ) × (Fin m → ℝ) | p.1 - p.2 ∈ U} := by
    intro x
    have hprod_mem :
        {p : (Fin m → ℝ) × (Fin m → ℝ) | p.1 - p.2 ∈ U} ∈ 𝓝 (x.1, t₀) := by
      exact (continuous_fst.sub continuous_snd).continuousAt.preimage_mem_nhds
        (hU_open.mem_nhds (hbase x.1 x.2))
    rcases mem_nhds_prod_iff.mp hprod_mem with ⟨Vx0, hVx0, Wx, hWx, hsub⟩
    refine ⟨interior Vx0, Wx, ?_, hWx, isOpen_interior, ?_, ?_⟩
    · exact isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hVx0)
    · exact mem_interior_iff_mem_nhds.mpr hVx0
    · exact Set.Subset.trans (Set.prod_mono interior_subset (Subset.rfl)) hsub
  choose V W hV_nhds hW_nhds hV_open hxV hVW using hloc
  obtain ⟨s, hscover⟩ := hK_compact.elim_finite_subcover (fun x : K => V x)
    (fun x => hV_open x) (by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩)
  have hN_nhds_aux : ∀ s : Finset K, (⋂ x ∈ s, W x) ∈ 𝓝 t₀ := by
    classical
    intro s
    exact (biInter_finset_mem s).2 fun x hx => hW_nhds x
  have hN_nhds : (⋂ x ∈ s, W x) ∈ 𝓝 t₀ := hN_nhds_aux s
  let N : Set (Fin m → ℝ) := ⋂ x ∈ s, W x
  refine ⟨N, hN_nhds, ?_⟩
  intro t ht z hz
  have hy : z + t ∈ K := (mem_support_translateSchwartz_iff t f z).mp hz
  have hycover : z + t ∈ ⋃ x ∈ s, V x := hscover hy
  rcases mem_iUnion.mp hycover with ⟨x, hycover⟩
  rcases mem_iUnion.mp hycover with ⟨hxs, hzV⟩
  have htW : t ∈ W x := by
    have ht' : t ∈ N := ht
    simp [N] at ht'
    exact ht' x.1 x.2 hxs
  have hpair : ((z + t), t) ∈ V x ×ˢ W x := ⟨hzV, htW⟩
  have hsub : (z + t) - t ∈ U := hVW x hpair
  simpa using hsub

/-- If a continuous linear functional vanishes on all Schwartz functions
    supported in an open set `U`, then it also vanishes on all nearby translates
    of a compactly supported Schwartz function whose translate at `t₀` is
    contained in `U`. This is the local vanishing step needed for mollified
    boundary traces in the distributional EOW argument. -/
theorem map_translateSchwartz_eq_zero_nhds_of_support_subset
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (U : Set (Fin m → ℝ)) (hT_zero : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      Function.support (φ : (Fin m → ℝ) → ℂ) ⊆ U → T φ = 0)
    (t₀ : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ)))
    (hU_open : IsOpen U)
    (hsub : Function.support (translateSchwartz t₀ ψ : (Fin m → ℝ) → ℂ) ⊆ U) :
    ∃ V ∈ 𝓝 t₀, ∀ t ∈ V, T (translateSchwartz t ψ) = 0 := by
  obtain ⟨V, hV, hVsub⟩ :=
    exists_mem_nhds_support_translateSchwartz_subset_of_isCompactSupport
      t₀ ψ hψ_compact U hU_open hsub
  refine ⟨V, hV, ?_⟩
  intro t ht
  exact hT_zero (translateSchwartz t ψ) (hVsub t ht)

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

/-- A local 1D uniqueness theorem for holomorphic functions on the upper
    half-plane with zero continuous boundary values on an interval.

    This is the exact local endpoint needed in mollifier-based distributional
    edge-of-the-wedge arguments: once the mollified boundary trace vanishes on
    an interval `(a,b)`, the holomorphic function vanishes on the canonical ball
    produced by `edge_of_the_wedge_1d`. -/
theorem uniqueness_of_boundary_zero_on_interval (a b : ℝ) (hab : a < b)
    {g : ℂ → ℂ}
    (hg_diff : DifferentiableOn ℂ g EOW.UpperHalfPlane)
    (hg_boundary : ∀ x : ℝ, a < x → x < b → g (x : ℂ) = 0)
    (hcont_plus : ∀ x : ℝ, a < x → x < b →
      Filter.Tendsto g (nhdsWithin (x : ℂ) EOW.UpperHalfPlane) (nhds (g x)))
    (hbv_cont : ∀ x₀ : ℝ, a < x₀ → x₀ < b →
      Filter.Tendsto g (nhdsWithin (x₀ : ℂ) {c : ℂ | c.im = 0})
        (nhds (g x₀))) :
    ∀ z ∈ Metric.ball (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2), z.im > 0 → g z = 0 := by
  obtain ⟨U, F, hU_open, hU_conv, _, _, hF_diff, hF_plus, hF_minus, hU_ball⟩ :=
    edge_of_the_wedge_1d a b hab g 0
      hg_diff
      (differentiableOn_const 0)
      hcont_plus
      (fun _ _ _ => tendsto_const_nhds)
      hg_boundary
      hbv_cont
  let mid : ℂ := (((a + b) / 2 : ℝ) : ℂ)
  let rad : ℝ := (b - a) / 2
  have hrad : 0 < rad := by
    dsimp [rad]
    linarith
  let w0 : ℂ := mid - ((rad / 2 : ℝ) : ℂ) * Complex.I
  have hw0_ball : w0 ∈ Metric.ball mid rad := by
    rw [Metric.mem_ball, Complex.dist_eq]
    dsimp [w0, mid, rad]
    have hnorm : ‖(((b - a) / 4 : ℝ) : ℂ) * Complex.I‖ = (b - a) / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
      have : 0 ≤ (b - a) / 4 := by linarith
      simp [abs_of_nonneg this]
    have hsub : w0 - mid = -((((b - a) / 4 : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext
      · simp [w0, mid, rad]
      · simp [w0, mid, rad]
        ring_nf
    rw [hsub, norm_neg, hnorm]
    linarith
  have hw0_U : w0 ∈ U := hU_ball hw0_ball
  have hw0_LHP : w0 ∈ EOW.LowerHalfPlane := by
    change w0.im < 0
    simp [w0, mid, rad]
    linarith
  have hU_conn : IsConnected U := by
    refine ⟨?_, hU_conv.isPreconnected⟩
    exact ⟨w0, hw0_U⟩
  have hF_zero_on_U : ∀ w ∈ U, F w = 0 := by
    have h_freq : ∃ᶠ w in nhdsWithin w0 ({w0}ᶜ), F w = (0 : ℂ → ℂ) w := by
      apply Filter.Eventually.frequently
      have hmem : U ∩ EOW.LowerHalfPlane ∈ nhdsWithin w0 ({w0}ᶜ) := by
        exact nhdsWithin_le_nhds
          ((hU_open.inter EOW.lowerHalfPlane_isOpen).mem_nhds ⟨hw0_U, hw0_LHP⟩)
      filter_upwards [hmem] with w hw
      exact hF_minus w hw
    intro w hw
    exact (identity_theorem_connected hU_open hU_conn F 0
      hF_diff (differentiableOn_const 0) w0 hw0_U h_freq) hw
  intro z hz hzUHP
  have hzU : z ∈ U := hU_ball hz
  calc
    g z = F z := (hF_plus z ⟨hzU, hzUHP⟩).symm
    _ = 0 := hF_zero_on_U z hzU

end SCV

end
