import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SeedSlices
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.D1N2Invariants
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.D1N2LorentzInvariantRoute

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

variable {d : ℕ}

/-- Deferred geometric input (`d ≥ 2`): connectedness of the permutation seed set. -/
theorem blocker_isConnected_permSeedSet_dge2_nontrivial
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hd2 : 2 ≤ d)
    (hn2 : ¬ n ≤ 1) (hσ : σ ≠ 1) :
    IsConnected (permSeedSet (d := d) n σ) := by
  -- Remaining nontrivial branch (`n ≥ 2`, `σ ≠ 1`):
  -- closure route uses connectedness of forward-overlap index sets.
  sorry

/-- Deferred geometric input (`d ≥ 2`): connectedness of the permutation seed set. -/
theorem blocker_isConnected_permSeedSet_dge2
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hd2 : 2 ≤ d) :
    IsConnected (permSeedSet (d := d) n σ) := by
  by_cases hn : n ≤ 1
  · have hsub : Subsingleton (Fin n) := by
      refine ⟨?_⟩
      intro a b
      apply Fin.ext
      have ha0 : a.val = 0 := by omega
      have hb0 : b.val = 0 := by omega
      omega
    letI : Subsingleton (Fin n) := hsub
    have hσ : σ = 1 := Subsingleton.elim σ 1
    subst hσ
    have hset : permSeedSet (d := d) n (1 : Equiv.Perm (Fin n)) = ForwardTube d n := by
      ext z
      constructor
      · intro hz
        simpa [permSeedSet, PermutedForwardTube, permAct] using hz.2
      · intro hz
        exact ⟨forwardTube_subset_extendedTube hz,
          by simpa [PermutedForwardTube, permAct] using hz⟩
    simpa [hset] using
      (show IsConnected (ForwardTube d n) from
        ⟨forwardTube_nonempty (d := d) (n := n), forwardTube_convex.isPreconnected⟩)
  · -- Remaining nontrivial branch (`n ≥ 2`): geometric connectedness input.
    by_cases hσ : σ = 1
    · subst hσ
      have hset : permSeedSet (d := d) n (1 : Equiv.Perm (Fin n)) = ForwardTube d n := by
        ext z
        constructor
        · intro hz
          simpa [permSeedSet, PermutedForwardTube, permAct] using hz.2
        · intro hz
          exact ⟨forwardTube_subset_extendedTube hz,
            by simpa [PermutedForwardTube, permAct] using hz⟩
      simpa [hset] using
        (show IsConnected (ForwardTube d n) from
          ⟨forwardTube_nonempty (d := d) (n := n), forwardTube_convex.isPreconnected⟩)
    · -- Remaining nontrivial branch (`n ≥ 2`, `σ ≠ 1`):
      exact blocker_isConnected_permSeedSet_dge2_nontrivial
        (d := d) n σ hd2 hn hσ

/-- Deferred geometric input (`d = 1`): connectedness of the permutation seed set. -/
theorem blocker_isConnected_permSeedSet_d1_nontrivial
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hn2 : ¬ n ≤ 1) (hσ : σ ≠ 1) :
    IsConnected (permSeedSet (d := 1) n σ) := by
  -- Remaining nontrivial branch (`n ≥ 2`, `σ ≠ 1`).
  sorry

/-- Deferred geometric input (`d = 1`): connectedness of the permutation seed set. -/
theorem blocker_isConnected_permSeedSet_d1
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsConnected (permSeedSet (d := 1) n σ) := by
  by_cases hn : n ≤ 1
  · have hsub : Subsingleton (Fin n) := by
      refine ⟨?_⟩
      intro a b
      apply Fin.ext
      have ha0 : a.val = 0 := by omega
      have hb0 : b.val = 0 := by omega
      omega
    letI : Subsingleton (Fin n) := hsub
    have hσ : σ = 1 := Subsingleton.elim σ 1
    subst hσ
    have hset : permSeedSet (d := 1) n (1 : Equiv.Perm (Fin n)) = ForwardTube 1 n := by
      ext z
      constructor
      · intro hz
        simpa [permSeedSet, PermutedForwardTube, permAct] using hz.2
      · intro hz
        exact ⟨forwardTube_subset_extendedTube hz,
          by simpa [PermutedForwardTube, permAct] using hz⟩
    simpa [hset] using
      (show IsConnected (ForwardTube 1 n) from
        ⟨forwardTube_nonempty (d := 1) (n := n), forwardTube_convex.isPreconnected⟩)
  · by_cases hσ : σ = 1
    · subst hσ
      have hset : permSeedSet (d := 1) n (1 : Equiv.Perm (Fin n)) = ForwardTube 1 n := by
        ext z
        constructor
        · intro hz
          simpa [permSeedSet, PermutedForwardTube, permAct] using hz.2
        · intro hz
          exact ⟨forwardTube_subset_extendedTube hz,
            by simpa [PermutedForwardTube, permAct] using hz⟩
      simpa [hset] using
        (show IsConnected (ForwardTube 1 n) from
          ⟨forwardTube_nonempty (d := 1) (n := n), forwardTube_convex.isPreconnected⟩)
    · -- Remaining nontrivial branch (`n ≥ 2`, `σ ≠ 1`) is deferred.
      exact blocker_isConnected_permSeedSet_d1_nontrivial n σ hn hσ

/-- Nontrivial permutations of `Fin 2` are exactly the adjacent swap. -/
theorem fin2_perm_ne_one_eq_swap01 (τ : Equiv.Perm (Fin 2)) (hτ : τ ≠ 1) :
    τ = Equiv.swap (0 : Fin 2) 1 := by
  fin_cases τ <;> simp at hτ ⊢

/-- `d=1,n=2` invariant-function step A (deferred):
factorization of `F` on `FT` through Lorentz invariants `(Q₀,Q₁,P,S)`. -/
theorem blocker_d1N2InvariantFactorization_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ,
      ∀ z, z ∈ ForwardTube 1 2 →
        F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := by
  let _ := hF_bv
  let _ := hF_local
  let f : ℂ → ℂ → ℂ → ℂ → ℂ :=
    fun a b c s =>
      if h : ∃ z : Fin 2 → Fin (1 + 1) → ℂ,
          z ∈ ForwardTube 1 2 ∧ d1InvariantQuad z = (a, b, c, s)
      then F h.choose
      else 0
  refine ⟨f, ?_⟩
  intro z hz
  have hex :
      ∃ w : Fin 2 → Fin (1 + 1) → ℂ,
        w ∈ ForwardTube 1 2 ∧
          d1InvariantQuad w = (d1Q0 z, d1Q1 z, d1P01 z, d1S01 z) :=
    ⟨z, hz, by rfl⟩
  have hf_eq :
      f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) = F hex.choose := by
    simp [f, hex]
  have hchooseFT : hex.choose ∈ ForwardTube 1 2 := hex.choose_spec.1
  have hchooseQuad :
      d1InvariantQuad hex.choose = (d1Q0 z, d1Q1 z, d1P01 z, d1S01 z) :=
    hex.choose_spec.2
  have hquadEq : d1InvariantQuad hex.choose = d1InvariantQuad z := by
    simpa [d1InvariantQuad] using hchooseQuad
  rcases d1_exists_lorentz_of_sameInvariantQuad_on_FT hchooseFT hz hquadEq with ⟨Λ, hz_eq⟩
  have hΛchooseFT : complexLorentzAction Λ hex.choose ∈ ForwardTube 1 2 := by
    rw [← hz_eq]
    exact hz
  have hFΛ :
      F (complexLorentzAction Λ hex.choose) = F hex.choose :=
    complex_lorentz_invariance 2 F hF_holo hF_lorentz
      Λ hex.choose hchooseFT hΛchooseFT
  have hFz_action : F z = F (complexLorentzAction Λ hex.choose) :=
    congrArg F hz_eq
  have hFz_eq_hchoose : F z = F hex.choose :=
    hFz_action.trans hFΛ
  calc
    F z = F hex.choose := hFz_eq_hchoose
    _ = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hf_eq.symm

/-- Pure invariant-function swap law on the `d=1,n=2` invariant quadric. -/
def d1N2InvariantKernelSwapOnQuadric (f : ℂ → ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∀ q0 q1 p s : ℂ,
    s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      f q0 q1 p s = f q1 q0 p (-s)

/-- Equivalent invariant-only formulation:
the swap-difference kernel vanishes on the quadric
`s^2 = 4*(p^2 - q0*q1)`. -/
def d1N2InvariantKernelDiffZeroOnQuadric (f : ℂ → ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∀ q0 q1 p s : ℂ,
    s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      f q0 q1 p s - f q1 q0 p (-s) = 0

/-- From vanishing swap-difference on the quadric, recover the swap law. -/
theorem d1N2InvariantKernelSwapOnQuadric_of_diffZero
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hzero : d1N2InvariantKernelDiffZeroOnQuadric f) :
    d1N2InvariantKernelSwapOnQuadric f := by
  intro q0 q1 p s hquad
  exact sub_eq_zero.mp (hzero q0 q1 p s hquad)

/-- Invariant quadruple `(q0,q1,p,s)` is realized by an `FT_{1,2}` point. -/
def d1N2InvariantRealizable (q0 q1 p s : ℂ) : Prop :=
  ∃ z : Fin 2 → Fin (1 + 1) → ℂ,
    z ∈ ForwardTube 1 2 ∧ d1InvariantQuad z = (q0, q1, p, s)

/-- Swap-difference vanishes on quadric points that are realized by `FT_{1,2}`
configurations. This is the maximal statement forced by `hf_onFT` data alone. -/
def d1N2InvariantKernelDiffZeroOnRealizableQuadric
    (f : ℂ → ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∀ q0 q1 p s : ℂ,
    s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
    d1N2InvariantRealizable q0 q1 p s →
      f q0 q1 p s - f q1 q0 p (-s) = 0

/-- Invariant quadruple `(q0,q1,p,s)` is represented by a forward configuration
whose swapped image is forwardizable by some complex Lorentz witness. -/
def d1N2InvariantForwardizableSwap (q0 q1 p s : ℂ) : Prop :=
  ∃ z : Fin 2 → Fin (1 + 1) → ℂ, ∃ Γ : ComplexLorentzGroup 1,
    z ∈ ForwardTube 1 2 ∧
    complexLorentzAction Γ
      (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 ∧
    d1InvariantQuad z = (q0, q1, p, s)

/-- Swap-difference vanishes on quadric points that are forwardizable in the
`d=1,n=2` swap sense. -/
def d1N2InvariantKernelDiffZeroOnForwardizableQuadric
    (f : ℂ → ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∀ q0 q1 p s : ℂ,
    s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
    d1N2InvariantForwardizableSwap q0 q1 p s →
      f q0 q1 p s - f q1 q0 p (-s) = 0

/-- Source package for an invariant kernel arising from the `d=1,n=2`
Wightman assumptions and FT factorization data. -/
def d1N2InvariantKernelSource (f : ℂ → ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∃ F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ,
    DifferentiableOn ℂ F (ForwardTube 1 2) ∧
    (∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z) ∧
    (∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ))) ∧
    (∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) ∧
    (∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z))

/-- Reduce the `FT` kernel-swap condition to a pure invariant-quadric swap law. -/
theorem blocker_d1N2InvariantKernelSwap_core_of_quadricSwapLaw
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hquadSwap : d1N2InvariantKernelSwapOnQuadric f) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
  intro z _hz _Γ _hΓswap
  exact hquadSwap (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)
    (d1_invariant_quadric_relation z)

/-- Reduce the `FT` kernel-swap condition to vanishing of the invariant swap-
difference on realizable quadric points. -/
theorem blocker_d1N2InvariantKernelSwap_core_of_realizableQuadricDiffZero
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hquadDiff : d1N2InvariantKernelDiffZeroOnRealizableQuadric f) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
  intro z hz _Γ _hΓswap
  apply sub_eq_zero.mp
  exact hquadDiff (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)
    (d1_invariant_quadric_relation z) ⟨z, hz, rfl⟩

/-- Reduce the `FT` kernel-swap condition to vanishing of the invariant swap-
difference on forwardizable quadric points. -/
theorem blocker_d1N2InvariantKernelSwap_core_of_forwardizableQuadricDiffZero
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hquadDiff : d1N2InvariantKernelDiffZeroOnForwardizableQuadric f) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
  intro z hz Γ hΓswap
  apply sub_eq_zero.mp
  exact hquadDiff (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)
    (d1_invariant_quadric_relation z) ⟨z, Γ, hz, hΓswap, rfl⟩

/-- If forward-swap equality holds on `FT_{1,2}`, then any `FT` invariant kernel
representation has vanishing swap-difference on forwardizable invariant points. -/
theorem d1N2InvariantKernelDiffZeroOnForwardizableQuadric_of_forwardSwapEq
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z))
    (hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  intro q0 q1 p s _hquad hfw
  rcases hfw with ⟨z, Γ, hz, hΓswap, hquadZ⟩
  let y : Fin 2 → Fin (1 + 1) → ℂ :=
    complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)
  have hyFT : y ∈ ForwardTube 1 2 := by
    simpa [y] using hΓswap
  have hF_forward : F y = F z := by
    simpa [y] using hforward z hz Γ hΓswap
  have hleft : f q0 q1 p s = F z := by
    have hq :
        f q0 q1 p s = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := by
      simpa [d1InvariantQuad] using
        (congrArg (fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2) hquadZ).symm
    calc
      f q0 q1 p s = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) := hq
      _ = F z := by simpa using (hf_onFT z hz).symm
  have hquadY :
      d1InvariantQuad y = (q1, q0, p, -s) := by
    calc
      d1InvariantQuad y
          = d1InvariantQuad (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) := by
              simp [y, d1InvariantQuad_lorentzAction]
      _ = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z) := d1InvariantQuad_swap01 z
      _ = (q1, q0, p, -s) := by
            simpa [d1InvariantQuad] using congrArg
              (fun t => (t.2.1, t.1, t.2.2.1, -t.2.2.2)) hquadZ
  have hright : f q1 q0 p (-s) = F y := by
    have hq :
        f q1 q0 p (-s) = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := by
      simpa [d1InvariantQuad] using
        (congrArg (fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2) hquadY).symm
    calc
      f q1 q0 p (-s) = f (d1Q0 y) (d1Q1 y) (d1P01 y) (d1S01 y) := hq
      _ = F y := by simpa using (hf_onFT y hyFT).symm
  calc
    f q0 q1 p s - f q1 q0 p (-s) = F z - F y := by rw [hleft, hright]
    _ = 0 := sub_eq_zero.mpr hF_forward.symm

/-- Deferred invariant-function analytic core (`d=1,n=2`):
pure quadric-level involution law on Lorentz invariants. -/
theorem blocker_d1N2InvariantKernelSwapOnQuadric_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hquadDiff : d1N2InvariantKernelDiffZeroOnForwardizableQuadric f) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  exact hquadDiff

/-- `d=1,n=2` invariant-function core (deferred):
construct a swap-compatible invariant-kernel model on `FT`. -/
theorem blocker_d1N2InvariantModel_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    d1N2InvariantModel F := by
  rcases blocker_d1N2InvariantFactorization_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local with
    ⟨f, hf_onFT⟩
  have hf_swap :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
            f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
    -- Remaining analytic invariant-function core:
    -- establish swap-compatibility of the invariant kernel on forwardizable
    -- `FT_{1,2}` points from local commutativity via the invariant-quadric route.
    sorry
  exact ⟨f, hf_onFT, hf_swap⟩

/-- Deferred bridge (`d=1,n=2`): extract the forwardizable invariant
swap-difference vanishing statement from the Wightman-source package. -/
theorem blocker_d1N2InvariantKernelSwapOnForwardizable_core_fromSource_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  rcases hsource with ⟨F, hF_holo, hF_lorentz, hF_bv, hF_local, hf_onFT⟩
  have hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z :=
    d1_n2_forward_swap_eq_of_invariantModel F
      (blocker_d1N2InvariantModel_core_deferred F hF_holo hF_lorentz hF_bv hF_local)
  exact d1N2InvariantKernelDiffZeroOnForwardizableQuadric_of_forwardSwapEq
    F f hf_onFT hforward

/-- `d=1,n=2` invariant-function step B:
kernel swap symmetry reduced to forward-swap equality from the invariant model. -/
theorem blocker_d1N2InvariantKernelSwap_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z)) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z) =
          f (d1Q1 z) (d1Q0 z) (d1P01 z) (-d1S01 z) := by
  have hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z := by
    intro z hz Γ hΓswap
    exact d1_n2_forward_swap_eq_of_invariantModel F
      (blocker_d1N2InvariantModel_core_deferred F hF_holo hF_lorentz hF_bv hF_local)
      z hz Γ hΓswap
  exact d1_n2_invariantKernelSwapRule_of_forwardSwapEq F f hf_onFT hforward

/-- `d=1,n=2` forward swap equality on `FT`, reduced to the invariant model. -/
theorem blocker_d1N2ForwardSwapEq_on_FT_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∀ z, z ∈ ForwardTube 1 2 →
      ∀ Γ : ComplexLorentzGroup 1,
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        F (complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z := by
  intro z hz Γ hΓswap
  exact d1_n2_forward_swap_eq_of_invariantModel F
    (blocker_d1N2InvariantModel_core_deferred F hF_holo hF_lorentz hF_bv hF_local)
    z hz Γ hΓswap

/-- Deferred `d=1` local slice-anchor input at a prepared adjacent-swap anchor. -/
theorem blocker_eventually_slice_anchor_on_prepared_nhds_d1_nontrivial
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (τ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n τ ∧
      complexLorentzAction Γ (permAct (d := 1) τ w) ∈ ForwardTube 1 n)
    (hn2 : ¬ n ≤ 1)
    (hτ : τ ≠ 1) :
    ∀ᶠ w in 𝓝 w0, w ∈ U →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀ (permAct (d := 1) τ w) ∈ ForwardTube 1 n ∧
        F (complexLorentzAction Λ₀ (permAct (d := 1) τ w)) = F w := by
  by_cases h2 : n = 2
  · subst h2
    have hτswap : τ = Equiv.swap (0 : Fin 2) 1 :=
      fin2_perm_ne_one_eq_swap01 τ hτ
    subst hτswap
    exact Filter.Eventually.of_forall (fun w hwU => by
      refine ⟨Γ, (hU_good w hwU).2, ?_⟩
      have hwFT : w ∈ ForwardTube 1 2 := (hU_good w hwU).1.1
      exact blocker_d1N2ForwardSwapEq_on_FT_core_deferred
        F hF_holo hF_lorentz hF_bv hF_local w hwFT Γ (hU_good w hwU).2)
  · -- Remaining nontrivial local branches (`n = 3` and `4 ≤ n`) stay deferred.
    sorry

/-- Deferred `d=1` local slice-anchor input at a prepared adjacent-swap anchor. -/
theorem blocker_eventually_slice_anchor_on_prepared_nhds_d1
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (τ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n τ ∧
      complexLorentzAction Γ (permAct (d := 1) τ w) ∈ ForwardTube 1 n) :
    ∀ᶠ w in 𝓝 w0, w ∈ U →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀ (permAct (d := 1) τ w) ∈ ForwardTube 1 n ∧
        F (complexLorentzAction Λ₀ (permAct (d := 1) τ w)) = F w := by
  by_cases hτ : τ = 1
  · subst hτ
    exact Filter.Eventually.of_forall (fun w hwU => by
      refine ⟨(1 : ComplexLorentzGroup 1), ?_, ?_⟩
      · have hwFT : w ∈ ForwardTube 1 n := (hU_good w hwU).1.1
        simpa [permAct, complexLorentzAction_one] using hwFT
      · have hperm : permAct (d := 1) (1 : Equiv.Perm (Fin n)) w = w := by
          ext k μ
          simp [permAct]
        simp [complexLorentzAction_one, hperm])
  · by_cases hn : n ≤ 1
    · have hsub : Subsingleton (Fin n) := by
        refine ⟨?_⟩
        intro a b
        apply Fin.ext
        have ha0 : a.val = 0 := by omega
        have hb0 : b.val = 0 := by omega
        omega
      letI : Subsingleton (Fin n) := hsub
      exact (hτ (Subsingleton.elim τ 1)).elim
    · -- Remaining nontrivial branch (`n ≥ 2`, `τ ≠ 1`) is deferred.
      exact blocker_eventually_slice_anchor_on_prepared_nhds_d1_nontrivial
        n F hF_holo hF_lorentz hF_bv hF_local
        τ w0 Γ U hU_open hw0U hU_good hn hτ

/-- Deferred `d=1` geometric input B (`n ≥ 4` branch): forward-triple witness. -/
theorem blocker_d1_forward_triple_nonempty_nge4
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (hσ : σ ≠ (1 : Equiv.Perm (Fin n)))
    (hστ : σ ≠ Equiv.swap i ⟨i.val + 1, hi⟩)
    (hn4 : 4 ≤ n) :
    ({w : Fin n → Fin (1 + 1) → ℂ |
        w ∈ ForwardTube 1 n ∧
        permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩) w ∈ ExtendedTube 1 n ∧
        permAct (d := 1) σ w ∈ ExtendedTube 1 n
    }).Nonempty := by
  sorry

end BHW
