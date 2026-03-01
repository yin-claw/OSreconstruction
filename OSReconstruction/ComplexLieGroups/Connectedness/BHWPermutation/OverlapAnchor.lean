import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvarianceCore
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SeedSlices

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d : ℕ}

private lemma continuous_permAct
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Continuous (permAct (d := d) σ) := by
  refine continuous_pi ?_
  intro k
  refine continuous_pi ?_
  intro μ
  exact (continuous_apply μ).comp (continuous_apply (σ k))

/-- Extended-tube overlap domain for a fixed permutation. -/
def permExtendedOverlapSet
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  {z | z ∈ ExtendedTube d n ∧ permAct (d := d) σ z ∈ ExtendedTube d n}

/-- The ET overlap domain is the Lorentz-action image of the corresponding
forward-overlap slice. -/
theorem permExtendedOverlap_eq_action_image_forwardOverlap
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permExtendedOverlapSet (d := d) (n := n) σ =
      (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
        complexLorentzAction p.1 p.2) ''
      (Set.univ ×ˢ permForwardOverlapSet (d := d) n σ) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzET, hσzET⟩
    rcases Set.mem_iUnion.mp hzET with ⟨Λ, w, hwFT, hz_eq⟩
    have hσz_as_action :
        permAct (d := d) σ z =
          complexLorentzAction Λ (permAct (d := d) σ w) := by
      calc
        permAct (d := d) σ z
            = permAct (d := d) σ (complexLorentzAction Λ w) := by simp [hz_eq]
        _ = complexLorentzAction Λ (permAct (d := d) σ w) := by
              exact (lorentz_perm_commute Λ w σ).symm
    have hΛσw_ET : complexLorentzAction Λ (permAct (d := d) σ w) ∈ ExtendedTube d n := by
      simpa [hσz_as_action] using hσzET
    have hσw_ET : permAct (d := d) σ w ∈ ExtendedTube d n := by
      have := complexLorentzAction_mem_extendedTube (d := d) (n := n) Λ⁻¹ hΛσw_ET
      simpa [complexLorentzAction_inv] using this
    refine ⟨⟨Λ, w⟩, ⟨trivial, ⟨hwFT, hσw_ET⟩⟩, ?_⟩
    simp [hz_eq]
  · rintro ⟨⟨Λ, w⟩, ⟨_, hwFT, hσw_ET⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · exact complexLorentzAction_mem_extendedTube (d := d) (n := n) Λ
        (forwardTube_subset_extendedTube hwFT)
    · have hσ_action :
          permAct (d := d) σ (complexLorentzAction Λ w) =
            complexLorentzAction Λ (permAct (d := d) σ w) := by
        exact lorentz_perm_commute Λ w σ
      have hσ_ET : permAct (d := d) σ (complexLorentzAction Λ w) ∈ ExtendedTube d n := by
        simpa [hσ_action] using
          complexLorentzAction_mem_extendedTube (d := d) (n := n) Λ hσw_ET
      exact hσ_ET

/-- Connectedness transfer from forward overlap to ET overlap. -/
theorem isConnected_permExtendedOverlap_of_forwardOverlapConnected
    {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hFwd_conn : IsConnected (permForwardOverlapSet (d := d) n σ)) :
    IsConnected (permExtendedOverlapSet (d := d) (n := n) σ) := by
  haveI : PathConnectedSpace (ComplexLorentzGroup d) :=
    pathConnectedSpace_iff_univ.mpr ComplexLorentzGroup.isPathConnected
  have hprod_conn :
      IsConnected
        ((Set.univ : Set (ComplexLorentzGroup d)) ×ˢ
          permForwardOverlapSet (d := d) n σ) :=
    isConnected_univ.prod hFwd_conn
  have hcont : Continuous
      (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
        complexLorentzAction p.1 p.2) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    simp only [complexLorentzAction]
    apply continuous_finset_sum
    intro ν _
    apply Continuous.mul
    · have hval : Continuous
          (fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) => p.1.val) :=
        ComplexLorentzGroup.continuous_val.comp continuous_fst
      have hrow :
          Continuous (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M μ) :=
        continuous_apply μ
      have hentry : Continuous (fun r : Fin (d + 1) → ℂ => r ν) := continuous_apply ν
      exact hentry.comp (hrow.comp hval)
    · exact (continuous_apply ν).comp ((continuous_apply k).comp continuous_snd)
  have himage_conn :
      IsConnected
        ((fun p : ComplexLorentzGroup d × (Fin n → Fin (d + 1) → ℂ) =>
          complexLorentzAction p.1 p.2) ''
        ((Set.univ : Set (ComplexLorentzGroup d)) ×ˢ
          permForwardOverlapSet (d := d) n σ)) :=
    hprod_conn.image _ hcont.continuousOn
  simpa [permExtendedOverlap_eq_action_image_forwardOverlap (d := d) (n := n) σ]
    using himage_conn

/-- Open-anchor ET-overlap propagation from connected forward overlap.

If ET-overlap permutation equality for `extendF` holds on a nonempty open subset
of the overlap domain, it holds on the full overlap domain as soon as the
forward-overlap set is connected. -/
theorem extendF_perm_overlap_of_open_anchor_and_forwardOverlapConnected
    {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hFwd_conn : IsConnected (permForwardOverlapSet (d := d) n σ))
    (W : Set (Fin n → Fin (d + 1) → ℂ))
    (hW_open : IsOpen W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ permExtendedOverlapSet (d := d) (n := n) σ)
    (hW_eq : ∀ z ∈ W, extendF F (permAct (d := d) σ z) = extendF F z) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  let D : Set (Fin n → Fin (d + 1) → ℂ) := permExtendedOverlapSet (d := d) (n := n) σ
  have hD_open : IsOpen D := by
    change IsOpen (ExtendedTube d n ∩ (permAct (d := d) σ) ⁻¹' ExtendedTube d n)
    exact isOpen_extendedTube.inter (isOpen_extendedTube.preimage
      (continuous_permAct (d := d) (n := n) σ))
  have hD_conn : IsConnected D :=
    isConnected_permExtendedOverlap_of_forwardOverlapConnected (d := d) (n := n) σ hFwd_conn
  have hD_sub_ET : D ⊆ ExtendedTube d n := by
    intro z hz
    exact hz.1
  have hD_sub_permET : D ⊆ {z | permAct (d := d) σ z ∈ ExtendedTube d n} := by
    intro z hz
    exact hz.2
  exact fun z hz hσz =>
    extendF_perm_eq_on_connectedDomain_of_openSubset n F hF_holo hF_lorentz
      σ D hD_open hD_conn hD_sub_ET hD_sub_permET
      W hW_open hW_ne hW_sub hW_eq z ⟨hz, hσz⟩

/-- Extract an explicit nonempty complex-open anchor subset of the ET-overlap
domain from local eventual overlap equality at one anchor point. -/
theorem exists_overlap_open_anchor_of_eventuallyEq_local
    {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (σ : Equiv.Perm (Fin n))
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hz0D : z0 ∈ permExtendedOverlapSet (d := d) (n := n) σ)
    (hlocal : ∀ᶠ z in 𝓝 z0,
      z ∈ permExtendedOverlapSet (d := d) (n := n) σ →
      extendF F (permAct (d := d) σ z) = extendF F z) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧
      W.Nonempty ∧
      W ⊆ permExtendedOverlapSet (d := d) (n := n) σ ∧
      (∀ z ∈ W, extendF F (permAct (d := d) σ z) = extendF F z) := by
  let D : Set (Fin n → Fin (d + 1) → ℂ) := permExtendedOverlapSet (d := d) (n := n) σ
  have hD_open : IsOpen D := by
    change IsOpen (ExtendedTube d n ∩ (permAct (d := d) σ) ⁻¹' ExtendedTube d n)
    exact isOpen_extendedTube.inter (isOpen_extendedTube.preimage
      (continuous_permAct (d := d) (n := n) σ))
  have hnhds_inter :
      (D ∩ {z | z ∈ D → extendF F (permAct (d := d) σ z) = extendF F z}) ∈ 𝓝 z0 := by
    refine Filter.inter_mem (hD_open.mem_nhds ?_) hlocal
    exact hz0D
  rcases mem_nhds_iff.mp hnhds_inter with ⟨W, hW_sub, hW_open, hz0W⟩
  have hW_ne : W.Nonempty := ⟨z0, hz0W⟩
  have hW_sub_D : W ⊆ D := by
    intro z hz
    exact (hW_sub hz).1
  have hW_eq : ∀ z ∈ W, extendF F (permAct (d := d) σ z) = extendF F z := by
    intro z hz
    exact (hW_sub hz).2 (hW_sub_D hz)
  exact ⟨W, hW_open, hW_ne, hW_sub_D, hW_eq⟩

/-- Eventual ET-overlap equality at one complex anchor point upgrades to global
ET-overlap permutation invariance, assuming connected forward overlap. -/
theorem extendF_perm_overlap_of_eventuallyEq_anchor_and_forwardOverlapConnected
    {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hFwd_conn : IsConnected (permForwardOverlapSet (d := d) n σ))
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (hz0D : z0 ∈ permExtendedOverlapSet (d := d) (n := n) σ)
    (hlocal : ∀ᶠ z in 𝓝 z0,
      z ∈ permExtendedOverlapSet (d := d) (n := n) σ →
      extendF F (permAct (d := d) σ z) = extendF F z) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  rcases exists_overlap_open_anchor_of_eventuallyEq_local
      (d := d) (n := n) F σ z0 hz0D hlocal with
    ⟨W, hW_open, hW_ne, hW_sub, hW_eq⟩
  exact extendF_perm_overlap_of_open_anchor_and_forwardOverlapConnected
    (d := d) (n := n) F hF_holo hF_lorentz σ hFwd_conn
    W hW_open hW_ne hW_sub hW_eq

/-- ET-overlap permutation invariance of `extendF` from a forward-base identity.

If one can prove the base identity
`extendF F (σ · w) = F w` for every `w ∈ FT` with `σ · w ∈ ET`, then full
ET-overlap permutation invariance of `extendF` follows for the same `σ`. -/
theorem extendF_perm_overlap_of_forward_base
    {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hBase :
      ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
        permAct (d := d) σ w ∈ ExtendedTube d n →
        extendF F (permAct (d := d) σ w) = F w) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  intro z hz hσz
  rcases Set.mem_iUnion.mp hz with ⟨Λ, w, hwFT, rfl⟩
  have hσ_action :
      permAct (d := d) σ (complexLorentzAction Λ w) =
        complexLorentzAction Λ (permAct (d := d) σ w) := by
    simpa [permAct] using (lorentz_perm_commute Λ w σ).symm
  have hΛσw_ET : complexLorentzAction Λ (permAct (d := d) σ w) ∈ ExtendedTube d n := by
    simpa [hσ_action] using hσz
  have hσw_ET : permAct (d := d) σ w ∈ ExtendedTube d n := by
    have := complexLorentzAction_mem_extendedTube (d := d) (n := n) Λ⁻¹ hΛσw_ET
    simpa [complexLorentzAction_inv] using this
  have hbase_w : extendF F (permAct (d := d) σ w) = F w :=
    hBase w hwFT hσw_ET
  have hleft :
      extendF F (permAct (d := d) σ (complexLorentzAction Λ w)) =
        extendF F (permAct (d := d) σ w) := by
    calc
      extendF F (permAct (d := d) σ (complexLorentzAction Λ w))
          = extendF F (complexLorentzAction Λ (permAct (d := d) σ w)) := by
              simp [hσ_action]
      _ = extendF F (permAct (d := d) σ w) :=
            extendF_complex_lorentz_invariant (d := d) n F hF_holo hF_real_inv
              Λ (permAct (d := d) σ w) hσw_ET
  have hright :
      extendF F (complexLorentzAction Λ w) = extendF F w :=
    extendF_complex_lorentz_invariant (d := d) n F hF_holo hF_real_inv
      Λ w (forwardTube_subset_extendedTube hwFT)
  have hw_eval : extendF F w = F w :=
    extendF_eq_on_forwardTube n F hF_holo hF_real_inv w hwFT
  calc
    extendF F (permAct (d := d) σ (complexLorentzAction Λ w))
        = extendF F (permAct (d := d) σ w) := hleft
    _ = F w := hbase_w
    _ = extendF F w := hw_eval.symm
    _ = extendF F (complexLorentzAction Λ w) := hright.symm

/-- Open-anchor propagation on the forward-overlap base set.

If the base identity `extendF F (σ·w) = F w` holds on a nonempty open subset of
the connected base set `{w ∈ FT | σ·w ∈ ET}`, then it holds on the whole base set. -/
theorem forward_base_eq_of_open_anchor
    {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hΩ_conn : IsConnected (permForwardOverlapSet (d := d) n σ))
    (W : Set (Fin n → Fin (d + 1) → ℂ))
    (hW_open : IsOpen W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ permForwardOverlapSet (d := d) n σ)
    (hW_eq : ∀ w ∈ W, extendF F (permAct (d := d) σ w) = F w) :
    ∀ w ∈ permForwardOverlapSet (d := d) n σ,
      extendF F (permAct (d := d) σ w) = F w := by
  let Ω : Set (Fin n → Fin (d + 1) → ℂ) := permForwardOverlapSet (d := d) n σ
  have hΩ_open : IsOpen Ω := by
    change IsOpen (ForwardTube d n ∩ (permAct (d := d) σ) ⁻¹' ExtendedTube d n)
    exact isOpen_forwardTube.inter (isOpen_extendedTube.preimage
      (continuous_permAct (d := d) (n := n) σ))
  have hF_cinv : ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_real_inv Λ z hz hΛz
  have hExt_holo : DifferentiableOn ℂ (extendF F) (ExtendedTube d n) :=
    extendF_holomorphicOn n F hF_holo hF_cinv
  let f : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun w => extendF F (permAct (d := d) σ w)
  let g : (Fin n → Fin (d + 1) → ℂ) → ℂ := F
  have hf : DifferentiableOn ℂ f Ω := by
    intro w hwΩ
    have hperm_diff : Differentiable ℂ (permAct (d := d) σ) :=
      differentiable_pi.mpr (fun k => differentiable_apply (σ k))
    have hcomp : DifferentiableAt ℂ f w := by
      exact ((hExt_holo _ hwΩ.2).differentiableAt
        (isOpen_extendedTube.mem_nhds hwΩ.2)).comp w (hperm_diff w)
    exact hcomp.differentiableWithinAt
  have hg : DifferentiableOn ℂ g Ω := by
    intro w hwΩ
    exact ((hF_holo w hwΩ.1).differentiableAt
      (isOpen_forwardTube.mem_nhds hwΩ.1)).differentiableWithinAt
  rcases hW_ne with ⟨w0, hw0W⟩
  have hw0Ω : w0 ∈ Ω := hW_sub hw0W
  have hagree : f =ᶠ[nhds w0] g := by
    apply Filter.eventuallyEq_of_mem (hW_open.mem_nhds hw0W)
    intro w hwW
    exact hW_eq w hwW
  have hEqOn : Set.EqOn f g Ω :=
    identity_theorem_product hΩ_open hΩ_conn hf hg hw0Ω hagree
  intro w hwΩ
  exact hEqOn hwΩ

/-- Real-anchor propagation on the forward-overlap base set.

If the base identity `extendF F (σ·w) = F w` holds on a nonempty open subset of
real configurations whose embedding lies in the connected base set
`{w ∈ FT | σ·w ∈ ET}`, then it holds on the whole base set. -/
theorem forward_base_eq_of_real_open_anchor
    {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hΩ_conn : IsConnected (permForwardOverlapSet (d := d) n σ))
    (V : Set (Fin n → Fin (d + 1) → ℝ))
    (hV_open : IsOpen V)
    (hV_ne : V.Nonempty)
    (hV_sub : ∀ x ∈ V, realEmbed x ∈ permForwardOverlapSet (d := d) n σ)
    (hV_eq : ∀ x ∈ V, extendF F (permAct (d := d) σ (realEmbed x)) = F (realEmbed x)) :
    ∀ w ∈ permForwardOverlapSet (d := d) n σ,
      extendF F (permAct (d := d) σ w) = F w := by
  let Ω : Set (Fin n → Fin (d + 1) → ℂ) := permForwardOverlapSet (d := d) n σ
  have hΩ_open : IsOpen Ω := by
    change IsOpen (ForwardTube d n ∩ (permAct (d := d) σ) ⁻¹' ExtendedTube d n)
    exact isOpen_forwardTube.inter (isOpen_extendedTube.preimage
      (continuous_permAct (d := d) (n := n) σ))
  have hF_cinv : ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_real_inv Λ z hz hΛz
  have hExt_holo : DifferentiableOn ℂ (extendF F) (ExtendedTube d n) :=
    extendF_holomorphicOn n F hF_holo hF_cinv
  let f : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun w => extendF F (permAct (d := d) σ w)
  let g : (Fin n → Fin (d + 1) → ℂ) → ℂ := F
  have hf : DifferentiableOn ℂ f Ω := by
    intro w hwΩ
    have hperm_diff : Differentiable ℂ (permAct (d := d) σ) :=
      differentiable_pi.mpr (fun k => differentiable_apply (σ k))
    have hcomp : DifferentiableAt ℂ f w := by
      exact ((hExt_holo _ hwΩ.2).differentiableAt
        (isOpen_extendedTube.mem_nhds hwΩ.2)).comp w (hperm_diff w)
    exact hcomp.differentiableWithinAt
  have hg : DifferentiableOn ℂ g Ω := by
    intro w hwΩ
    exact ((hF_holo w hwΩ.1).differentiableAt
      (isOpen_forwardTube.mem_nhds hwΩ.1)).differentiableWithinAt
  let h : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun w => f w - g w
  have hh : DifferentiableOn ℂ h Ω := hf.sub hg
  have hV_zero : ∀ x ∈ V, h (realEmbed x) = 0 := by
    intro x hx
    have hx_eq : f (realEmbed x) = g (realEmbed x) := hV_eq x hx
    simp [h, hx_eq]
  have hEqZero : ∀ w ∈ Ω, h w = 0 :=
    identity_theorem_totally_real_product (hD_open := hΩ_open) (hD_conn := hΩ_conn)
      (hf := hh) (hV_open := hV_open) (hV_ne := hV_ne) (hV_sub := hV_sub)
      (hf_zero := hV_zero)
  intro w hwΩ
  exact sub_eq_zero.mp (hEqZero w hwΩ)

/-- Open-anchor wrapper for ET-overlap permutation invariance.

An open-anchor identity on the connected forward-overlap base set is enough to
derive full ET-overlap permutation invariance of `extendF`. -/
theorem extendF_perm_overlap_of_forward_open_anchor
    {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hΩ_conn : IsConnected (permForwardOverlapSet (d := d) n σ))
    (W : Set (Fin n → Fin (d + 1) → ℂ))
    (hW_open : IsOpen W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ permForwardOverlapSet (d := d) n σ)
    (hW_eq : ∀ w ∈ W, extendF F (permAct (d := d) σ w) = F w) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  have hBase :
      ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
        permAct (d := d) σ w ∈ ExtendedTube d n →
        extendF F (permAct (d := d) σ w) = F w := by
    intro w hwFT hσwET
    exact forward_base_eq_of_open_anchor (d := d) (n := n) F hF_holo hF_real_inv
      σ hΩ_conn W hW_open hW_ne hW_sub hW_eq w ⟨hwFT, hσwET⟩
  exact extendF_perm_overlap_of_forward_base (d := d) (n := n)
    F hF_holo hF_real_inv σ hBase

/-- Real-open-anchor wrapper for ET-overlap permutation invariance.

An identity known on a nonempty real-open anchor set in the forward-overlap base
is enough to derive full ET-overlap permutation invariance of `extendF`. -/
theorem extendF_perm_overlap_of_forward_real_open_anchor
    {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hΩ_conn : IsConnected (permForwardOverlapSet (d := d) n σ))
    (V : Set (Fin n → Fin (d + 1) → ℝ))
    (hV_open : IsOpen V)
    (hV_ne : V.Nonempty)
    (hV_sub : ∀ x ∈ V, realEmbed x ∈ permForwardOverlapSet (d := d) n σ)
    (hV_eq : ∀ x ∈ V, extendF F (permAct (d := d) σ (realEmbed x)) = F (realEmbed x)) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  have hBase :
      ∀ (w : Fin n → Fin (d + 1) → ℂ), w ∈ ForwardTube d n →
        permAct (d := d) σ w ∈ ExtendedTube d n →
        extendF F (permAct (d := d) σ w) = F w := by
    intro w hwFT hσwET
    exact forward_base_eq_of_real_open_anchor (d := d) (n := n) F hF_holo hF_real_inv
      σ hΩ_conn V hV_open hV_ne hV_sub hV_eq w ⟨hwFT, hσwET⟩
  exact extendF_perm_overlap_of_forward_base (d := d) (n := n)
    F hF_holo hF_real_inv σ hBase

/-- Real-open-anchor ET-overlap propagation.

If ET-overlap permutation equality for `extendF` holds on a nonempty real-open
anchor subset of the overlap domain
`D_σ = ET ∩ σ^{-1}(ET)`, then it holds on all of `D_σ` as soon as
`permForwardOverlapSet` is connected. -/
theorem extendF_perm_overlap_of_overlap_real_open_anchor
    {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hFwd_conn : IsConnected (permForwardOverlapSet (d := d) n σ))
    (V : Set (Fin n → Fin (d + 1) → ℝ))
    (hV_open : IsOpen V)
    (hV_ne : V.Nonempty)
    (hV_sub : ∀ x ∈ V, realEmbed x ∈ permExtendedOverlapSet (d := d) (n := n) σ)
    (hV_eq : ∀ x ∈ V,
      extendF F (permAct (d := d) σ (realEmbed x)) = extendF F (realEmbed x)) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      permAct (d := d) σ z ∈ ExtendedTube d n →
      extendF F (permAct (d := d) σ z) = extendF F z := by
  let D : Set (Fin n → Fin (d + 1) → ℂ) := permExtendedOverlapSet (d := d) (n := n) σ
  have hD_open : IsOpen D := by
    change IsOpen (ExtendedTube d n ∩ (permAct (d := d) σ) ⁻¹' ExtendedTube d n)
    exact isOpen_extendedTube.inter (isOpen_extendedTube.preimage
      (continuous_permAct (d := d) (n := n) σ))
  have hD_conn : IsConnected D :=
    isConnected_permExtendedOverlap_of_forwardOverlapConnected
      (d := d) (n := n) σ hFwd_conn
  have hD_sub_ET : D ⊆ ExtendedTube d n := by
    intro z hz
    exact hz.1
  have hD_sub_permET : D ⊆ {z | permAct (d := d) σ z ∈ ExtendedTube d n} := by
    intro z hz
    exact hz.2
  have hV_sub_D : ∀ x ∈ V, realEmbed x ∈ D := by
    intro x hx
    exact hV_sub x hx
  intro z hzET hσzET
  have hzD : z ∈ D := ⟨hzET, hσzET⟩
  exact extendF_perm_eq_on_connectedDomain_of_realOpen n F hF_holo hF_real_inv
    σ D hD_open hD_conn hD_sub_ET hD_sub_permET
    V hV_open hV_ne hV_sub_D hV_eq z hzD

end BHW
