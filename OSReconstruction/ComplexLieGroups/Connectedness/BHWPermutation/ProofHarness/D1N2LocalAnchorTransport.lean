import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlowBlockers.Tail

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

example
    (F : D1N2Config → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : D1N2Config), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (w : D1N2Config)
    (Γ : ComplexLorentzGroup 1)
    (hΓswap :
      complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2)
    (hanchorAt :
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 ∧
        F (complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w) :
    F (complexLorentzAction Γ
      (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w :=
  d1N2ForwardEq_of_sliceAnchorAtPoint F hF_holo hF_lorentz w Γ hΓswap hanchorAt

example
    (F : D1N2Config → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : D1N2Config), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (w0 : D1N2Config)
    (Γ : ComplexLorentzGroup 1)
    (U : Set D1N2Config)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2) :
    (∀ᶠ w in 𝓝 w0, w ∈ U →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 ∧
        F (complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w) ↔
    (∀ᶠ w in 𝓝 w0, w ∈ U →
      F (complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w) :=
  d1N2EventuallySliceAnchor_iff_eventuallyForwardEq_fixedWitness
    F hF_holo hF_lorentz w0 Γ U hU_good

end BHW

