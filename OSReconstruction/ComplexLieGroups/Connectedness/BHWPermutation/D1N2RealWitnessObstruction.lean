import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.D1N2Invariants
import OSReconstruction.ComplexLieGroups.D1OrbitSet

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

private abbrev i0 : Fin (1 + 1) := 0
private abbrev i1 : Fin (1 + 1) := 1

private def plusCoord (v : Fin 2 → ℝ) : ℝ := v 0 + v 1

private lemma inOpenForwardCone_one_plus_pos (η : Fin (1 + 1) → ℝ)
    (hη : InOpenForwardCone 1 η) :
    η 0 + η 1 > 0 := by
  have htime : 0 < η 0 := hη.1
  have hq : -(η 0) ^ 2 + (η 1) ^ 2 < 0 := by
    simpa [minkowskiSignature] using hη.2
  have hsq : (η 1) ^ 2 < (η 0) ^ 2 := by nlinarith
  have habs : |η 1| < η 0 := by
    exact abs_lt_of_sq_lt_sq hsq (le_of_lt htime)
  linarith [neg_abs_le (η 1)]

private theorem d1_eta_transpose_eta_eq (Λ : ComplexLorentzGroup 1) :
    ComplexLorentzGroup.ηℂ * Λ.val.transpose * ComplexLorentzGroup.ηℂ =
      !![Λ.val i0 i0, -Λ.val i1 i0; -Λ.val i0 i1, Λ.val i1 i1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ComplexLorentzGroup.ηℂ, minkowskiSignature]

private theorem d1_inv_eq_adjugate_fin_two (Λ : ComplexLorentzGroup 1) :
    Λ.val⁻¹ = !![Λ.val i1 i1, -Λ.val i0 i1; -Λ.val i1 i0, Λ.val i0 i0] := by
  rw [Matrix.inv_def]
  have hdet : Λ.val.det = (1 : ℂ) := Λ.proper
  rw [hdet, Ring.inverse_one, one_smul]
  simpa using (Matrix.adjugate_fin_two Λ.val)

private theorem d1_entries_pairing (Λ : ComplexLorentzGroup 1) :
    Λ.val i0 i0 = Λ.val i1 i1 ∧ Λ.val i0 i1 = Λ.val i1 i0 := by
  have h_left_inv :
      (ComplexLorentzGroup.ηℂ * Λ.val.transpose * ComplexLorentzGroup.ηℂ) * Λ.val =
        (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) := by
    have hΛ := ComplexLorentzGroup.metric_preserving_matrix Λ
    calc
      ComplexLorentzGroup.ηℂ * Λ.val.transpose * ComplexLorentzGroup.ηℂ * Λ.val
          = ComplexLorentzGroup.ηℂ * (Λ.val.transpose * ComplexLorentzGroup.ηℂ * Λ.val) := by
              simp [Matrix.mul_assoc]
      _ = ComplexLorentzGroup.ηℂ * ComplexLorentzGroup.ηℂ := by rw [hΛ]
      _ = 1 := ComplexLorentzGroup.ηℂ_sq (d := 1)
  have h_right_inv :
      Λ.val * (ComplexLorentzGroup.ηℂ * Λ.val.transpose * ComplexLorentzGroup.ηℂ) =
        (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) := by
    exact mul_eq_one_comm.mp h_left_inv
  have h_inv_eta :
      Λ.val⁻¹ = ComplexLorentzGroup.ηℂ * Λ.val.transpose * ComplexLorentzGroup.ηℂ :=
    Matrix.inv_eq_right_inv h_right_inv
  rw [d1_eta_transpose_eta_eq, d1_inv_eq_adjugate_fin_two] at h_inv_eta
  have h00 : Λ.val i0 i0 = Λ.val i1 i1 := by
    simpa [i0, i1] using (congr_fun (congr_fun h_inv_eta 0) 0).symm
  have h01 : Λ.val i0 i1 = Λ.val i1 i0 := by
    simpa [i0, i1] using congrFun (congr_fun h_inv_eta 0) 1
  exact ⟨h00, h01⟩

private theorem plus_channel_action_real_cfg
    (Γ : ComplexLorentzGroup 1)
    (x : Fin 2 → Fin 2 → ℝ) (k : Fin 2) :
    ((BHWCore.complexLorentzAction (d := 1) (n := 2) Γ (realEmbed x) k 0).im +
      (BHWCore.complexLorentzAction (d := 1) (n := 2) Γ (realEmbed x) k 1).im)
      = (Γ.val i0 i0 + Γ.val i0 i1).im * plusCoord (x k) := by
  rcases d1_entries_pairing Γ with ⟨hdiag, hoff⟩
  simp [realEmbed, BHWCore.complexLorentzAction, Fin.sum_univ_two, plusCoord, hdiag, hoff,
    Complex.add_im, mul_add, add_assoc, add_comm, Complex.mul_im]
  ring

private theorem et_real_plus_profile_n2
    (x : Fin 2 → Fin 2 → ℝ)
    (hET : realEmbed x ∈ ExtendedTube 1 2) :
    ∃ splus : ℝ,
      splus * plusCoord (x 0) > 0 ∧
      splus * plusCoord (fun μ => x 1 μ - x 0 μ) > 0 := by
  rcases Set.mem_iUnion.mp hET with ⟨Λ, w, hwFT, hx_eq⟩
  let Γ : ComplexLorentzGroup 1 := Λ⁻¹
  have hx_eq_core : realEmbed x =
      BHWCore.complexLorentzAction (d := 1) (n := 2) Λ w := by
    simpa [complexLorentzAction] using hx_eq
  have hw_repr : w = BHWCore.complexLorentzAction (d := 1) (n := 2) Γ (realEmbed x) := by
    calc
      w = BHWCore.complexLorentzAction (d := 1) (n := 2) Γ
          (BHWCore.complexLorentzAction (d := 1) (n := 2) Λ w) := by
            simpa [Γ] using (BHWCore.complexLorentzAction_inv (d := 1) (n := 2) Λ w).symm
      _ = BHWCore.complexLorentzAction (d := 1) (n := 2) Γ (realEmbed x) := by
            simp [hx_eq_core]
  let splus : ℝ := (Γ.val i0 i0 + Γ.val i0 i1).im
  have h0 := hwFT (0 : Fin 2)
  have h1 := hwFT (1 : Fin 2)
  have h0_plus : ((w 0 0).im + (w 0 1).im) > 0 := by
    have := inOpenForwardCone_one_plus_pos
      (η := fun μ => (w 0 μ -
        ((if h : (0 : Fin 2).val = 0 then (0 : Fin 2 → ℂ) else w ⟨(0 : Fin 2).val - 1, by omega⟩) μ)).im)
      h0
    simpa using this
  have h1_plus : (((w 1 0 - w 0 0).im) + ((w 1 1 - w 0 1).im)) > 0 := by
    have := inOpenForwardCone_one_plus_pos
      (η := fun μ => (w 1 μ -
        ((if h : (1 : Fin 2).val = 0 then (0 : Fin 2 → ℂ) else w ⟨(1 : Fin 2).val - 1, by omega⟩) μ)).im)
      h1
    simpa using this
  have hs0 : splus * plusCoord (x 0) > 0 := by
    have hw0 :
        ((w 0 0).im + (w 0 1).im) = splus * plusCoord (x 0) := by
      calc
        ((w 0 0).im + (w 0 1).im)
            = ((BHWCore.complexLorentzAction (d := 1) (n := 2) Γ (realEmbed x) 0 0).im +
                (BHWCore.complexLorentzAction (d := 1) (n := 2) Γ (realEmbed x) 0 1).im) := by
                  simp [hw_repr]
        _ = splus * plusCoord (x 0) := by
              simpa [splus] using plus_channel_action_real_cfg Γ x 0
    exact hw0 ▸ h0_plus
  have hs1 : splus * plusCoord (fun μ => x 1 μ - x 0 μ) > 0 := by
    have hdiff :
        (((w 1 0 - w 0 0).im) + ((w 1 1 - w 0 1).im))
          = splus * plusCoord (fun μ => x 1 μ - x 0 μ) := by
      let xdiff : Fin 2 → Fin 2 → ℝ := fun k μ =>
        if k = (0 : Fin 2) then x 1 μ - x 0 μ else 0
      have hxdiff0 : xdiff 0 = fun μ => x 1 μ - x 0 μ := by
        ext μ
        simp [xdiff]
      have hwlin :
          (fun μ => w 1 μ - w 0 μ) =
            BHWCore.complexLorentzAction (d := 1) (n := 2) Γ (realEmbed xdiff) 0 := by
        ext μ
        simp [hw_repr, xdiff, realEmbed, BHWCore.complexLorentzAction, Fin.sum_univ_two,
          sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add]
      have hwlin0 :
          w 1 0 - w 0 0 =
            BHWCore.complexLorentzAction (d := 1) (n := 2) Γ (realEmbed xdiff) 0 0 := by
        simpa using congrArg (fun f : Fin 2 → ℂ => f 0) hwlin
      have hwlin1 :
          w 1 1 - w 0 1 =
            BHWCore.complexLorentzAction (d := 1) (n := 2) Γ (realEmbed xdiff) 0 1 := by
        simpa using congrArg (fun f : Fin 2 → ℂ => f 1) hwlin
      calc
        (((w 1 0 - w 0 0).im) + ((w 1 1 - w 0 1).im))
            = (((BHWCore.complexLorentzAction (d := 1) (n := 2) Γ
                  (realEmbed xdiff) 0 0).im) +
                ((BHWCore.complexLorentzAction (d := 1) (n := 2) Γ
                  (realEmbed xdiff) 0 1).im)) := by
                  simp [hwlin0, hwlin1]
        _ = (Γ.val i0 i0 + Γ.val i0 i1).im * plusCoord (xdiff 0) := by
              exact plus_channel_action_real_cfg Γ xdiff 0
        _ = splus * plusCoord (fun μ => x 1 μ - x 0 μ) := by
              simp [splus, hxdiff0]
    exact hdiff ▸ h1_plus
  exact ⟨splus, hs0, hs1⟩

private theorem et_real_plus_profile_n2_swapped
    (x : Fin 2 → Fin 2 → ℝ)
    (hSwapET :
      realEmbed (fun k => x (Equiv.swap (0 : Fin 2) (1 : Fin 2) k))
        ∈ ExtendedTube 1 2) :
    ∃ splus' : ℝ,
      splus' * plusCoord (x 1) > 0 ∧
      splus' * plusCoord (fun μ => x 0 μ - x 1 μ) > 0 := by
  set xswap : Fin 2 → Fin 2 → ℝ := fun k => x (Equiv.swap (0 : Fin 2) (1 : Fin 2) k)
  rcases et_real_plus_profile_n2 xswap hSwapET with ⟨splus', hs0, hs1⟩
  refine ⟨splus', ?_, ?_⟩
  · simpa [xswap, plusCoord] using hs0
  · simpa [xswap, plusCoord, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs1

/-- In `d=1,n=2`, there is no real configuration whose embedding and swapped
embedding are both in the extended tube. -/
theorem d1N2_no_real_et_pair_swap :
    ¬ ∃ x : Fin 2 → Fin 2 → ℝ,
      realEmbed x ∈ ExtendedTube 1 2 ∧
      realEmbed (fun k => x (Equiv.swap (0 : Fin 2) (1 : Fin 2) k))
        ∈ ExtendedTube 1 2 := by
  intro hx
  rcases hx with ⟨x, hxET, hSwapET⟩
  rcases et_real_plus_profile_n2 x hxET with ⟨s, hs_x0, hs_diff⟩
  rcases et_real_plus_profile_n2_swapped x hSwapET with ⟨s', hs_x1, hs_negdiff⟩
  let A : ℝ := plusCoord (x 0)
  let B : ℝ := plusCoord (fun μ => x 1 μ - x 0 μ)
  let C : ℝ := plusCoord (x 1)
  have hC_eq : C = A + B := by
    simp [A, B, C, plusCoord, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hs_C : s * C > 0 := by
    rw [hC_eq, mul_add]
    have hs_A : s * A > 0 := by simpa [A] using hs_x0
    have hs_B : s * B > 0 := by simpa [B] using hs_diff
    linarith
  have hs_B : s * B > 0 := by simpa [B] using hs_diff
  have hs'_Bneg : s' * (-B) > 0 := by
    simpa [B, plusCoord, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs_negdiff
  have hB_ne : B ≠ 0 := by
    intro hB0
    have : s * B = 0 := by simp [hB0]
    linarith
  have hs'_C : s' * C > 0 := by simpa [C] using hs_x1
  by_cases hBpos : 0 < B
  · have hs_pos : 0 < s := by
      nlinarith [hs_B, hBpos]
    have hs'_neg : s' < 0 := by
      have hnegB : -B < 0 := by linarith
      nlinarith [hs'_Bneg, hnegB]
    have hC_pos : 0 < C := by
      nlinarith [hs_C, hs_pos]
    have hC_neg : C < 0 := by
      nlinarith [hs'_C, hs'_neg]
    linarith
  · have hBneg : B < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hBpos) (by
        intro h0B
        exact hB_ne h0B)
    have hs_neg : s < 0 := by
      nlinarith [hs_B, hBneg]
    have hs'_pos : 0 < s' := by
      have hnegBpos : 0 < -B := by linarith
      nlinarith [hs'_Bneg, hnegBpos]
    have hC_neg : C < 0 := by
      nlinarith [hs_C, hs_neg]
    have hC_pos : 0 < C := by
      nlinarith [hs'_C, hs'_pos]
    linarith

/-- Corollary: the `d=1,n=2` EOW real-witness package is impossible. -/
theorem d1N2_no_real_adjacent_spacelike_witness_swap :
    ¬ ∃ x : Fin 2 → Fin 2 → ℝ,
      (∑ μ, minkowskiSignature 1 μ *
          (x (1 : Fin 2) μ - x (0 : Fin 2) μ) ^ 2 > 0) ∧
      realEmbed x ∈ ExtendedTube 1 2 ∧
      realEmbed (fun k => x (Equiv.swap (0 : Fin 2) (1 : Fin 2) k))
        ∈ ExtendedTube 1 2 := by
  intro hx
  rcases hx with ⟨x, _hsp, hxET, hSwapET⟩
  exact d1N2_no_real_et_pair_swap ⟨x, hxET, hSwapET⟩

end BHW
