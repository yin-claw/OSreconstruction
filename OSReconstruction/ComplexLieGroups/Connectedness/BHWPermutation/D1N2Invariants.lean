import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SeedSlices
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

/-- `d=1` Minkowski bilinear form in coordinates `(t,x)` with signature `(-,+)`. -/
def d1MinkowskiBilin (u v : Fin (1 + 1) → ℝ) : ℝ :=
  ∑ μ, minkowskiSignature 1 μ * u μ * v μ

/-- Symmetry of the `d=1` Minkowski bilinear form. -/
lemma d1MinkowskiBilin_symm (u v : Fin (1 + 1) → ℝ) :
    d1MinkowskiBilin u v = d1MinkowskiBilin v u := by
  simp [d1MinkowskiBilin, mul_comm, mul_left_comm]

/-- Polarization identity for the `d=1` Minkowski form on a difference vector. -/
lemma d1MinkowskiBilin_sub_sub (u v : Fin (1 + 1) → ℝ) :
    d1MinkowskiBilin (fun μ => v μ - u μ) (fun μ => v μ - u μ) =
      d1MinkowskiBilin u u + d1MinkowskiBilin v v - 2 * d1MinkowskiBilin u v := by
  simp [d1MinkowskiBilin, Fin.sum_univ_two]
  ring

/-- `n=2` specialization: the adjacent spacelike expression at indices `(0,1)`
expands as `a + b - 2c` in `d=1` Minkowski invariants. -/
lemma d1_n2_adj_spacelike_expr_eq_invariants (x : Fin 2 → Fin (1 + 1) → ℝ) :
    (∑ μ, minkowskiSignature 1 μ * (x 1 μ - x 0 μ) ^ 2) =
      d1MinkowskiBilin (x 0) (x 0) +
      d1MinkowskiBilin (x 1) (x 1) -
      2 * d1MinkowskiBilin (x 0) (x 1) := by
  calc
    (∑ μ, minkowskiSignature 1 μ * (x 1 μ - x 0 μ) ^ 2)
        = d1MinkowskiBilin (fun μ => x 1 μ - x 0 μ) (fun μ => x 1 μ - x 0 μ) := by
            simp [d1MinkowskiBilin, pow_two]
            ring
    _ = d1MinkowskiBilin (x 0) (x 0) +
        d1MinkowskiBilin (x 1) (x 1) -
        2 * d1MinkowskiBilin (x 0) (x 1) :=
          d1MinkowskiBilin_sub_sub (u := x 0) (v := x 1)

/-- `n=2` forward-tube membership is exactly the pair of cone conditions for
the base point and the single consecutive difference. -/
lemma forwardTube_d1_n2_iff
    (z : Fin 2 → Fin (1 + 1) → ℂ) :
    z ∈ ForwardTube 1 2 ↔
      InOpenForwardCone 1 (fun μ => (z 0 μ).im) ∧
      InOpenForwardCone 1 (fun μ => (z 1 μ - z 0 μ).im) := by
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · simpa [ForwardTube] using hz (0 : Fin 2)
    · have h1 := hz (1 : Fin 2)
      have hprev : (⟨(1 : Fin 2).val - 1, by omega⟩ : Fin 2) = (0 : Fin 2) := by
        ext
        simp
      have hk_ne : ¬ ((1 : Fin 2).val = 0) := by
        decide
      simpa [ForwardTube, hk_ne, hprev] using h1
  · rintro ⟨h0, h1⟩
    intro k
    fin_cases k
    · simpa [ForwardTube] using h0
    · have hprev : (⟨(1 : Fin 2).val - 1, by omega⟩ : Fin 2) = (0 : Fin 2) := by
        ext
        simp
      have hk_ne : ¬ ((1 : Fin 2).val = 0) := by
        decide
      simpa [ForwardTube, hk_ne, hprev] using h1

/-- For `n=2`, the adjacent-swap overlap domain is `ET ∩ swap(ET)` in the
expected `permAct` form. -/
lemma mem_adjSwapExtendedOverlapSet_d1_swap01_n2_iff
    (z : Fin 2 → Fin (1 + 1) → ℂ) :
    z ∈ adjSwapExtendedOverlapSet (d := 1) 2 (0 : Fin 2) (by decide) ↔
      z ∈ ExtendedTube 1 2 ∧
      permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z ∈ ExtendedTube 1 2 := by
  constructor
  · intro hz
    exact ⟨hz.1, by simpa [adjSwapExtendedOverlapSet, permAct] using hz.2⟩
  · rintro ⟨hzET, hswapET⟩
    exact ⟨hzET, by simpa [adjSwapExtendedOverlapSet, permAct] using hswapET⟩

/-- For `n=2`, forward-overlap under `swap(0,1)` is exactly `FT ∩ swap(ET)`. -/
lemma mem_permForwardOverlapSet_d1_swap01_n2_iff
    (z : Fin 2 → Fin (1 + 1) → ℂ) :
    z ∈ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ↔
      z ∈ ForwardTube 1 2 ∧
      permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z ∈ ExtendedTube 1 2 := by
  rfl

/-- `d=1,n=2`: no single complex Lorentz element can place both `w` and
`swap(0,1)·w` in the forward tube. -/
lemma no_common_forwardizer_d1_swap01_n2
    (w : Fin 2 → Fin (1 + 1) → ℂ) :
    ¬ ∃ Λ : ComplexLorentzGroup 1,
        complexLorentzAction Λ w ∈ ForwardTube 1 2 ∧
        complexLorentzAction Λ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 := by
  intro h
  rcases h with ⟨Λ, hΛwFT, hΛswapFT⟩
  let z : Fin 2 → Fin (1 + 1) → ℂ := complexLorentzAction Λ w
  have hzFT : z ∈ ForwardTube 1 2 := hΛwFT
  have hswapzFT : (fun k => z (Equiv.swap (0 : Fin 2) 1 k)) ∈ ForwardTube 1 2 := by
    simpa [z, permAct, lorentz_perm_commute] using hΛswapFT
  exact (adjSwap_not_mem_forwardTube_d1 (n := 2) (i := (0 : Fin 2))
    (hi := by decide) hzFT) hswapzFT

/-- Prepared `d=1,n=2` adjacent-swap neighborhoods cannot have unswapped
forward membership for the same fixed witness `Γ`. -/
lemma prepared_unswapped_not_forward_d1_swap01_n2
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin 2 → Fin (1 + 1) → ℂ))
    (hU_good : ∀ z ∈ U,
      z ∈ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2) :
    ∀ z ∈ U, ¬ complexLorentzAction Γ z ∈ ForwardTube 1 2 := by
  intro z hzU hΓzFT
  have hΓswapFT :
      complexLorentzAction Γ (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 :=
    (hU_good z hzU).2
  exact (no_common_forwardizer_d1_swap01_n2 z) ⟨Γ, hΓzFT, hΓswapFT⟩

end BHW
