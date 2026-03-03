import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlowBlockers.Core

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

/-- Logical form of the active blocker theorem statement (without using any
proof term from the deferred theorem). -/
def d1N2ActiveBlockerStatement : Prop :=
  ∀ (f : ℂ → ℂ → ℂ → ℂ → ℂ), d1N2InvariantKernelSource f →
    ∀ q0 q1 p s, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      d1N2InvariantLightConeWitness q0 q1 p s →
      d1N2InvariantLightConeWitness q1 q0 p (-s) →
      f q0 q1 p s - f q1 q0 p (-s) = 0

/-- Exact falsification target for the active blocker. -/
def d1N2ActiveBlockerCounterexample : Prop :=
  ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ,
    d1N2InvariantKernelSource f ∧
    ∃ q0 q1 p s : ℂ,
      s ^ 2 = 4 * (p ^ 2 - q0 * q1) ∧
      d1N2InvariantLightConeWitness q0 q1 p s ∧
      d1N2InvariantLightConeWitness q1 q0 p (-s) ∧
      f q0 q1 p s - f q1 q0 p (-s) ≠ 0

/-- Any valid counterexample immediately refutes the active blocker statement. -/
lemma d1N2ActiveCounterexample_implies_not_statement :
    d1N2ActiveBlockerCounterexample → ¬ d1N2ActiveBlockerStatement := by
  intro hcex hstmt
  rcases hcex with ⟨f, hsource, q0, q1, p, s, hquad, hLC, hswapLC, hneq⟩
  exact hneq (hstmt f hsource q0 q1 p s hquad hLC hswapLC)

/-- Any tuple with `q0 = 0` is not `FT`-realizable; useful for pruning false
counterexample candidates that live off the realizable image. -/
lemma not_realizable_of_q0_zero (q1 p s : ℂ) :
    ¬ d1N2InvariantRealizable 0 q1 p s := by
  intro hreal
  rcases hreal with ⟨z, hz, hquad⟩
  have hQ0 : d1Q0 z = (0 : ℂ) := by
    simpa [d1InvariantQuad] using congrArg Prod.fst hquad
  exact (d1Q0_ne_zero_of_mem_forwardTube_d1_n2 z hz) hQ0

example : ¬ d1N2InvariantRealizable (0 : ℂ) 0 1 (-2) :=
  not_realizable_of_q0_zero 0 1 (-2)

end BHW
