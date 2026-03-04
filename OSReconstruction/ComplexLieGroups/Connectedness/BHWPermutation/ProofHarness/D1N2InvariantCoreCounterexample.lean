import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlowBlockers.Tail

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

/-- Intrinsic witnessed domain used in the `d=1,n=2` invariant core theorem. -/
private def d1N2WitnessedDomain : Set (ℂ × ℂ × ℂ × ℂ) :=
  {t : ℂ × ℂ × ℂ × ℂ |
    t.2.2.2 ^ 2 = 4 * (t.2.2.1 ^ 2 - t.1 * t.2.1) ∧
    (∃ v0 : ℂ,
      0 < v0.im ∧
      0 < ((-t.1) / v0).im ∧
      0 < ((t.1 - t.2.2.1 - t.2.2.2 / 2) / v0).im ∧
      0 < (((t.2.2.1 - t.2.2.2 / 2 - t.1) * v0 / t.1).im)) ∧
    (∃ w0 : ℂ,
      0 < w0.im ∧
      0 < ((-t.2.1) / w0).im ∧
      0 < ((t.2.1 - t.2.2.1 + t.2.2.2 / 2) / w0).im ∧
      0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))}

/-- Real spacelike correction predicate used in the current invariant-core
assumption shape. -/
private def d1N2RealSpacelikeCond (q0 q1 p s : ℂ) : Prop :=
  q0.im = 0 ∧ q1.im = 0 ∧ p.im = 0 ∧ s.im = 0 ∧ q0.re + q1.re - 2 * p.re > 0

/-- Test kernel used to probe the current core theorem assumptions:
on real-spacelike tuples it is symmetrized; elsewhere it returns `q0`. -/
private def d1N2BadF (q0 q1 p s : ℂ) : ℂ :=
  if d1N2RealSpacelikeCond q0 q1 p s then q0 + q1 else q0

private def d1N2BadG (t : ℂ × ℂ × ℂ × ℂ) : ℂ :=
  d1N2BadF t.1 t.2.1 t.2.2.1 t.2.2.2 - d1N2BadF t.2.1 t.1 t.2.2.1 (-t.2.2.2)

private lemma d1N2RealSpacelikeCond_false_on_witnessed
    {t : ℂ × ℂ × ℂ × ℂ} (ht : t ∈ d1N2WitnessedDomain) :
    ¬ d1N2RealSpacelikeCond t.1 t.2.1 t.2.2.1 t.2.2.2 := by
  intro hcond
  rcases hcond with ⟨hq0, hq1, hp, hs, hsp⟩
  have hneg : t.1.re + t.2.1.re - 2 * t.2.2.1.re < 0 :=
    d1N2InvariantWitnessedDomain_real_implies_neg_spacelike ht hq0 hq1 hp hs
  linarith

private lemma d1N2RealSpacelikeCond_swap_false_on_witnessed
    {t : ℂ × ℂ × ℂ × ℂ} (ht : t ∈ d1N2WitnessedDomain) :
    ¬ d1N2RealSpacelikeCond t.2.1 t.1 t.2.2.1 (-t.2.2.2) := by
  intro hcond
  rcases hcond with ⟨hq1, hq0, hp, hnegS, hsp⟩
  have hs : t.2.2.2.im = 0 := by
    have hs' : (-t.2.2.2).im = 0 := hnegS
    simpa [Complex.neg_im] using hs'
  have hneg : t.1.re + t.2.1.re - 2 * t.2.2.1.re < 0 :=
    d1N2InvariantWitnessedDomain_real_implies_neg_spacelike ht hq0 hq1 hp hs
  linarith

private lemma d1N2BadG_eq_simple_on_witnessed
    {t : ℂ × ℂ × ℂ × ℂ} (ht : t ∈ d1N2WitnessedDomain) :
    d1N2BadG t = t.1 - t.2.1 := by
  have hfalse : ¬ d1N2RealSpacelikeCond t.1 t.2.1 t.2.2.1 t.2.2.2 :=
    d1N2RealSpacelikeCond_false_on_witnessed ht
  have hswapFalse : ¬ d1N2RealSpacelikeCond t.2.1 t.1 t.2.2.1 (-t.2.2.2) :=
    d1N2RealSpacelikeCond_swap_false_on_witnessed ht
  simp [d1N2BadG, d1N2BadF, hfalse, hswapFalse]

private lemma d1N2BadG_differentiableOn_witnessed :
    DifferentiableOn ℂ d1N2BadG d1N2WitnessedDomain := by
  have hsimple :
      DifferentiableOn ℂ (fun t : ℂ × ℂ × ℂ × ℂ => t.1 - t.2.1) d1N2WitnessedDomain := by
    intro t ht
    have h1 : DifferentiableAt ℂ (fun τ : ℂ × ℂ × ℂ × ℂ => τ.1) t := by
      fun_prop
    have h2 : DifferentiableAt ℂ (fun τ : ℂ × ℂ × ℂ × ℂ => τ.2.1) t := by
      fun_prop
    exact (h1.sub h2).differentiableWithinAt
  exact hsimple.congr (fun t ht => d1N2BadG_eq_simple_on_witnessed ht)

private lemma d1N2BadF_correction :
    ∀ q0 q1 p s : ℂ,
      s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      q0.im = 0 →
      q1.im = 0 →
      p.im = 0 →
      s.im = 0 →
      q0.re + q1.re - 2 * p.re > 0 →
      d1N2BadF q0 q1 p s = d1N2BadF q1 q0 p (-s) := by
  intro q0 q1 p s hquad hq0 hq1 hp hs hsp
  let hcond : d1N2RealSpacelikeCond q0 q1 p s := ⟨hq0, hq1, hp, hs, hsp⟩
  have hcond' : d1N2RealSpacelikeCond q1 q0 p (-s) := by
    refine ⟨hq1, hq0, hp, ?_, ?_⟩
    · simpa [Complex.neg_im] using hs
    · simpa [add_comm, add_left_comm, add_assoc] using hsp
  calc
    d1N2BadF q0 q1 p s = q0 + q1 := by simp [d1N2BadF, hcond]
    _ = q1 + q0 := by ring
    _ = d1N2BadF q1 q0 p (-s) := by simp [d1N2BadF, hcond']

/-- Counterexample harness:
if the current intrinsic witnessed domain is preconnected, then the present
core theorem shape
`blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred`
forces a contradiction.

This isolates that the current correction-hypothesis shape (`real spacelike > 0`)
is insufficient by itself for the witnessed-domain swap conclusion. -/
theorem d1N2InvariantCore_counterexample_if_connected
    (hConnected : IsPreconnected d1N2WitnessedDomain) : False := by
  have hcore := blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred
    d1N2BadF
    (by
      simpa [d1N2BadG, d1N2WitnessedDomain]
        using d1N2BadG_differentiableOn_witnessed)
    (by simpa [d1N2WitnessedDomain] using hConnected)
    d1N2BadF_correction
  rcases d1N2InvariantWitnessedDomain_nontrivial_example with
    ⟨q0, q1, p, s, hneq, hquad, hOrig, hSwap⟩
  have heq : d1N2BadF q0 q1 p s = d1N2BadF q1 q0 p (-s) :=
    hcore q0 q1 p s hquad hOrig hSwap
  have htD : (q0, q1, p, s) ∈ d1N2WitnessedDomain := by
    exact ⟨hquad, hOrig, hSwap⟩
  have hleft : d1N2BadF q0 q1 p s = q0 := by
    have hfalse : ¬ d1N2RealSpacelikeCond q0 q1 p s :=
      d1N2RealSpacelikeCond_false_on_witnessed htD
    simp [d1N2BadF, hfalse]
  have hright : d1N2BadF q1 q0 p (-s) = q1 := by
    have hfalse : ¬ d1N2RealSpacelikeCond q1 q0 p (-s) :=
      d1N2RealSpacelikeCond_swap_false_on_witnessed htD
    simp [d1N2BadF, hfalse]
  have hqq : q0 = q1 := by simpa [hleft, hright] using heq
  exact hneq hqq

end BHW
