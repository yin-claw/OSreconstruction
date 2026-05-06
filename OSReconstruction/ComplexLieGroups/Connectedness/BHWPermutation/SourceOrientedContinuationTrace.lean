import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuation

/-!
# Transfer-provenance continuation traces

Recursive constructors for transfer traces.  These are kept separate from the
base continuation carriers so the hard comparison frontier stays small.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

namespace BHWJostOrientedTransferContinuationTrace

variable [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}
variable {p0 p q center : Fin n → Fin (d + 1) → ℂ}

/-- Append one branch-free transfer step to a transfer trace. -/
def snocAtTerminalNode
    (Tr :
      BHWJostOrientedTransferContinuationTrace hd n τ Ω0 U B0 p0 p)
    (N : BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U center)
    (hpN : Tr.chain.node (Fin.last Tr.chain.m) ∈ N.N)
    (hpU : Tr.chain.node (Fin.last Tr.chain.m) ∈ U)
    (hqN : q ∈ N.N) (hqU : q ∈ U) :
    BHWJostOrientedTransferContinuationTrace hd n τ Ω0 U B0 p0 q :=
  let hpC :
      Tr.chain.node (Fin.last Tr.chain.m) ∈
        (Tr.chain.localChart (Fin.last Tr.chain.m)).carrier := by
    simpa [Tr.chain.chart_eq_local (Fin.last Tr.chain.m)]
      using Tr.chain.node_mem (Fin.last Tr.chain.m)
  let R :=
    N.transfer (Tr.chain.node (Fin.last Tr.chain.m)) q hpN hpU hqN hqU
      (Tr.chain.localChart (Fin.last Tr.chain.m)) hpC
  let Control :=
    BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl N
  let Cnext :=
    BHWJostOrientedSourcePatchContinuationChain.snoc
      (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
      (p0 := p0) Tr.chain R.1 R.2
  { chain := Cnext
    stepControl := by
      intro j
      refine Fin.lastCases ?_ ?_ j
      · exact Control
      · intro i
        exact Tr.stepControl i
    step_left_mem := by
      intro j
      refine Fin.lastCases ?_ ?_ j
      · simpa [Cnext, Control,
          BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl,
          BHWJostOrientedSourcePatchContinuationChain.snoc,
          Fin.snoc_castSucc] using hpN
      · intro i
        simpa [Cnext, Control,
          BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl,
          BHWJostOrientedSourcePatchContinuationChain.snoc,
          Fin.snoc_castSucc] using Tr.step_left_mem i
    step_right_mem := by
      intro j
      refine Fin.lastCases ?_ ?_ j
      · simpa [Cnext, Control,
          BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl,
          BHWJostOrientedSourcePatchContinuationChain.snoc,
          Fin.snoc_last] using hqN
      · intro i
        have hidx :
            (i.castSucc : Fin (Tr.chain.m + 1)).succ =
              (i.succ).castSucc := by
          ext
          rfl
        have hnode :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              Tr.chain.node q i.castSucc.succ) =
              Tr.chain.node i.succ := by
          rw [hidx]
          simpa using
            (Fin.snoc_castSucc
              (α := fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              (x := q) (p := Tr.chain.node) i.succ)
        simpa [Cnext, Control,
          BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl,
          BHWJostOrientedSourcePatchContinuationChain.snoc,
          Fin.snoc_castSucc, hnode] using Tr.step_right_mem i
    step_transfer_chart_eq := by
      intro j
      refine Fin.lastCases ?_ ?_ j
      · have hnode_left :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              Tr.chain.node q (Fin.last Tr.chain.m).castSucc) =
              Tr.chain.node (Fin.last Tr.chain.m) := by
          simp
        have hnode_right :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              Tr.chain.node q (Fin.last (Tr.chain.m + 1))) =
              q := by
          simp
        have hchart_left :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                BHWJostLocalOrientedContinuationChart hd n τ U)
              Tr.chain.localChart R.1 (Fin.last Tr.chain.m).castSucc) =
              Tr.chain.localChart (Fin.last Tr.chain.m) := by
          simp
        have hchart_right :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                BHWJostLocalOrientedContinuationChart hd n τ U)
              Tr.chain.localChart R.1 (Fin.last (Tr.chain.m + 1))) =
              R.1 := by
          simp
        dsimp [Cnext, BHWJostOrientedSourcePatchContinuationChain.snoc]
        convert
          (show
            (N.transfer (Tr.chain.node (Fin.last Tr.chain.m)) q hpN hpU
              hqN hqU (Tr.chain.localChart (Fin.last Tr.chain.m)) hpC).1 =
              R.1 by
            rfl)
          using 2
        · simp [Control,
          BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl,
          hnode_left, hnode_right, hchart_left]
      · intro i
        have hidx :
            (i.castSucc : Fin (Tr.chain.m + 1)).succ =
              (i.succ).castSucc := by
          ext
          rfl
        have hnode_right :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              Tr.chain.node q i.castSucc.succ) =
              Tr.chain.node i.succ := by
          rw [hidx]
          simpa using
            (Fin.snoc_castSucc
              (α := fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              (x := q) (p := Tr.chain.node) i.succ)
        have hnode_left :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                Fin n → Fin (d + 1) → ℂ)
              Tr.chain.node q i.castSucc.castSucc) =
              Tr.chain.node i.castSucc := by
          simp
        have hchart_right :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                BHWJostLocalOrientedContinuationChart hd n τ U)
              Tr.chain.localChart R.1 i.castSucc.succ) =
              Tr.chain.localChart i.succ := by
          rw [hidx]
          simpa using
            (Fin.snoc_castSucc
              (α := fun _ : Fin (Tr.chain.m + 1 + 1) =>
                BHWJostLocalOrientedContinuationChart hd n τ U)
              (x := R.1) (p := Tr.chain.localChart) i.succ)
        have hchart_left :
            (@Fin.snoc (Tr.chain.m + 1)
              (fun _ : Fin (Tr.chain.m + 1 + 1) =>
                BHWJostLocalOrientedContinuationChart hd n τ U)
              Tr.chain.localChart R.1 i.castSucc.castSucc) =
              Tr.chain.localChart i.castSucc := by
          simp
        dsimp [Cnext, BHWJostOrientedSourcePatchContinuationChain.snoc]
        convert Tr.step_transfer_chart_eq i using 2
        · simp [Control, Fin.lastCases_castSucc] }

end BHWJostOrientedTransferContinuationTrace

end BHW
