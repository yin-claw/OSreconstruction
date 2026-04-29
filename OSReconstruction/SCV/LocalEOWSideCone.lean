/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.LocalEOWChartLinear

/-!
# Local EOW Side-Cone Boundary Filters

This file contains the small cone/filter support needed before the local
distributional EOW slice-CLM assembly.  The point is to keep the lower-side
sign change explicit: a lower boundary value written as `x - iη` is a raw
slice limit over the negative image of the positive side cone.
-/

noncomputable section

open Complex Filter

namespace SCV

variable {m : ℕ}

/-- The compact simplex of chart directions does not contain the zero vector
when the chosen chart directions are linearly independent. -/
theorem zero_not_mem_localEOWSimplexDirections
    (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys) :
    (0 : Fin m → ℝ) ∉ localEOWSimplexDirections ys := by
  rintro ⟨a, ha, hzero⟩
  have hcoeff : ∀ j, a j = 0 := by
    intro j
    exact Fintype.linearIndependent_iff.mp hli a (by simpa using hzero) j
  have hsum_zero : ∑ j, a j = 0 := by
    simp [hcoeff]
  have hsum_one : ∑ j, a j = 1 := ha.2
  linarith

/-- Negation sends the edge filter on the negative image of a cone to the edge
filter on the original cone. -/
theorem tendsto_neg_nhdsWithin_zero_neg_image
    (C : Set (Fin m → ℝ)) :
    Filter.Tendsto (fun y : Fin m → ℝ => -y)
      (nhdsWithin 0 (Neg.neg '' C)) (nhdsWithin 0 C) := by
  have hcont0 : ContinuousAt (fun y : Fin m → ℝ => -y) (0 : Fin m → ℝ) :=
    continuous_neg.continuousAt
  have hmaps : Set.MapsTo (fun y : Fin m → ℝ => -y) (Neg.neg '' C) C := by
    rintro y ⟨x, hx, rfl⟩
    simpa using hx
  simpa using hcont0.continuousWithinAt.tendsto_nhdsWithin hmaps

end SCV
