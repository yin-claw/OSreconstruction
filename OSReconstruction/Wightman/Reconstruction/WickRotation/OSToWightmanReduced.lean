/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesBase

/-!
# Reduced-coordinate support for the selected OS witness

This file contains small reduced-coordinate facts for the selected analytic
witness `bvt_F OS lgc`.  The point is purely algebraic: because the selected
witness is invariant under common complex translations, it factors through
successive differences.
-/

open scoped Classical NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The canonical reduced imaginary direction: every reduced difference slot
uses the fixed future-timelike safe basepoint vector. -/
def canonicalReducedDirection (m : ℕ) : Fin m → Fin (d + 1) → ℝ :=
  fun _ μ => BHW.safeBasepointVec d μ

/-- Complex-valued version of `canonicalReducedDirection`. -/
def canonicalReducedDirectionC (m : ℕ) : BHW.ReducedNPointConfig d m :=
  fun k μ => (canonicalReducedDirection (d := d) m k μ : ℂ)

/-- Canonical reduced direction after applying an absolute permutation through
the induced reduced-difference action. -/
noncomputable def permutedCanonicalReducedDirectionC
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    BHW.ReducedNPointConfig d m :=
  BHW.permOnReducedDiff (d := d) (n := m + 1) σ
    (canonicalReducedDirectionC (d := d) m)

/-- The selected OS analytic witness descended to reduced difference
coordinates through the public safe section. -/
def bvt_F_reduced
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) : BHW.ReducedNPointConfig d m → ℂ :=
  fun η => bvt_F OS lgc (m + 1) (BHW.safeSection d m η)

/-- The selected OS analytic witness factors through reduced difference
coordinates.  This is the theorem-2 reduced-coordinate entry point: no locality
or BHW PET uniqueness is used, only common complex translation invariance of the
chosen OS witness. -/
theorem bvt_F_eq_bvt_F_reduced_reducedDiffMap
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) :
    bvt_F OS lgc (m + 1) z =
      bvt_F_reduced (d := d) OS lgc m
        (BHW.reducedDiffMap (m + 1) d z) := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  let s : Fin (m + 1) → Fin (d + 1) → ℂ :=
    BHW.safeSection d m (BHW.reducedDiffMap (m + 1) d z)
  have hred :
      BHW.reducedDiffMap (m + 1) d z =
        BHW.reducedDiffMap (m + 1) d s := by
    simpa [s] using
      (BHW.reducedDiffMap_safeSection (d := d) (m := m)
        (BHW.reducedDiffMap (m + 1) d z)).symm
  obtain ⟨c, hc⟩ :=
    BHW.exists_uniformShift_eq_of_reducedDiffMap_eq
      (d := d) z s hred
  have hshift :
      bvt_F OS lgc (m + 1) s = bvt_F OS lgc (m + 1) z := by
    rw [hc]
    exact bvt_F_translationInvariant OS lgc (m + 1) z c
  simpa [bvt_F_reduced, s] using hshift.symm

/-- The reduced selected witness is invariant under the reduced action induced
by an absolute coordinate permutation. -/
theorem bvt_F_reduced_permOnReducedDiff
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (σ : Equiv.Perm (Fin (m + 1)))
    (ζ : BHW.ReducedNPointConfig d m) :
    bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ) =
      bvt_F_reduced (d := d) OS lgc m ζ := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  let z : Fin (m + 1) → Fin (d + 1) → ℂ := BHW.safeSection d m ζ
  let zσ : Fin (m + 1) → Fin (d + 1) → ℂ := fun k => z (σ k)
  have hz_red :
      BHW.reducedDiffMap (m + 1) d z = ζ := by
    simpa [z] using BHW.reducedDiffMap_safeSection (d := d) (m := m) ζ
  have hperm_red :
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ =
        BHW.reducedDiffMap (m + 1) d zσ := by
    calc
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ
          = BHW.permOnReducedDiff (d := d) (n := m + 1) σ
              (BHW.reducedDiffMap (m + 1) d z) := by
                rw [hz_red]
      _ = BHW.reducedDiffMap (m + 1) d zσ := by
            simpa [zσ] using
              BHW.permOnReducedDiff_reducedDiffMap
                (d := d) (n := m + 1) σ z
  have hfac_perm :=
    bvt_F_eq_bvt_F_reduced_reducedDiffMap
      (d := d) OS lgc m zσ
  have hfac :=
    bvt_F_eq_bvt_F_reduced_reducedDiffMap
      (d := d) OS lgc m z
  calc
    bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ)
        = bvt_F OS lgc (m + 1) zσ := by
            rw [hperm_red]
            exact hfac_perm.symm
    _ = bvt_F OS lgc (m + 1) z := by
            exact bvt_F_perm OS lgc (m + 1) σ z
    _ = bvt_F_reduced (d := d) OS lgc m ζ := by
            rw [← hz_red]
            exact hfac

/-- Applying the same transposition twice to the canonical reduced direction
returns the canonical direction. -/
theorem permOnReducedDiff_swap_permutedCanonicalDirection
    (m : ℕ) (i j : Fin (m + 1)) :
    BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
        (permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j)) =
      canonicalReducedDirectionC (d := d) m := by
  have _ : NeZero d := inferInstance
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  have hmul :=
    BHW.permOnReducedDiff_mul (d := d) (n := m + 1)
      (Equiv.swap i j) (Equiv.swap i j)
      (canonicalReducedDirectionC (d := d) m)
  calc
    BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
        (permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j))
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
        (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
          (canonicalReducedDirectionC (d := d) m)) := by
            rfl
    _ =
      BHW.permOnReducedDiff (d := d) (n := m + 1)
        ((Equiv.swap i j) * (Equiv.swap i j))
        (canonicalReducedDirectionC (d := d) m) := by
            exact hmul.symm
    _ = canonicalReducedDirectionC (d := d) m := by
            simpa using
              BHW.permOnReducedDiff_one (d := d) (n := m + 1)
                (canonicalReducedDirectionC (d := d) m)

/-- Convert a reduced value at the permuted canonical direction into the
corresponding value after applying the induced reduced permutation. -/
theorem bvt_F_reduced_permutedDirection_to_realPermutedCanonical
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (ξ : NPointDomain d m) (ε : ℝ) :
    bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I) =
      bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
          (fun k μ =>
            (ξ k μ : ℂ) +
              ε *
                permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
                Complex.I)) := by
  exact (bvt_F_reduced_permOnReducedDiff
    (d := d) OS lgc m (Equiv.swap i j)
    (fun k μ =>
      (ξ k μ : ℂ) +
        ε *
          permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
          Complex.I)).symm
