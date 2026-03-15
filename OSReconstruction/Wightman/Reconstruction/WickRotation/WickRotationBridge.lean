import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Wick Rotation Bridge

Small one-variable lemmas bridging the semigroup half-plane `{z : ℂ | 0 < z.re}`
and the Wick-rotated tube variable `{u : ℂ | 0 < u.im}` via `z = -I * u`.
-/

noncomputable section

open Complex

namespace OSReconstruction

/-- The Wick rotation `u ↦ -Iu` sends `{u : ℂ | 0 < u.im}` to
`{z : ℂ | 0 < z.re}` because `Re(-Iu) = Im(u)`. -/
theorem neg_I_mul_re_eq_im (u : ℂ) : (-I * u).re = u.im := by
  simp [neg_re, mul_re, I_re, I_im]

/-- The inverse Wick rotation `z ↦ Iz` sends `{z : ℂ | 0 < z.re}` to
`{u : ℂ | 0 < u.im}` because `Im(Iz) = Re(z)`. -/
theorem I_mul_im_eq_re (z : ℂ) : (I * z).im = z.re := by
  simp [mul_im, I_re, I_im]

/-- The Wick rotation cancels on complex scalars: `-I * (I * t) = t`. -/
theorem neg_I_mul_I_mul (t : ℂ) : -I * (I * t) = t := by
  rw [← mul_assoc]
  simp

/-- Real version of `neg_I_mul_I_mul`. -/
theorem neg_I_mul_I_mul_ofReal (r : ℝ) : -I * (I * (r : ℂ)) = (r : ℂ) := by
  exact neg_I_mul_I_mul (r : ℂ)

/-- If a scalar holomorphic function is evaluated on one coordinate of `ℂ^N`,
the resulting function is holomorphic on any domain where that coordinate stays
inside the original domain. -/
theorem differentiableOn_of_coord_dep {N : ℕ}
    (j : Fin N)
    (H : ℂ → ℂ)
    (S : Set ℂ)
    (hH : DifferentiableOn ℂ H S)
    (U : Set (Fin N → ℂ))
    (hU : ∀ u ∈ U, u j ∈ S) :
    DifferentiableOn ℂ (fun u => H (u j)) U := by
  intro u hu
  have hd : DifferentiableWithinAt ℂ H S (u j) := hH (u j) (hU u hu)
  have hp : DifferentiableAt ℂ (fun u : Fin N → ℂ => u j) u :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ => ℂ) j).differentiableAt
  exact DifferentiableWithinAt.comp u hd hp.differentiableWithinAt (fun x hx => hU x hx)

/-- Composing a holomorphic scalar function with a complex-linear functional
preserves holomorphicity on the pullback domain. -/
theorem differentiableOn_comp_clm {N : ℕ}
    (H : ℂ → ℂ)
    (L : (Fin N → ℂ) →L[ℂ] ℂ)
    (S : Set ℂ)
    (hH : DifferentiableOn ℂ H S)
    (U : Set (Fin N → ℂ))
    (hU : ∀ u ∈ U, L u ∈ S) :
    DifferentiableOn ℂ (fun u => H (L u)) U := by
  exact hH.comp (ContinuousLinearMap.differentiable L).differentiableOn (fun x hx => hU x hx)

/-- The continuous linear functional extracting the `j`-th coordinate and
applying Wick rotation. -/
def negIMulCoordCLM {N : ℕ} (j : Fin N) : (Fin N → ℂ) →L[ℂ] ℂ :=
  (-I) • ContinuousLinearMap.proj j

theorem negIMulCoordCLM_apply {N : ℕ} (j : Fin N) (u : Fin N → ℂ) :
    negIMulCoordCLM j u = -I * u j := by
  simp [negIMulCoordCLM, ContinuousLinearMap.smul_apply]

/-- If `H` is holomorphic on the right half-plane, then composing with the Wick
rotation `u ↦ -Iu` gives a holomorphic function on the upper half-plane. -/
theorem differentiableOn_comp_neg_I_mul {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.re}) :
    DifferentiableOn ℂ (fun u => H (-I * u)) {u : ℂ | 0 < u.im} := by
  intro u hu
  simp only [Set.mem_setOf_eq] at hu
  have hmap : -I * u ∈ {z : ℂ | 0 < z.re} := by
    rw [Set.mem_setOf_eq, neg_I_mul_re_eq_im]
    exact hu
  have hH_diff : DifferentiableAt ℂ H (-I * u) :=
    hH.differentiableAt (IsOpen.mem_nhds (isOpen_lt continuous_const continuous_re) hmap)
  have hmul_diff : DifferentiableAt ℂ (fun v : ℂ => -I * v) u := by
    have hclm : (fun v : ℂ => -I * v) = ⇑((-I) • ContinuousLinearMap.id ℂ ℂ) := by
      ext v
      simp
    rw [hclm]
    exact ((-I) • ContinuousLinearMap.id ℂ ℂ).differentiableAt
  exact (hH_diff.comp u hmul_diff).differentiableWithinAt

/-- Coordinate-wise version of `differentiableOn_comp_neg_I_mul`. If `H` is
holomorphic on the right half-plane, then `u ↦ H (-I * u_j)` is holomorphic on
the domain where the `j`-th coordinate lies in the upper half-plane. -/
theorem differentiableOn_H_neg_I_coord {N : ℕ}
    (j : Fin N)
    (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.re}) :
    DifferentiableOn ℂ (fun u : Fin N → ℂ => H (-I * u j))
      {u : Fin N → ℂ | 0 < (u j).im} := by
  apply differentiableOn_comp_clm H (negIMulCoordCLM j) {z | 0 < z.re} hH
  intro u hu
  simp only [Set.mem_setOf_eq, negIMulCoordCLM_apply]
  rw [neg_I_mul_re_eq_im]
  exact hu

/-- Product tube domain: all coordinates indexed by `S` lie in the upper
half-plane. -/
def productUpperHalfTube {N : ℕ} (S : Finset (Fin N)) : Set (Fin N → ℂ) :=
  {u | ∀ j ∈ S, 0 < (u j).im}

theorem productUpperHalfTube_subset_single {N : ℕ}
    (j : Fin N) (S : Finset (Fin N)) (hj : j ∈ S) :
    productUpperHalfTube S ⊆ {u : Fin N → ℂ | 0 < (u j).im} := by
  intro u hu
  exact hu j hj

/-- If the `j`-th upper-half-plane condition is present in a product tube, then
`u ↦ H(-I * u_j)` is holomorphic on that whole tube. -/
theorem differentiableOn_H_neg_I_coord_on_productTube {N : ℕ}
    (j : Fin N)
    (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.re})
    (S : Finset (Fin N)) (hj : j ∈ S) :
    DifferentiableOn ℂ (fun u : Fin N → ℂ => H (-I * u j))
      (productUpperHalfTube S) := by
  exact (differentiableOn_H_neg_I_coord j H hH).mono
    (productUpperHalfTube_subset_single j S hj)

/-- More generally, composing any holomorphic function with the Wick rotation
`u ↦ -Iu` preserves holomorphicity on the pullback of its domain. -/
theorem differentiableOn_wick_rotate {H : ℂ → ℂ} {S : Set ℂ}
    (hH : DifferentiableOn ℂ H S) (hS : IsOpen S) :
    DifferentiableOn ℂ (fun u => H (-I * u)) {u | -I * u ∈ S} := by
  intro u hu
  simp only [Set.mem_setOf_eq] at hu
  have hH_diff : DifferentiableAt ℂ H (-I * u) :=
    hH.differentiableAt (IsOpen.mem_nhds hS hu)
  have hmul_diff : DifferentiableAt ℂ (fun v : ℂ => -I * v) u := by
    have hclm : (fun v : ℂ => -I * v) = ⇑((-I) • ContinuousLinearMap.id ℂ ℂ) := by
      ext v
      simp
    rw [hclm]
    exact ((-I) • ContinuousLinearMap.id ℂ ℂ).differentiableAt
  exact (hH_diff.comp u hmul_diff).differentiableWithinAt

end OSReconstruction
